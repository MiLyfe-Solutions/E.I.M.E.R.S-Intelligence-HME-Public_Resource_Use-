import V185TrunkScan23Chunk0712

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4215265 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_4215265 : Nat := 118140960795 + 4215265 * 2 ^ 59
def prefixEnd_4215265 : Nat := 4983230072969 + 3 ^ 40 * 4215265 * 2
def baseEnd_4215265 : Nat := 2164457031074555490001855

theorem tailTrace_4215265 : CollatzResearch.WordTrace tailWord_4215265 prefixEnd_4215265 2164457031074555490001855 := by
  unfold tailWord_4215265
  simp only [CollatzResearch.WordTrace]
  refine ⟨153743345073822289792151249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102495563382548193194767499 153743345073822289792151249)
  ·
    refine ⟨115307508805366717344113437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153743345073822289792151249 115307508805366717344113437)
    ·
      refine ⟨43240315802012519004042539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115307508805366717344113437 43240315802012519004042539)
      ·
        refine ⟨64860473703018778506063809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43240315802012519004042539 64860473703018778506063809)
        ·
          refine ⟨48645355277264083879547857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64860473703018778506063809 48645355277264083879547857)
          ·
            refine ⟨36484016457948062909660893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48645355277264083879547857 36484016457948062909660893)
            ·
              refine ⟨13681506171730523591122835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36484016457948062909660893 13681506171730523591122835)
              ·
                refine ⟨20522259257595785386684253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13681506171730523591122835 20522259257595785386684253)
                ·
                  refine ⟨7695847221598419520006595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20522259257595785386684253 7695847221598419520006595)
                  ·
                    refine ⟨11543770832397629280009893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7695847221598419520006595 11543770832397629280009893)
                    ·
                      refine ⟨2164457031074555490001855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11543770832397629280009893 2164457031074555490001855)
                      ·
                        rfl

theorem cell23_4215265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_4215265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215265 prefixEnd_4215265 := by exact prefixLift 4215265
  have htrace : WordTrace (prefixWord ++ tailWord_4215265) baseStart_4215265 baseEnd_4215265 := by
    simpa [prefixWord, tailWord_4215265, baseEnd_4215265] using wordTrace_append hprefix tailTrace_4215265
  have hstable : (prefixWord ++ tailWord_4215265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215265).length < 2 ^ (prefixWord ++ tailWord_4215265).sum := by decide
  have hdescent : baseEnd_4215265 < baseStart_4215265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215268 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_4215268 : Nat := 118140960795 + 4215268 * 2 ^ 59
def prefixEnd_4215268 : Nat := 4983230072969 + 3 ^ 40 * 4215268 * 2
def baseEnd_4215268 : Nat := 2164458571516518978264341

theorem tailTrace_4215268 : CollatzResearch.WordTrace tailWord_4215268 prefixEnd_4215268 2164458571516518978264341 := by
  unfold tailWord_4215268
  simp only [CollatzResearch.WordTrace]
  refine ⟨76871727246405710652255229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102495636328540947536340305 76871727246405710652255229)
  ·
    refine ⟨28826897717402141494595711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76871727246405710652255229 28826897717402141494595711)
    ·
      refine ⟨43240346576103212241893567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28826897717402141494595711 43240346576103212241893567)
      ·
        refine ⟨64860519864154818362840351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43240346576103212241893567 64860519864154818362840351)
        ·
          refine ⟨97290779796232227544260527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64860519864154818362840351 97290779796232227544260527)
          ·
            refine ⟨145936169694348341316390791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97290779796232227544260527 145936169694348341316390791)
            ·
              refine ⟨218904254541522511974586187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145936169694348341316390791 218904254541522511974586187)
              ·
                refine ⟨328356381812283767961879281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218904254541522511974586187 328356381812283767961879281)
                ·
                  refine ⟨246267286359212825971409461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328356381812283767961879281 246267286359212825971409461)
                  ·
                    refine ⟨23087558096176202434819637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 246267286359212825971409461 23087558096176202434819637)
                    ·
                      refine ⟨2164458571516518978264341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23087558096176202434819637 2164458571516518978264341)
                      ·
                        rfl

theorem cell23_4215268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_4215268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215268 prefixEnd_4215268 := by exact prefixLift 4215268
  have htrace : WordTrace (prefixWord ++ tailWord_4215268) baseStart_4215268 baseEnd_4215268 := by
    simpa [prefixWord, tailWord_4215268, baseEnd_4215268] using wordTrace_append hprefix tailTrace_4215268
  have hstable : (prefixWord ++ tailWord_4215268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215268).length < 2 ^ (prefixWord ++ tailWord_4215268).sum := by decide
  have hdescent : baseEnd_4215268 < baseStart_4215268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215309 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_4215309 : Nat := 118140960795 + 4215309 * 2 ^ 59
def prefixEnd_4215309 : Nat := 4983230072969 + 3 ^ 40 * 4215309 * 2
def baseEnd_4215309 : Nat := 721493208074451105950551

theorem tailTrace_4215309 : CollatzResearch.WordTrace tailWord_4215309 prefixEnd_4215309 721493208074451105950551 := by
  unfold tailWord_4215309
  simp only [CollatzResearch.WordTrace]
  refine ⟨153744949885662885306752981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102496633257108590204501987 153744949885662885306752981)
  ·
    refine ⟨3603397262945223874377023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 153744949885662885306752981 3603397262945223874377023)
    ·
      refine ⟨5405095894417835811565535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3603397262945223874377023 5405095894417835811565535)
      ·
        refine ⟨8107643841626753717348303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5405095894417835811565535 8107643841626753717348303)
        ·
          refine ⟨12161465762440130576022455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8107643841626753717348303 12161465762440130576022455)
          ·
            refine ⟨18242198643660195864033683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12161465762440130576022455 18242198643660195864033683)
            ·
              refine ⟨27363297965490293796050525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18242198643660195864033683 27363297965490293796050525)
              ·
                refine ⟨10261236737058860173518947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27363297965490293796050525 10261236737058860173518947)
                ·
                  refine ⟨15391855105588290260278421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10261236737058860173518947 15391855105588290260278421)
                  ·
                    refine ⟨721493208074451105950551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15391855105588290260278421 721493208074451105950551)
                    ·
                      rfl

theorem cell23_4215309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_4215309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215309 prefixEnd_4215309 := by exact prefixLift 4215309
  have htrace : WordTrace (prefixWord ++ tailWord_4215309) baseStart_4215309 baseEnd_4215309 := by
    simpa [prefixWord, tailWord_4215309, baseEnd_4215309] using wordTrace_append hprefix tailTrace_4215309
  have hstable : (prefixWord ++ tailWord_4215309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215309).length < 2 ^ (prefixWord ++ tailWord_4215309).sum := by decide
  have hdescent : baseEnd_4215309 < baseStart_4215309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215316 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_4215316 : Nat := 118140960795 + 4215316 * 2 ^ 59
def prefixEnd_4215316 : Nat := 4983230072969 + 3 ^ 40 * 4215316 * 2
def baseEnd_4215316 : Nat := 2164483218587934790464121

theorem tailTrace_4215316 : CollatzResearch.WordTrace tailWord_4215316 prefixEnd_4215316 2164483218587934790464121 := by
  unfold tailWord_4215316
  simp only [CollatzResearch.WordTrace]
  refine ⟨76872602598318762751128901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102496803464425017001505201 76872602598318762751128901)
  ·
    refine ⟨14413612987184768015836669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76872602598318762751128901 14413612987184768015836669)
    ·
      refine ⟨5405104870194288005938751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14413612987184768015836669 5405104870194288005938751)
      ·
        refine ⟨8107657305291432008908127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5405104870194288005938751 8107657305291432008908127)
        ·
          refine ⟨12161485957937148013362191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8107657305291432008908127 12161485957937148013362191)
          ·
            refine ⟨18242228936905722020043287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12161485957937148013362191 18242228936905722020043287)
            ·
              refine ⟨27363343405358583030064931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18242228936905722020043287 27363343405358583030064931)
              ·
                refine ⟨41045015108037874545097397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27363343405358583030064931 41045015108037874545097397)
                ·
                  refine ⟨3847970166378550738602881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41045015108037874545097397 3847970166378550738602881)
                  ·
                    refine ⟨2885977624783913053952161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3847970166378550738602881 2885977624783913053952161)
                    ·
                      refine ⟨2164483218587934790464121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885977624783913053952161 2164483218587934790464121)
                      ·
                        rfl

theorem cell23_4215316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_4215316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215316 prefixEnd_4215316 := by exact prefixLift 4215316
  have htrace : WordTrace (prefixWord ++ tailWord_4215316) baseStart_4215316 baseEnd_4215316 := by
    simpa [prefixWord, tailWord_4215316, baseEnd_4215316] using wordTrace_append hprefix tailTrace_4215316
  have hstable : (prefixWord ++ tailWord_4215316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215316).length < 2 ^ (prefixWord ++ tailWord_4215316).sum := by decide
  have hdescent : baseEnd_4215316 < baseStart_4215316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215336 : List Nat := [2, 1, 5, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_4215336 : Nat := 118140960795 + 4215336 * 2 ^ 59
def prefixEnd_4215336 : Nat := 4983230072969 + 3 ^ 40 * 4215336 * 2
def baseEnd_4215336 : Nat := 2164493488201024712214029

theorem tailTrace_4215336 : CollatzResearch.WordTrace tailWord_4215336 prefixEnd_4215336 2164493488201024712214029 := by
  unfold tailWord_4215336
  simp only [CollatzResearch.WordTrace]
  refine ⟨76872967328282534458992931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102497289771043379278657241 76872967328282534458992931)
  ·
    refine ⟨115309450992423801688489397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76872967328282534458992931 115309450992423801688489397)
    ·
      refine ⟨10810261030539731408295881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115309450992423801688489397 10810261030539731408295881)
      ·
        refine ⟨8107695772904798556221911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10810261030539731408295881 8107695772904798556221911)
        ·
          refine ⟨12161543659357197834332867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8107695772904798556221911 12161543659357197834332867)
          ·
            refine ⟨18242315489035796751499301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12161543659357197834332867 18242315489035796751499301)
            ·
              refine ⟨3420434154194211890906119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18242315489035796751499301 3420434154194211890906119)
              ·
                refine ⟨5130651231291317836359179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3420434154194211890906119 5130651231291317836359179)
                ·
                  refine ⟨7695976846936976754538769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5130651231291317836359179 7695976846936976754538769)
                  ·
                    refine ⟨5771982635202732565904077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7695976846936976754538769 5771982635202732565904077)
                    ·
                      refine ⟨2164493488201024712214029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5771982635202732565904077 2164493488201024712214029)
                      ·
                        rfl

theorem cell23_4215336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_4215336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215336 prefixEnd_4215336 := by exact prefixLift 4215336
  have htrace : WordTrace (prefixWord ++ tailWord_4215336) baseStart_4215336 baseEnd_4215336 := by
    simpa [prefixWord, tailWord_4215336, baseEnd_4215336] using wordTrace_append hprefix tailTrace_4215336
  have hstable : (prefixWord ++ tailWord_4215336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215336).length < 2 ^ (prefixWord ++ tailWord_4215336).sum := by decide
  have hdescent : baseEnd_4215336 < baseStart_4215336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215365 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 2, 6]
def baseStart_4215365 : Nat := 118140960795 + 4215365 * 2 ^ 59
def prefixEnd_4215365 : Nat := 4983230072969 + 3 ^ 40 * 4215365 * 2
def baseEnd_4215365 : Nat := 721502793046668366250465

theorem tailTrace_4215365 : CollatzResearch.WordTrace tailWord_4215365 prefixEnd_4215365 721502793046668366250465 := by
  unfold tailWord_4215365
  simp only [CollatzResearch.WordTrace]
  refine ⟨153746992373460006870791549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102497994915640004580527699 153746992373460006870791549)
  ·
    refine ⟨57655122140047502576546831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153746992373460006870791549 57655122140047502576546831)
    ·
      refine ⟨86482683210071253864820247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57655122140047502576546831 86482683210071253864820247)
      ·
        refine ⟨129724024815106880797230371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86482683210071253864820247 129724024815106880797230371)
        ·
          refine ⟨194586037222660321195845557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129724024815106880797230371 194586037222660321195845557)
          ·
            refine ⟨18242440989624405112110521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 194586037222660321195845557 18242440989624405112110521)
            ·
              refine ⟨13681830742218303834082891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18242440989624405112110521 13681830742218303834082891)
              ·
                refine ⟨20522746113327455751124337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13681830742218303834082891 20522746113327455751124337)
                ·
                  refine ⟨15392059584995591813343253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20522746113327455751124337 15392059584995591813343253)
                  ·
                    refine ⟨721502793046668366250465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15392059584995591813343253 721502793046668366250465)
                    ·
                      rfl

theorem cell23_4215365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_4215365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215365 prefixEnd_4215365 := by exact prefixLift 4215365
  have htrace : WordTrace (prefixWord ++ tailWord_4215365) baseStart_4215365 baseEnd_4215365 := by
    simpa [prefixWord, tailWord_4215365, baseEnd_4215365] using wordTrace_append hprefix tailTrace_4215365
  have hstable : (prefixWord ++ tailWord_4215365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215365).length < 2 ^ (prefixWord ++ tailWord_4215365).sum := by decide
  have hdescent : baseEnd_4215365 < baseStart_4215365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215366 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_4215366 : Nat := 118140960795 + 4215366 * 2 ^ 59
def prefixEnd_4215366 : Nat := 4983230072969 + 3 ^ 40 * 4215366 * 2
def baseEnd_4215366 : Nat := 2164508892620659594838891

theorem tailTrace_4215366 : CollatzResearch.WordTrace tailWord_4215366 prefixEnd_4215366 2164508892620659594838891 := by
  unfold tailWord_4215366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4804594651451762001299311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 102498019230970922694385301 4804594651451762001299311)
  ·
    refine ⟨7206891977177643001948967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4804594651451762001299311 7206891977177643001948967)
    ·
      refine ⟨10810337965766464502923451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7206891977177643001948967 10810337965766464502923451)
      ·
        refine ⟨16215506948649696754385177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10810337965766464502923451 16215506948649696754385177)
        ·
          refine ⟨12161630211487272565788883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16215506948649696754385177 12161630211487272565788883)
          ·
            refine ⟨18242445317230908848683325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12161630211487272565788883 18242445317230908848683325)
            ·
              refine ⟨6840916993961590818256247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18242445317230908848683325 6840916993961590818256247)
              ·
                refine ⟨10261375490942386227384371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6840916993961590818256247 10261375490942386227384371)
                ·
                  refine ⟨15392063236413579341076557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10261375490942386227384371 15392063236413579341076557)
                  ·
                    refine ⟨5772023713655092252903709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15392063236413579341076557 5772023713655092252903709)
                    ·
                      refine ⟨2164508892620659594838891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5772023713655092252903709 2164508892620659594838891)
                      ·
                        rfl

theorem cell23_4215366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_4215366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215366 prefixEnd_4215366 := by exact prefixLift 4215366
  have htrace : WordTrace (prefixWord ++ tailWord_4215366) baseStart_4215366 baseEnd_4215366 := by
    simpa [prefixWord, tailWord_4215366, baseEnd_4215366] using wordTrace_append hprefix tailTrace_4215366
  have hstable : (prefixWord ++ tailWord_4215366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215366).length < 2 ^ (prefixWord ++ tailWord_4215366).sum := by decide
  have hdescent : baseEnd_4215366 < baseStart_4215366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215375 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 3]
def baseStart_4215375 : Nat := 118140960795 + 4215375 * 2 ^ 59
def prefixEnd_4215375 : Nat := 4983230072969 + 3 ^ 40 * 4215375 * 2
def baseEnd_4215375 : Nat := 2164513513946550059626349

theorem tailTrace_4215375 : CollatzResearch.WordTrace tailWord_4215375 prefixEnd_4215375 2164513513946550059626349 := by
  unfold tailWord_4215375
  simp only [CollatzResearch.WordTrace]
  refine ⟨153747357103423778578655579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102498238068949185719103719 153747357103423778578655579)
  ·
    refine ⟨230621035655135667867983369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153747357103423778578655579 230621035655135667867983369)
    ·
      refine ⟨172965776741351750900987527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230621035655135667867983369 172965776741351750900987527)
      ·
        refine ⟨259448665112027626351481291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172965776741351750900987527 259448665112027626351481291)
        ·
          refine ⟨389172997668041439527221937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259448665112027626351481291 389172997668041439527221937)
          ·
            refine ⟨291879748251031079645416453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389172997668041439527221937 291879748251031079645416453)
            ·
              refine ⟨54727452797068327433515585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 291879748251031079645416453 54727452797068327433515585)
              ·
                refine ⟨41045589597801245575136689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54727452797068327433515585 41045589597801245575136689)
                ·
                  refine ⟨30784192198350934181352517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41045589597801245575136689 30784192198350934181352517)
                  ·
                    refine ⟨5772036037190800159003597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30784192198350934181352517 5772036037190800159003597)
                    ·
                      refine ⟨2164513513946550059626349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5772036037190800159003597 2164513513946550059626349)
                      ·
                        rfl

theorem cell23_4215375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 3].length) (baseStart_4215375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215375 prefixEnd_4215375 := by exact prefixLift 4215375
  have htrace : WordTrace (prefixWord ++ tailWord_4215375) baseStart_4215375 baseEnd_4215375 := by
    simpa [prefixWord, tailWord_4215375, baseEnd_4215375] using wordTrace_append hprefix tailTrace_4215375
  have hstable : (prefixWord ++ tailWord_4215375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215375).length < 2 ^ (prefixWord ++ tailWord_4215375).sum := by decide
  have hdescent : baseEnd_4215375 < baseStart_4215375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215406 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_4215406 : Nat := 118140960795 + 4215406 * 2 ^ 59
def prefixEnd_4215406 : Nat := 4983230072969 + 3 ^ 40 * 4215406 * 2
def baseEnd_4215406 : Nat := 2164529431846839438338707

theorem tailTrace_4215406 : CollatzResearch.WordTrace tailWord_4215406 prefixEnd_4215406 2164529431846839438338707 := by
  unfold tailWord_4215406
  simp only [CollatzResearch.WordTrace]
  refine ⟨19218560970788933859129259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102498991844207647248689381 19218560970788933859129259)
  ·
    refine ⟨28827841456183400788693889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19218560970788933859129259 28827841456183400788693889)
    ·
      refine ⟨21620881092137550591520417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28827841456183400788693889 21620881092137550591520417)
      ·
        refine ⟨16215660819103162943640313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21620881092137550591520417 16215660819103162943640313)
        ·
          refine ⟨12161745614327372207730235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16215660819103162943640313 12161745614327372207730235)
          ·
            refine ⟨18242618421491058311595353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12161745614327372207730235 18242618421491058311595353)
            ·
              refine ⟨13681963816118293733696515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18242618421491058311595353 13681963816118293733696515)
              ·
                refine ⟨20522945724177440600544773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13681963816118293733696515 20522945724177440600544773)
                ·
                  refine ⟨3848052323283270112602145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20522945724177440600544773 3848052323283270112602145)
                  ·
                    refine ⟨2886039242462452584451609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3848052323283270112602145 2886039242462452584451609)
                    ·
                      refine ⟨2164529431846839438338707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2886039242462452584451609 2164529431846839438338707)
                      ·
                        rfl

theorem cell23_4215406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_4215406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215406 prefixEnd_4215406 := by exact prefixLift 4215406
  have htrace : WordTrace (prefixWord ++ tailWord_4215406) baseStart_4215406 baseEnd_4215406 := by
    simpa [prefixWord, tailWord_4215406, baseEnd_4215406] using wordTrace_append hprefix tailTrace_4215406
  have hstable : (prefixWord ++ tailWord_4215406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215406).length < 2 ^ (prefixWord ++ tailWord_4215406).sum := by decide
  have hdescent : baseEnd_4215406 < baseStart_4215406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215452 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_4215452 : Nat := 118140960795 + 4215452 * 2 ^ 59
def prefixEnd_4215452 : Nat := 4983230072969 + 3 ^ 40 * 4215452 * 2
def baseEnd_4215452 : Nat := 2164553051956946258363495

theorem tailTrace_4215452 : CollatzResearch.WordTrace tailWord_4215452 prefixEnd_4215452 2164553051956946258363495 := by
  unfold tailWord_4215452
  simp only [CollatzResearch.WordTrace]
  refine ⟨76875082762072410364604305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102500110349429880486139073 76875082762072410364604305)
  ·
    refine ⟨57656312071554307773453229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76875082762072410364604305 57656312071554307773453229)
    ·
      refine ⟨21621117026832865415044961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57656312071554307773453229 21621117026832865415044961)
      ·
        refine ⟨16215837770124649061283721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21621117026832865415044961 16215837770124649061283721)
        ·
          refine ⟨12161878327593486795962791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16215837770124649061283721 12161878327593486795962791)
          ·
            refine ⟨18242817491390230193944187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12161878327593486795962791 18242817491390230193944187)
            ·
              refine ⟨27364226237085345290916281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18242817491390230193944187 27364226237085345290916281)
              ·
                refine ⟨20523169677814008968187211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27364226237085345290916281 20523169677814008968187211)
                ·
                  refine ⟨30784754516721013452280817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20523169677814008968187211 30784754516721013452280817)
                  ·
                    refine ⟨23088565887540760089210613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30784754516721013452280817 23088565887540760089210613)
                    ·
                      refine ⟨2164553051956946258363495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23088565887540760089210613 2164553051956946258363495)
                      ·
                        rfl

theorem cell23_4215452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_4215452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215452 prefixEnd_4215452 := by exact prefixLift 4215452
  have htrace : WordTrace (prefixWord ++ tailWord_4215452) baseStart_4215452 baseEnd_4215452 := by
    simpa [prefixWord, tailWord_4215452, baseEnd_4215452] using wordTrace_append hprefix tailTrace_4215452
  have hstable : (prefixWord ++ tailWord_4215452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215452).length < 2 ^ (prefixWord ++ tailWord_4215452).sum := by decide
  have hdescent : baseEnd_4215452 < baseStart_4215452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215472 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 3, 4]
def baseStart_4215472 : Nat := 118140960795 + 4215472 * 2 ^ 59
def prefixEnd_4215472 : Nat := 4983230072969 + 3 ^ 40 * 4215472 * 2
def baseEnd_4215472 : Nat := 721521107190012060037801

theorem tailTrace_4215472 : CollatzResearch.WordTrace tailWord_4215472 prefixEnd_4215472 721521107190012060037801 := by
  unfold tailWord_4215472
  simp only [CollatzResearch.WordTrace]
  refine ⟨76875447492036182072468335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102500596656048242763291113 76875447492036182072468335)
  ·
    refine ⟨115313171238054273108702503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76875447492036182072468335 115313171238054273108702503)
    ·
      refine ⟨172969756857081409663053755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115313171238054273108702503 172969756857081409663053755)
      ·
        refine ⟨259454635285622114494580633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172969756857081409663053755 259454635285622114494580633)
        ·
          refine ⟨194590976464216585870935475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259454635285622114494580633 194590976464216585870935475)
          ·
            refine ⟨291886464696324878806403213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194590976464216585870935475 291886464696324878806403213)
            ·
              refine ⟨109457424261121829552401205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 291886464696324878806403213 109457424261121829552401205)
              ·
                refine ⟨10261633524480171520537613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109457424261121829552401205 10261633524480171520537613)
                ·
                  refine ⟨3848112571680064320201605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10261633524480171520537613 3848112571680064320201605)
                  ·
                    refine ⟨721521107190012060037801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3848112571680064320201605 721521107190012060037801)
                    ·
                      rfl

theorem cell23_4215472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 3, 4].length) (baseStart_4215472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215472 prefixEnd_4215472 := by exact prefixLift 4215472
  have htrace : WordTrace (prefixWord ++ tailWord_4215472) baseStart_4215472 baseEnd_4215472 := by
    simpa [prefixWord, tailWord_4215472, baseEnd_4215472] using wordTrace_append hprefix tailTrace_4215472
  have hstable : (prefixWord ++ tailWord_4215472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215472).length < 2 ^ (prefixWord ++ tailWord_4215472).sum := by decide
  have hdescent : baseEnd_4215472 < baseStart_4215472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215482 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3]
def baseStart_4215482 : Nat := 118140960795 + 4215482 * 2 ^ 59
def prefixEnd_4215482 : Nat := 4983230072969 + 3 ^ 40 * 4215482 * 2
def baseEnd_4215482 : Nat := 2164568456376581140988357

theorem tailTrace_4215482 : CollatzResearch.WordTrace tailWord_4215482 prefixEnd_4215482 2164568456376581140988357 := by
  unfold tailWord_4215482
  simp only [CollatzResearch.WordTrace]
  refine ⟨38437814928509033963200175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102500839809357423901867133 38437814928509033963200175)
  ·
    refine ⟨57656722392763550944800263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38437814928509033963200175 57656722392763550944800263)
    ·
      refine ⟨86485083589145326417200395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57656722392763550944800263 86485083589145326417200395)
      ·
        refine ⟨129727625383717989625800593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86485083589145326417200395 129727625383717989625800593)
        ·
          refine ⟨97295719037788492219350445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129727625383717989625800593 97295719037788492219350445)
          ·
            refine ⟨36485894639170684582256417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97295719037788492219350445 36485894639170684582256417)
            ·
              refine ⟨27364420979378013436692313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36485894639170684582256417 27364420979378013436692313)
              ·
                refine ⟨20523315734533510077519235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27364420979378013436692313 20523315734533510077519235)
                ·
                  refine ⟨30784973601800265116278853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20523315734533510077519235 30784973601800265116278853)
                  ·
                    refine ⟨5772182550337549709302285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30784973601800265116278853 5772182550337549709302285)
                    ·
                      refine ⟨2164568456376581140988357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5772182550337549709302285 2164568456376581140988357)
                      ·
                        rfl

theorem cell23_4215482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_4215482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215482 prefixEnd_4215482 := by exact prefixLift 4215482
  have htrace : WordTrace (prefixWord ++ tailWord_4215482) baseStart_4215482 baseEnd_4215482 := by
    simpa [prefixWord, tailWord_4215482, baseEnd_4215482] using wordTrace_append hprefix tailTrace_4215482
  have hstable : (prefixWord ++ tailWord_4215482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215482).length < 2 ^ (prefixWord ++ tailWord_4215482).sum := by decide
  have hdescent : baseEnd_4215482 < baseStart_4215482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215519 : List Nat := [1, 1, 2, 3, 2, 5, 1, 2, 6]
def baseStart_4215519 : Nat := 118140960795 + 4215519 * 2 ^ 59
def prefixEnd_4215519 : Nat := 4983230072969 + 3 ^ 40 * 4215519 * 2
def baseEnd_4215519 : Nat := 240509717240088610691743

theorem tailTrace_4215519 : CollatzResearch.WordTrace tailWord_4215519 prefixEnd_4215519 240509717240088610691743 := by
  unfold tailWord_4215519
  simp only [CollatzResearch.WordTrace]
  refine ⟨153752609214902091171897611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102501739476601394114598407 153752609214902091171897611)
  ·
    refine ⟨230628913822353136757846417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153752609214902091171897611 230628913822353136757846417)
    ·
      refine ⟨172971685366764852568384813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230628913822353136757846417 172971685366764852568384813)
      ·
        refine ⟨64864382012536819713144305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172971685366764852568384813 64864382012536819713144305)
        ·
          refine ⟨48648286509402614784858229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64864382012536819713144305 48648286509402614784858229)
          ·
            refine ⟨4560776860256495136080459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48648286509402614784858229 4560776860256495136080459)
            ·
              refine ⟨6841165290384742704120689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4560776860256495136080459 6841165290384742704120689)
              ·
                refine ⟨5130873967788557028090517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6841165290384742704120689 5130873967788557028090517)
                ·
                  refine ⟨240509717240088610691743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5130873967788557028090517 240509717240088610691743)
                  ·
                    rfl

theorem cell23_4215519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 6].length) (baseStart_4215519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215519 prefixEnd_4215519 := by exact prefixLift 4215519
  have htrace : WordTrace (prefixWord ++ tailWord_4215519) baseStart_4215519 baseEnd_4215519 := by
    simpa [prefixWord, tailWord_4215519, baseEnd_4215519] using wordTrace_append hprefix tailTrace_4215519
  have hstable : (prefixWord ++ tailWord_4215519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215519).length < 2 ^ (prefixWord ++ tailWord_4215519).sum := by decide
  have hdescent : baseEnd_4215519 < baseStart_4215519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215529 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 3, 1, 3]
def baseStart_4215529 : Nat := 118140960795 + 4215529 * 2 ^ 59
def prefixEnd_4215529 : Nat := 4983230072969 + 3 ^ 40 * 4215529 * 2
def baseEnd_4215529 : Nat := 2164592589967342457100641

theorem tailTrace_4215529 : CollatzResearch.WordTrace tailWord_4215529 prefixEnd_4215529 2164592589967342457100641 := by
  unfold tailWord_4215529
  simp only [CollatzResearch.WordTrace]
  refine ⟨153752973944865862879761641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102501982629910575253174427 153752973944865862879761641)
  ·
    refine ⟨115314730458649397159821231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153752973944865862879761641 115314730458649397159821231)
    ·
      refine ⟨172972095687974095739731847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115314730458649397159821231 172972095687974095739731847)
      ·
        refine ⟨259458143531961143609597771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172972095687974095739731847 259458143531961143609597771)
        ·
          refine ⟨389187215297941715414396657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259458143531961143609597771 389187215297941715414396657)
          ·
            refine ⟨291890411473456286560797493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389187215297941715414396657 291890411473456286560797493)
            ·
              refine ⟨27364726075636526865074765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 291890411473456286560797493 27364726075636526865074765)
              ·
                refine ⟨10261772278363697574403037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27364726075636526865074765 10261772278363697574403037)
                ·
                  refine ⟨3848164604386386590401139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10261772278363697574403037 3848164604386386590401139)
                  ·
                    refine ⟨5772246906579579885601709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3848164604386386590401139 5772246906579579885601709)
                    ·
                      refine ⟨2164592589967342457100641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5772246906579579885601709 2164592589967342457100641)
                      ·
                        rfl

theorem cell23_4215529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 1, 3].length) (baseStart_4215529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215529 prefixEnd_4215529 := by exact prefixLift 4215529
  have htrace : WordTrace (prefixWord ++ tailWord_4215529) baseStart_4215529 baseEnd_4215529 := by
    simpa [prefixWord, tailWord_4215529, baseEnd_4215529] using wordTrace_append hprefix tailTrace_4215529
  have hstable : (prefixWord ++ tailWord_4215529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215529).length < 2 ^ (prefixWord ++ tailWord_4215529).sum := by decide
  have hdescent : baseEnd_4215529 < baseStart_4215529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215549 : List Nat := [1, 4, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_4215549 : Nat := 118140960795 + 4215549 * 2 ^ 59
def prefixEnd_4215549 : Nat := 4983230072969 + 3 ^ 40 * 4215549 * 2
def baseEnd_4215549 : Nat := 721534286526810792950183

theorem tailTrace_4215549 : CollatzResearch.WordTrace tailWord_4215549 prefixEnd_4215549 721534286526810792950183 := by
  unfold tailWord_4215549
  simp only [CollatzResearch.WordTrace]
  refine ⟨153753703404793406295489701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102502468936528937530326467 153753703404793406295489701)
  ·
    refine ⟨28828819388398763680404319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153753703404793406295489701 28828819388398763680404319)
    ·
      refine ⟨43243229082598145520606479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28828819388398763680404319 43243229082598145520606479)
      ·
        refine ⟨64864843623897218280909719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43243229082598145520606479 64864843623897218280909719)
        ·
          refine ⟨97297265435845827421364579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64864843623897218280909719 97297265435845827421364579)
          ·
            refine ⟨145945898153768741132046869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97297265435845827421364579 145945898153768741132046869)
            ·
              refine ⟨6841213975957909740564697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 145945898153768741132046869 6841213975957909740564697)
              ·
                refine ⟨5130910481968432305423523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6841213975957909740564697 5130910481968432305423523)
                ·
                  refine ⟨7696365722952648458135285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5130910481968432305423523 7696365722952648458135285)
                  ·
                    refine ⟨721534286526810792950183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7696365722952648458135285 721534286526810792950183)
                    ·
                      rfl

theorem cell23_4215549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_4215549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215549 prefixEnd_4215549 := by exact prefixLift 4215549
  have htrace : WordTrace (prefixWord ++ tailWord_4215549) baseStart_4215549 baseEnd_4215549 := by
    simpa [prefixWord, tailWord_4215549, baseEnd_4215549] using wordTrace_append hprefix tailTrace_4215549
  have hstable : (prefixWord ++ tailWord_4215549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215549).length < 2 ^ (prefixWord ++ tailWord_4215549).sum := by decide
  have hdescent : baseEnd_4215549 < baseStart_4215549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215556 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_4215556 : Nat := 118140960795 + 4215556 * 2 ^ 59
def prefixEnd_4215556 : Nat := 4983230072969 + 3 ^ 40 * 4215556 * 2
def baseEnd_4215556 : Nat := 2164606453945013851463017

theorem tailTrace_4215556 : CollatzResearch.WordTrace tailWord_4215556 prefixEnd_4215556 2164606453945013851463017 := by
  unfold tailWord_4215556
  simp only [CollatzResearch.WordTrace]
  refine ⟨76876979357884023245497261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102502639143845364327329681 76876979357884023245497261)
  ·
    refine ⟨28828867259206508717061473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76876979357884023245497261 28828867259206508717061473)
    ·
      refine ⟨21621650444404881537796105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28828867259206508717061473 21621650444404881537796105)
      ·
        refine ⟨16216237833303661153347079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21621650444404881537796105 16216237833303661153347079)
        ·
          refine ⟨24324356749955491730020619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16216237833303661153347079 24324356749955491730020619)
          ·
            refine ⟨36486535124933237595030929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24324356749955491730020619 36486535124933237595030929)
            ·
              refine ⟨27364901343699928196273197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36486535124933237595030929 27364901343699928196273197)
              ·
                refine ⟨10261838003887473073602449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27364901343699928196273197 10261838003887473073602449)
                ·
                  refine ⟨7696378502915604805201837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10261838003887473073602449 7696378502915604805201837)
                  ·
                    refine ⟨2886141938593351801950689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7696378502915604805201837 2886141938593351801950689)
                    ·
                      refine ⟨2164606453945013851463017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2886141938593351801950689 2164606453945013851463017)
                      ·
                        rfl

theorem cell23_4215556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_4215556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215556 prefixEnd_4215556 := by exact prefixLift 4215556
  have htrace : WordTrace (prefixWord ++ tailWord_4215556) baseStart_4215556 baseEnd_4215556 := by
    simpa [prefixWord, tailWord_4215556, baseEnd_4215556] using wordTrace_append hprefix tailTrace_4215556
  have hstable : (prefixWord ++ tailWord_4215556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215556).length < 2 ^ (prefixWord ++ tailWord_4215556).sum := by decide
  have hdescent : baseEnd_4215556 < baseStart_4215556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215562 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 3, 6]
def baseStart_4215562 : Nat := 118140960795 + 4215562 * 2 ^ 59
def prefixEnd_4215562 : Nat := 4983230072969 + 3 ^ 40 * 4215562 * 2
def baseEnd_4215562 : Nat := 721536511609646942662663

theorem tailTrace_4215562 : CollatzResearch.WordTrace tailWord_4215562 prefixEnd_4215562 721536511609646942662663 := by
  unfold tailWord_4215562
  simp only [CollatzResearch.WordTrace]
  refine ⟨38438544388436577378928235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102502785035830873010475293 38438544388436577378928235)
  ·
    refine ⟨57657816582654866068392353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38438544388436577378928235 57657816582654866068392353)
    ·
      refine ⟨43243362436991149551294265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57657816582654866068392353 43243362436991149551294265)
      ·
        refine ⟨32432521827743362163470699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43243362436991149551294265 32432521827743362163470699)
        ·
          refine ⟨48648782741615043245206049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32432521827743362163470699 48648782741615043245206049)
          ·
            refine ⟨36486587056211282433904537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48648782741615043245206049 36486587056211282433904537)
            ·
              refine ⟨27364940292158461825428403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36486587056211282433904537 27364940292158461825428403)
              ·
                refine ⟨41047410438237692738142605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27364940292158461825428403 41047410438237692738142605)
                ·
                  refine ⟨15392778914339134776803477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41047410438237692738142605 15392778914339134776803477)
                  ·
                    refine ⟨721536511609646942662663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15392778914339134776803477 721536511609646942662663)
                    ·
                      rfl

theorem cell23_4215562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_4215562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215562 prefixEnd_4215562 := by exact prefixLift 4215562
  have htrace : WordTrace (prefixWord ++ tailWord_4215562) baseStart_4215562 baseEnd_4215562 := by
    simpa [prefixWord, tailWord_4215562, baseEnd_4215562] using wordTrace_append hprefix tailTrace_4215562
  have hstable : (prefixWord ++ tailWord_4215562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215562).length < 2 ^ (prefixWord ++ tailWord_4215562).sum := by decide
  have hdescent : baseEnd_4215562 < baseStart_4215562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215569 : List Nat := [1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 4]
def baseStart_4215569 : Nat := 118140960795 + 4215569 * 2 ^ 59
def prefixEnd_4215569 : Nat := 4983230072969 + 3 ^ 40 * 4215569 * 2
def baseEnd_4215569 : Nat := 2164613129193522300600457

theorem tailTrace_4215569 : CollatzResearch.WordTrace tailWord_4215569 prefixEnd_4215569 2164613129193522300600457 := by
  unfold tailWord_4215569
  simp only [CollatzResearch.WordTrace]
  refine ⟨153754432864720949711217761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102502955243147299807478507 153754432864720949711217761)
  ·
    refine ⟨115315824648540712283413321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153754432864720949711217761 115315824648540712283413321)
    ·
      refine ⟨86486868486405534212559991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115315824648540712283413321 86486868486405534212559991)
      ·
        refine ⟨129730302729608301318839987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86486868486405534212559991 129730302729608301318839987)
        ·
          refine ⟨194595454094412451978259981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129730302729608301318839987 194595454094412451978259981)
          ·
            refine ⟨72973295285404669491847493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194595454094412451978259981 72973295285404669491847493)
            ·
              refine ⟨13682492866013375529721405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72973295285404669491847493 13682492866013375529721405)
              ·
                refine ⟨5130934824755015823645527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13682492866013375529721405 5130934824755015823645527)
                ·
                  refine ⟨7696402237132523735468291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5130934824755015823645527 7696402237132523735468291)
                  ·
                    refine ⟨11544603355698785603202437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7696402237132523735468291 11544603355698785603202437)
                    ·
                      refine ⟨2164613129193522300600457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11544603355698785603202437 2164613129193522300600457)
                      ·
                        rfl

theorem cell23_4215569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_4215569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215569 prefixEnd_4215569 := by exact prefixLift 4215569
  have htrace : WordTrace (prefixWord ++ tailWord_4215569) baseStart_4215569 baseEnd_4215569 := by
    simpa [prefixWord, tailWord_4215569, baseEnd_4215569] using wordTrace_append hprefix tailTrace_4215569
  have hstable : (prefixWord ++ tailWord_4215569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215569).length < 2 ^ (prefixWord ++ tailWord_4215569).sum := by decide
  have hdescent : baseEnd_4215569 < baseStart_4215569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215580 : List Nat := [2, 2, 3, 1, 1, 4, 3, 2, 1, 1, 3]
def baseStart_4215580 : Nat := 118140960795 + 4215580 * 2 ^ 59
def prefixEnd_4215580 : Nat := 4983230072969 + 3 ^ 40 * 4215580 * 2
def baseEnd_4215580 : Nat := 2164618777480721757562907

theorem tailTrace_4215580 : CollatzResearch.WordTrace tailWord_4215580 prefixEnd_4215580 2164618777480721757562907 := by
  unfold tailWord_4215580
  simp only [CollatzResearch.WordTrace]
  refine ⟨76877417033840549294934097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102503222711787399059912129 76877417033840549294934097)
  ·
    refine ⟨57658062775380411971200573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76877417033840549294934097 57658062775380411971200573)
    ·
      refine ⟨21621773540767654489200215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57658062775380411971200573 21621773540767654489200215)
      ·
        refine ⟨32432660311151481733800323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21621773540767654489200215 32432660311151481733800323)
        ·
          refine ⟨48648990466727222600700485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32432660311151481733800323 48648990466727222600700485)
          ·
            refine ⟨9121685712511354237631341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48648990466727222600700485 9121685712511354237631341)
            ·
              refine ⟨3420632142191757839111753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9121685712511354237631341 3420632142191757839111753)
              ·
                refine ⟨2565474106643818379333815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3420632142191757839111753 2565474106643818379333815)
                ·
                  refine ⟨3848211159965727569000723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2565474106643818379333815 3848211159965727569000723)
                  ·
                    refine ⟨5772316739948591353501085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3848211159965727569000723 5772316739948591353501085)
                    ·
                      refine ⟨2164618777480721757562907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5772316739948591353501085 2164618777480721757562907)
                      ·
                        rfl

theorem cell23_4215580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_4215580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215580 prefixEnd_4215580 := by exact prefixLift 4215580
  have htrace : WordTrace (prefixWord ++ tailWord_4215580) baseStart_4215580 baseEnd_4215580 := by
    simpa [prefixWord, tailWord_4215580, baseEnd_4215580] using wordTrace_append hprefix tailTrace_4215580
  have hstable : (prefixWord ++ tailWord_4215580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215580).length < 2 ^ (prefixWord ++ tailWord_4215580).sum := by decide
  have hdescent : baseEnd_4215580 < baseStart_4215580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215589 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 3, 2, 3]
def baseStart_4215589 : Nat := 118140960795 + 4215589 * 2 ^ 59
def prefixEnd_4215589 : Nat := 4983230072969 + 3 ^ 40 * 4215589 * 2
def baseEnd_4215589 : Nat := 2164623398806612222350365

theorem tailTrace_4215589 : CollatzResearch.WordTrace tailWord_4215589 prefixEnd_4215589 2164623398806612222350365 := by
  unfold tailWord_4215589
  simp only [CollatzResearch.WordTrace]
  refine ⟨153755162324648493126945821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102503441549765662084630547 153755162324648493126945821)
  ·
    refine ⟨57658185871743184922604683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153755162324648493126945821 57658185871743184922604683)
    ·
      refine ⟨86487278807614777383907025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57658185871743184922604683 86487278807614777383907025)
      ·
        refine ⟨64865459105711083037930269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86487278807614777383907025 64865459105711083037930269)
        ·
          refine ⟨24324547164641656139223851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64865459105711083037930269 24324547164641656139223851)
          ·
            refine ⟨36486820746962484208835777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24324547164641656139223851 36486820746962484208835777)
            ·
              refine ⟨27365115560221863156626833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36486820746962484208835777 27365115560221863156626833)
              ·
                refine ⟨20523836670166397367470125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27365115560221863156626833 20523836670166397367470125)
                ·
                  refine ⟨7696438751312399012801297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20523836670166397367470125 7696438751312399012801297)
                  ·
                    refine ⟨5772329063484299259600973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7696438751312399012801297 5772329063484299259600973)
                    ·
                      refine ⟨2164623398806612222350365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5772329063484299259600973 2164623398806612222350365)
                      ·
                        rfl

theorem cell23_4215589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_4215589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215589 prefixEnd_4215589 := by exact prefixLift 4215589
  have htrace : WordTrace (prefixWord ++ tailWord_4215589) baseStart_4215589 baseEnd_4215589 := by
    simpa [prefixWord, tailWord_4215589, baseEnd_4215589] using wordTrace_append hprefix tailTrace_4215589
  have hstable : (prefixWord ++ tailWord_4215589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215589).length < 2 ^ (prefixWord ++ tailWord_4215589).sum := by decide
  have hdescent : baseEnd_4215589 < baseStart_4215589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215619 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 3]
def baseStart_4215619 : Nat := 118140960795 + 4215619 * 2 ^ 59
def prefixEnd_4215619 : Nat := 4983230072969 + 3 ^ 40 * 4215619 * 2
def baseEnd_4215619 : Nat := 2164638803226247104975227

theorem tailTrace_4215619 : CollatzResearch.WordTrace tailWord_4215619 prefixEnd_4215619 2164638803226247104975227 := by
  unfold tailWord_4215619
  simp only [CollatzResearch.WordTrace]
  refine ⟨153756256514539808250537911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102504171009693205500358607 153756256514539808250537911)
  ·
    refine ⟨230634384771809712375806867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153756256514539808250537911 230634384771809712375806867)
    ·
      refine ⟨345951577157714568563710301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230634384771809712375806867 345951577157714568563710301)
      ·
        refine ⟨129731841434142963211391363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 345951577157714568563710301 129731841434142963211391363)
        ·
          refine ⟨194597762151214444817087045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129731841434142963211391363 194597762151214444817087045)
          ·
            refine ⟨36487080403352708403203821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194597762151214444817087045 36487080403352708403203821)
            ·
              refine ⟨13682655151257265651201433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36487080403352708403203821 13682655151257265651201433)
              ·
                refine ⟨10261991363442949238401075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13682655151257265651201433 10261991363442949238401075)
                ·
                  refine ⟨15392987045164423857601613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10261991363442949238401075 15392987045164423857601613)
                  ·
                    refine ⟨5772370141936658946600605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15392987045164423857601613 5772370141936658946600605)
                    ·
                      refine ⟨2164638803226247104975227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5772370141936658946600605 2164638803226247104975227)
                      ·
                        rfl

theorem cell23_4215619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_4215619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215619 prefixEnd_4215619 := by exact prefixLift 4215619
  have htrace : WordTrace (prefixWord ++ tailWord_4215619) baseStart_4215619 baseEnd_4215619 := by
    simpa [prefixWord, tailWord_4215619, baseEnd_4215619] using wordTrace_append hprefix tailTrace_4215619
  have hstable : (prefixWord ++ tailWord_4215619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215619).length < 2 ^ (prefixWord ++ tailWord_4215619).sum := by decide
  have hdescent : baseEnd_4215619 < baseStart_4215619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215632 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 5]
def baseStart_4215632 : Nat := 118140960795 + 4215632 * 2 ^ 59
def prefixEnd_4215632 : Nat := 4983230072969 + 3 ^ 40 * 4215632 * 2
def baseEnd_4215632 : Nat := 2164645478474755554112667

theorem tailTrace_4215632 : CollatzResearch.WordTrace tailWord_4215632 prefixEnd_4215632 2164645478474755554112667 := by
  unfold tailWord_4215632
  simp only [CollatzResearch.WordTrace]
  refine ⟨76878365331746355735380575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102504487108995140980507433 76878365331746355735380575)
  ·
    refine ⟨115317547997619533603070863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76878365331746355735380575 115317547997619533603070863)
    ·
      refine ⟨172976321996429300404606295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115317547997619533603070863 172976321996429300404606295)
      ·
        refine ⟨259464482994643950606909443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172976321996429300404606295 259464482994643950606909443)
        ·
          refine ⟨389196724491965925910364165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259464482994643950606909443 389196724491965925910364165)
          ·
            refine ⟨72974385842243611108193281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 389196724491965925910364165 72974385842243611108193281)
            ·
              refine ⟨54730789381682708331144961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72974385842243611108193281 54730789381682708331144961)
              ·
                refine ⟨41048092036262031248358721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54730789381682708331144961 41048092036262031248358721)
                ·
                  refine ⟨30786069027196523436269041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41048092036262031248358721 30786069027196523436269041)
                  ·
                    refine ⟨23089551770397392577201781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30786069027196523436269041 23089551770397392577201781)
                    ·
                      refine ⟨2164645478474755554112667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23089551770397392577201781 2164645478474755554112667)
                      ·
                        rfl

theorem cell23_4215632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_4215632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215632 prefixEnd_4215632 := by exact prefixLift 4215632
  have htrace : WordTrace (prefixWord ++ tailWord_4215632) baseStart_4215632 baseEnd_4215632 := by
    simpa [prefixWord, tailWord_4215632, baseEnd_4215632] using wordTrace_append hprefix tailTrace_4215632
  have hstable : (prefixWord ++ tailWord_4215632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215632).length < 2 ^ (prefixWord ++ tailWord_4215632).sum := by decide
  have hdescent : baseEnd_4215632 < baseStart_4215632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215689 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 2, 2, 4]
def baseStart_4215689 : Nat := 118140960795 + 4215689 * 2 ^ 59
def prefixEnd_4215689 : Nat := 4983230072969 + 3 ^ 40 * 4215689 * 2
def baseEnd_4215689 : Nat := 2164674746872061831099905

theorem tailTrace_4215689 : CollatzResearch.WordTrace tailWord_4215689 prefixEnd_4215689 2164674746872061831099905 := by
  unfold tailWord_4215689
  simp only [CollatzResearch.WordTrace]
  refine ⟨153758809624286210205586121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102505873082857473470390747 153758809624286210205586121)
  ·
    refine ⟨115319107218214657654189591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153758809624286210205586121 115319107218214657654189591)
    ·
      refine ⟨172978660827321986481284387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115319107218214657654189591 172978660827321986481284387)
      ·
        refine ⟨259467991240982979721926581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172978660827321986481284387 259467991240982979721926581)
        ·
          refine ⟨24325124178842154348930617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 259467991240982979721926581 24325124178842154348930617)
          ·
            refine ⟨18243843134131615761697963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24325124178842154348930617 18243843134131615761697963)
            ·
              refine ⟨27365764701197423642546945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18243843134131615761697963 27365764701197423642546945)
              ·
                refine ⟨20524323525898067731910209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27365764701197423642546945 20524323525898067731910209)
                ·
                  refine ⟨15393242644423550798932657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20524323525898067731910209 15393242644423550798932657)
                  ·
                    refine ⟨11544931983317663099199493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15393242644423550798932657 11544931983317663099199493)
                    ·
                      refine ⟨2164674746872061831099905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11544931983317663099199493 2164674746872061831099905)
                      ·
                        rfl

theorem cell23_4215689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_4215689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215689 prefixEnd_4215689 := by exact prefixLift 4215689
  have htrace : WordTrace (prefixWord ++ tailWord_4215689) baseStart_4215689 baseEnd_4215689 := by
    simpa [prefixWord, tailWord_4215689, baseEnd_4215689] using wordTrace_append hprefix tailTrace_4215689
  have hstable : (prefixWord ++ tailWord_4215689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215689).length < 2 ^ (prefixWord ++ tailWord_4215689).sum := by decide
  have hdescent : baseEnd_4215689 < baseStart_4215689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215783 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_4215783 : Nat := 118140960795 + 4215783 * 2 ^ 59
def prefixEnd_4215783 : Nat := 4983230072969 + 3 ^ 40 * 4215783 * 2
def baseEnd_4215783 : Nat := 2164723014053584463324473

theorem tailTrace_4215783 : CollatzResearch.WordTrace tailWord_4215783 prefixEnd_4215783 2164723014053584463324473 := by
  unfold tailWord_4215783
  simp only [CollatzResearch.WordTrace]
  refine ⟨153762238085945664259508003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102508158723963776173005335 153762238085945664259508003)
  ·
    refine ⟨230643357128918496389262005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153762238085945664259508003 230643357128918496389262005)
    ·
      refine ⟨21622814730836109036493313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 230643357128918496389262005 21622814730836109036493313)
      ·
        refine ⟨16217111048127081777369985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21622814730836109036493313 16217111048127081777369985)
        ·
          refine ⟨12162833286095311333027489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16217111048127081777369985 12162833286095311333027489)
          ·
            refine ⟨9122124964571483499770617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12162833286095311333027489 9122124964571483499770617)
            ·
              refine ⟨6841593723428612624827963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9122124964571483499770617 6841593723428612624827963)
              ·
                refine ⟨10262390585142918937241945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6841593723428612624827963 10262390585142918937241945)
                ·
                  refine ⟨7696792938857189202931459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10262390585142918937241945 7696792938857189202931459)
                  ·
                    refine ⟨11545189408285783804397189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7696792938857189202931459 11545189408285783804397189)
                    ·
                      refine ⟨2164723014053584463324473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11545189408285783804397189 2164723014053584463324473)
                      ·
                        rfl

theorem cell23_4215783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_4215783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215783 prefixEnd_4215783 := by exact prefixLift 4215783
  have htrace : WordTrace (prefixWord ++ tailWord_4215783) baseStart_4215783 baseEnd_4215783 := by
    simpa [prefixWord, tailWord_4215783, baseEnd_4215783] using wordTrace_append hprefix tailTrace_4215783
  have hstable : (prefixWord ++ tailWord_4215783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215783).length < 2 ^ (prefixWord ++ tailWord_4215783).sum := by decide
  have hdescent : baseEnd_4215783 < baseStart_4215783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215837 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_4215837 : Nat := 118140960795 + 4215837 * 2 ^ 59
def prefixEnd_4215837 : Nat := 4983230072969 + 3 ^ 40 * 4215837 * 2
def baseEnd_4215837 : Nat := 2164750742008927252049225

theorem tailTrace_4215837 : CollatzResearch.WordTrace tailWord_4215837 prefixEnd_4215837 2164750742008927252049225 := by
  unfold tailWord_4215837
  simp only [CollatzResearch.WordTrace]
  refine ⟨153764207627750031481973765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102509471751833354321315843 153764207627750031481973765)
  ·
    refine ⟨28830788930203130902870081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153764207627750031481973765 28830788930203130902870081)
    ·
      refine ⟨21623091697652348177152561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28830788930203130902870081 21623091697652348177152561)
      ·
        refine ⟨16217318773239261132864421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21623091697652348177152561 16217318773239261132864421)
        ·
          refine ⟨3040747269982361462412079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16217318773239261132864421 3040747269982361462412079)
          ·
            refine ⟨4561120904973542193618119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040747269982361462412079 4561120904973542193618119)
            ·
              refine ⟨6841681357460313290427179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4561120904973542193618119 6841681357460313290427179)
              ·
                refine ⟨10262522036190469935640769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6841681357460313290427179 10262522036190469935640769)
                ·
                  refine ⟨7696891527142852451730577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10262522036190469935640769 7696891527142852451730577)
                  ·
                    refine ⟨5772668645357139338797933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7696891527142852451730577 5772668645357139338797933)
                    ·
                      refine ⟨2164750742008927252049225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5772668645357139338797933 2164750742008927252049225)
                      ·
                        rfl

theorem cell23_4215837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_4215837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215837 prefixEnd_4215837 := by exact prefixLift 4215837
  have htrace : WordTrace (prefixWord ++ tailWord_4215837) baseStart_4215837 baseEnd_4215837 := by
    simpa [prefixWord, tailWord_4215837, baseEnd_4215837] using wordTrace_append hprefix tailTrace_4215837
  have hstable : (prefixWord ++ tailWord_4215837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215837).length < 2 ^ (prefixWord ++ tailWord_4215837).sum := by decide
  have hdescent : baseEnd_4215837 < baseStart_4215837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215843 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 1, 5, 2]
def baseStart_4215843 : Nat := 118140960795 + 4215843 * 2 ^ 59
def prefixEnd_4215843 : Nat := 4983230072969 + 3 ^ 40 * 4215843 * 2
def baseEnd_4215843 : Nat := 2164753822892854228574197

theorem tailTrace_4215843 : CollatzResearch.WordTrace tailWord_4215843 prefixEnd_4215843 2164753822892854228574197 := by
  unfold tailWord_4215843
  simp only [CollatzResearch.WordTrace]
  refine ⟨153764426465728294506692183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102509617643818863004461455 153764426465728294506692183)
  ·
    refine ⟨230646639698592441760038275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153764426465728294506692183 230646639698592441760038275)
    ·
      refine ⟨345969959547888662640057413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230646639698592441760038275 345969959547888662640057413)
      ·
        refine ⟨64869367415229124245010765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 345969959547888662640057413 64869367415229124245010765)
        ·
          refine ⟨24326012780710921591879037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64869367415229124245010765 24326012780710921591879037)
          ·
            refine ⟨9122254792766595596954639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24326012780710921591879037 9122254792766595596954639)
            ·
              refine ⟨13683382189149893395431959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9122254792766595596954639 13683382189149893395431959)
              ·
                refine ⟨20525073283724840093147939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13683382189149893395431959 20525073283724840093147939)
                ·
                  refine ⟨30787609925587260139721909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20525073283724840093147939 30787609925587260139721909)
                  ·
                    refine ⟨2886338430523805638098929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30787609925587260139721909 2886338430523805638098929)
                    ·
                      refine ⟨2164753822892854228574197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2886338430523805638098929 2164753822892854228574197)
                      ·
                        rfl

theorem cell23_4215843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_4215843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215843 prefixEnd_4215843 := by exact prefixLift 4215843
  have htrace : WordTrace (prefixWord ++ tailWord_4215843) baseStart_4215843 baseEnd_4215843 := by
    simpa [prefixWord, tailWord_4215843, baseEnd_4215843] using wordTrace_append hprefix tailTrace_4215843
  have hstable : (prefixWord ++ tailWord_4215843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215843).length < 2 ^ (prefixWord ++ tailWord_4215843).sum := by decide
  have hdescent : baseEnd_4215843 < baseStart_4215843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215886 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_4215886 : Nat := 118140960795 + 4215886 * 2 ^ 59
def prefixEnd_4215886 : Nat := 4983230072969 + 3 ^ 40 * 4215886 * 2
def baseEnd_4215886 : Nat := 2164775902560997560336499

theorem tailTrace_4215886 : CollatzResearch.WordTrace tailWord_4215886 prefixEnd_4215886 2164775902560997560336499 := by
  unfold tailWord_4215886
  simp only [CollatzResearch.WordTrace]
  refine ⟨19220749350571564106313439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102510663203048341900338341 19220749350571564106313439)
  ·
    refine ⟨28831124025857346159470159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19220749350571564106313439 28831124025857346159470159)
    ·
      refine ⟨43246686038786019239205239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28831124025857346159470159 43246686038786019239205239)
      ·
        refine ⟨64870029058179028858807859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43246686038786019239205239 64870029058179028858807859)
        ·
          refine ⟨97305043587268543288211789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64870029058179028858807859 97305043587268543288211789)
          ·
            refine ⟨36489391345225703733079421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97305043587268543288211789 36489391345225703733079421)
            ·
              refine ⟨13683521754459638899904783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36489391345225703733079421 13683521754459638899904783)
              ·
                refine ⟨20525282631689458349857175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13683521754459638899904783 20525282631689458349857175)
                ·
                  refine ⟨30787923947534187524785763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20525282631689458349857175 30787923947534187524785763)
                  ·
                    refine ⟨46181885921301281287178645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30787923947534187524785763 46181885921301281287178645)
                    ·
                      refine ⟨2164775902560997560336499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46181885921301281287178645 2164775902560997560336499)
                      ·
                        rfl

theorem cell23_4215886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_4215886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215886 prefixEnd_4215886 := by exact prefixLift 4215886
  have htrace : WordTrace (prefixWord ++ tailWord_4215886) baseStart_4215886 baseEnd_4215886 := by
    simpa [prefixWord, tailWord_4215886, baseEnd_4215886] using wordTrace_append hprefix tailTrace_4215886
  have hstable : (prefixWord ++ tailWord_4215886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215886).length < 2 ^ (prefixWord ++ tailWord_4215886).sum := by decide
  have hdescent : baseEnd_4215886 < baseStart_4215886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215890 : List Nat := [3, 2, 2, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_4215890 : Nat := 118140960795 + 4215890 * 2 ^ 59
def prefixEnd_4215890 : Nat := 4983230072969 + 3 ^ 40 * 4215890 * 2
def baseEnd_4215890 : Nat := 2164777956483615544686481

theorem tailTrace_4215890 : CollatzResearch.WordTrace tailWord_4215890 prefixEnd_4215890 2164777956483615544686481 := by
  unfold tailWord_4215890
  simp only [CollatzResearch.WordTrace]
  refine ⟨38441535174139505383413281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102510760464372014355768749 38441535174139505383413281)
  ·
    refine ⟨28831151380604629037559961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38441535174139505383413281 28831151380604629037559961)
    ·
      refine ⟨21623363535453471778169971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28831151380604629037559961 21623363535453471778169971)
      ·
        refine ⟨32435045303180207667254957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21623363535453471778169971 32435045303180207667254957)
        ·
          refine ⟨12163141988692577875220609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32435045303180207667254957 12163141988692577875220609)
          ·
            refine ⟨9122356491519433406415457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12163141988692577875220609 9122356491519433406415457)
            ·
              refine ⟨6841767368639575054811593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9122356491519433406415457 6841767368639575054811593)
              ·
                refine ⟨5131325526479681291108695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6841767368639575054811593 5131325526479681291108695)
                ·
                  refine ⟨7696988289719521936663043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5131325526479681291108695 7696988289719521936663043)
                  ·
                    refine ⟨11545482434579282904994565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7696988289719521936663043 11545482434579282904994565)
                    ·
                      refine ⟨2164777956483615544686481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11545482434579282904994565 2164777956483615544686481)
                      ·
                        rfl

theorem cell23_4215890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_4215890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215890 prefixEnd_4215890 := by exact prefixLift 4215890
  have htrace : WordTrace (prefixWord ++ tailWord_4215890) baseStart_4215890 baseEnd_4215890 := by
    simpa [prefixWord, tailWord_4215890, baseEnd_4215890] using wordTrace_append hprefix tailTrace_4215890
  have hstable : (prefixWord ++ tailWord_4215890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215890).length < 2 ^ (prefixWord ++ tailWord_4215890).sum := by decide
  have hdescent : baseEnd_4215890 < baseStart_4215890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215901 : List Nat := [1, 4, 4, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_4215901 : Nat := 118140960795 + 4215901 * 2 ^ 59
def prefixEnd_4215901 : Nat := 4983230072969 + 3 ^ 40 * 4215901 * 2
def baseEnd_4215901 : Nat := 2164783604770815001648931

theorem tailTrace_4215901 : CollatzResearch.WordTrace tailWord_4215901 prefixEnd_4215901 2164783604770815001648931 := by
  unfold tailWord_4215901
  simp only [CollatzResearch.WordTrace]
  refine ⟨153766541899518170412303557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102511027933012113608202371 153766541899518170412303557)
  ·
    refine ⟨28831226606159656952306917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153766541899518170412303557 28831226606159656952306917)
    ·
      refine ⟨5405854988654935678557547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28831226606159656952306917 5405854988654935678557547)
      ·
        refine ⟨8108782482982403517836321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5405854988654935678557547 8108782482982403517836321)
        ·
          refine ⟨6081586862236802638377241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8108782482982403517836321 6081586862236802638377241)
          ·
            refine ⟨4561190146677601978782931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6081586862236802638377241 4561190146677601978782931)
            ·
              refine ⟨6841785220016402968174397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4561190146677601978782931 6841785220016402968174397)
              ·
                refine ⟨2565669457506151113065399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6841785220016402968174397 2565669457506151113065399)
                ·
                  refine ⟨3848504186259226669598099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2565669457506151113065399 3848504186259226669598099)
                  ·
                    refine ⟨5772756279388840004397149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3848504186259226669598099 5772756279388840004397149)
                    ·
                      refine ⟨2164783604770815001648931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5772756279388840004397149 2164783604770815001648931)
                      ·
                        rfl

theorem cell23_4215901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_4215901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215901 prefixEnd_4215901 := by exact prefixLift 4215901
  have htrace : WordTrace (prefixWord ++ tailWord_4215901) baseStart_4215901 baseEnd_4215901 := by
    simpa [prefixWord, tailWord_4215901, baseEnd_4215901] using wordTrace_append hprefix tailTrace_4215901
  have hstable : (prefixWord ++ tailWord_4215901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215901).length < 2 ^ (prefixWord ++ tailWord_4215901).sum := by decide
  have hdescent : baseEnd_4215901 < baseStart_4215901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215944 : List Nat := [2, 1, 3, 4, 3, 1, 1, 2, 1, 2, 3]
def baseStart_4215944 : Nat := 118140960795 + 4215944 * 2 ^ 59
def prefixEnd_4215944 : Nat := 4983230072969 + 3 ^ 40 * 4215944 * 2
def baseEnd_4215944 : Nat := 2164805684438958333411233

theorem tailTrace_4215944 : CollatzResearch.WordTrace tailWord_4215944 prefixEnd_4215944 2164805684438958333411233 := by
  unfold tailWord_4215944
  simp only [CollatzResearch.WordTrace]
  refine ⟨76884055119181194378059443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102512073492241592504079257 76884055119181194378059443)
  ·
    refine ⟨115326082678771791567089165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76884055119181194378059443 115326082678771791567089165)
    ·
      refine ⟨43247281004539421837658437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115326082678771791567089165 43247281004539421837658437)
      ·
        refine ⟨8108865188351141594560957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43247281004539421837658437 8108865188351141594560957)
        ·
          refine ⟨3040824445631678097960359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8108865188351141594560957 3040824445631678097960359)
          ·
            refine ⟨4561236668447517146940539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040824445631678097960359 4561236668447517146940539)
            ·
              refine ⟨6841855002671275720410809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4561236668447517146940539 6841855002671275720410809)
              ·
                refine ⟨5131391252003456790308107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6841855002671275720410809 5131391252003456790308107)
                ·
                  refine ⟨7697086878005185185462161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5131391252003456790308107 7697086878005185185462161)
                  ·
                    refine ⟨5772815158503888889096621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7697086878005185185462161 5772815158503888889096621)
                    ·
                      refine ⟨2164805684438958333411233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5772815158503888889096621 2164805684438958333411233)
                      ·
                        rfl

theorem cell23_4215944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_4215944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215944 prefixEnd_4215944 := by exact prefixLift 4215944
  have htrace : WordTrace (prefixWord ++ tailWord_4215944) baseStart_4215944 baseEnd_4215944 := by
    simpa [prefixWord, tailWord_4215944, baseEnd_4215944] using wordTrace_append hprefix tailTrace_4215944
  have hstable : (prefixWord ++ tailWord_4215944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215944).length < 2 ^ (prefixWord ++ tailWord_4215944).sum := by decide
  have hdescent : baseEnd_4215944 < baseStart_4215944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215993 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 2, 2, 4]
def baseStart_4215993 : Nat := 118140960795 + 4215993 * 2 ^ 59
def prefixEnd_4215993 : Nat := 4983230072969 + 3 ^ 40 * 4215993 * 2
def baseEnd_4215993 : Nat := 2164830844991028641698507

theorem tailTrace_4215993 : CollatzResearch.WordTrace tailWord_4215993 prefixEnd_4215993 2164830844991028641698507 := by
  unfold tailWord_4215993
  simp only [CollatzResearch.WordTrace]
  refine ⟨153769897415184870124652633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102513264943456580083101755 153769897415184870124652633)
  ·
    refine ⟨115327423061388652593489475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153769897415184870124652633 115327423061388652593489475)
    ·
      refine ⟨172991134592082978890234213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115327423061388652593489475 172991134592082978890234213)
      ·
        refine ⟨32435837736015558541918915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172991134592082978890234213 32435837736015558541918915)
        ·
          refine ⟨48653756604023337812878373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32435837736015558541918915 48653756604023337812878373)
          ·
            refine ⟨9122579363254375839914695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48653756604023337812878373 9122579363254375839914695)
            ·
              refine ⟨13683869044881563759872043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9122579363254375839914695 13683869044881563759872043)
              ·
                refine ⟨20525803567322345639808065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13683869044881563759872043 20525803567322345639808065)
                ·
                  refine ⟨15394352675491759229856049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20525803567322345639808065 15394352675491759229856049)
                  ·
                    refine ⟨11545764506618819422392037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15394352675491759229856049 11545764506618819422392037)
                    ·
                      refine ⟨2164830844991028641698507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11545764506618819422392037 2164830844991028641698507)
                      ·
                        rfl

theorem cell23_4215993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_4215993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215993 prefixEnd_4215993 := by exact prefixLift 4215993
  have htrace : WordTrace (prefixWord ++ tailWord_4215993) baseStart_4215993 baseEnd_4215993 := by
    simpa [prefixWord, tailWord_4215993, baseEnd_4215993] using wordTrace_append hprefix tailTrace_4215993
  have hstable : (prefixWord ++ tailWord_4215993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215993).length < 2 ^ (prefixWord ++ tailWord_4215993).sum := by decide
  have hdescent : baseEnd_4215993 < baseStart_4215993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215997 : List Nat := [1, 4, 1, 2, 1, 1, 4, 3, 2, 2, 2]
def baseStart_4215997 : Nat := 118140960795 + 4215997 * 2 ^ 59
def prefixEnd_4215997 : Nat := 4983230072969 + 3 ^ 40 * 4215997 * 2
def baseEnd_4215997 : Nat := 2164832898913646626048489

theorem tailTrace_4215997 : CollatzResearch.WordTrace tailWord_4215997 prefixEnd_4215997 2164832898913646626048489 := by
  unfold tailWord_4215997
  simp only [CollatzResearch.WordTrace]
  refine ⟨153770043307170378807798245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102513362204780252538532163 153770043307170378807798245)
  ·
    refine ⟨28831883120094446026462171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153770043307170378807798245 28831883120094446026462171)
    ·
      refine ⟨43247824680141669039693257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28831883120094446026462171 43247824680141669039693257)
      ·
        refine ⟨32435868510106251779769943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43247824680141669039693257 32435868510106251779769943)
        ·
          refine ⟨48653802765159377669654915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32435868510106251779769943 48653802765159377669654915)
          ·
            refine ⟨72980704147739066504482373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48653802765159377669654915 72980704147739066504482373)
            ·
              refine ⟨13683882027701074969590445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72980704147739066504482373 13683882027701074969590445)
              ·
                refine ⟨5131455760387903113596417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13683882027701074969590445 5131455760387903113596417)
                ·
                  refine ⟨3848591820290927335197313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5131455760387903113596417 3848591820290927335197313)
                  ·
                    refine ⟨2886443865218195501397985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3848591820290927335197313 2886443865218195501397985)
                    ·
                      refine ⟨2164832898913646626048489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2886443865218195501397985 2164832898913646626048489)
                      ·
                        rfl

theorem cell23_4215997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_4215997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215997 prefixEnd_4215997 := by exact prefixLift 4215997
  have htrace : WordTrace (prefixWord ++ tailWord_4215997) baseStart_4215997 baseEnd_4215997 := by
    simpa [prefixWord, tailWord_4215997, baseEnd_4215997] using wordTrace_append hprefix tailTrace_4215997
  have hstable : (prefixWord ++ tailWord_4215997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215997).length < 2 ^ (prefixWord ++ tailWord_4215997).sum := by decide
  have hdescent : baseEnd_4215997 < baseStart_4215997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216073 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 1, 4, 3]
def baseStart_4216073 : Nat := 118140960795 + 4216073 * 2 ^ 59
def prefixEnd_4216073 : Nat := 4983230072969 + 3 ^ 40 * 4216073 * 2
def baseEnd_4216073 : Nat := 2164871923443388328698139

theorem tailTrace_4216073 : CollatzResearch.WordTrace tailWord_4216073 prefixEnd_4216073 2164871923443388328698139 := by
  unfold tailWord_4216073
  simp only [CollatzResearch.WordTrace]
  refine ⟨153772815254895043787564873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102515210169930029191709915 153772815254895043787564873)
  ·
    refine ⟨115329611441171282840673655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153772815254895043787564873 115329611441171282840673655)
    ·
      refine ⟨172994417161756924261010483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115329611441171282840673655 172994417161756924261010483)
      ·
        refine ⟨259491625742635386391515725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172994417161756924261010483 259491625742635386391515725)
        ·
          refine ⟨97309359653488269896818397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259491625742635386391515725 97309359653488269896818397)
          ·
            refine ⟨36491009870058101211306899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97309359653488269896818397 36491009870058101211306899)
            ·
              refine ⟨54736514805087151816960349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36491009870058101211306899 54736514805087151816960349)
              ·
                refine ⟨20526193051907681931360131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54736514805087151816960349 20526193051907681931360131)
                ·
                  refine ⟨30789289577861522897040197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20526193051907681931360131 30789289577861522897040197)
                  ·
                    refine ⟨5772991795849035543195037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30789289577861522897040197 5772991795849035543195037)
                    ·
                      refine ⟨2164871923443388328698139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5772991795849035543195037 2164871923443388328698139)
                      ·
                        rfl

theorem cell23_4216073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 4, 3].length) (baseStart_4216073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216073 prefixEnd_4216073 := by exact prefixLift 4216073
  have htrace : WordTrace (prefixWord ++ tailWord_4216073) baseStart_4216073 baseEnd_4216073 := by
    simpa [prefixWord, tailWord_4216073, baseEnd_4216073] using wordTrace_append hprefix tailTrace_4216073
  have hstable : (prefixWord ++ tailWord_4216073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216073).length < 2 ^ (prefixWord ++ tailWord_4216073).sum := by decide
  have hdescent : baseEnd_4216073 < baseStart_4216073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216090 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3]
def baseStart_4216090 : Nat := 118140960795 + 4216090 * 2 ^ 59
def prefixEnd_4216090 : Nat := 4983230072969 + 3 ^ 40 * 4216090 * 2
def baseEnd_4216090 : Nat := 2164880652614514762185561

theorem tailTrace_4216090 : CollatzResearch.WordTrace tailWord_4216090 prefixEnd_4216090 2164880652614514762185561 := by
  unfold tailWord_4216090
  simp only [CollatzResearch.WordTrace]
  refine ⟨38443358823958363922733431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102515623530555637127289149 38443358823958363922733431)
  ·
    refine ⟨57665038235937545884100147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38443358823958363922733431 57665038235937545884100147)
    ·
      refine ⟨86497557353906318826150221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57665038235937545884100147 86497557353906318826150221)
      ·
        refine ⟨32436584007714869559806333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86497557353906318826150221 32436584007714869559806333)
        ·
          refine ⟨12163719002893076084927375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32436584007714869559806333 12163719002893076084927375)
          ·
            refine ⟨18245578504339614127391063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12163719002893076084927375 18245578504339614127391063)
            ·
              refine ⟨27368367756509421191086595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18245578504339614127391063 27368367756509421191086595)
              ·
                refine ⟨41052551634764131786629893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27368367756509421191086595 41052551634764131786629893)
                ·
                  refine ⟨7697353431518274709993105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41052551634764131786629893 7697353431518274709993105)
                  ·
                    refine ⟨5773015073638706032494829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7697353431518274709993105 5773015073638706032494829)
                    ·
                      refine ⟨2164880652614514762185561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5773015073638706032494829 2164880652614514762185561)
                      ·
                        rfl

theorem cell23_4216090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_4216090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216090 prefixEnd_4216090 := by exact prefixLift 4216090
  have htrace : WordTrace (prefixWord ++ tailWord_4216090) baseStart_4216090 baseEnd_4216090 := by
    simpa [prefixWord, tailWord_4216090, baseEnd_4216090] using wordTrace_append hprefix tailTrace_4216090
  have hstable : (prefixWord ++ tailWord_4216090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216090).length < 2 ^ (prefixWord ++ tailWord_4216090).sum := by decide
  have hdescent : baseEnd_4216090 < baseStart_4216090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216120 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 5, 1, 3]
def baseStart_4216120 : Nat := 118140960795 + 4216120 * 2 ^ 59
def prefixEnd_4216120 : Nat := 4983230072969 + 3 ^ 40 * 4216120 * 2
def baseEnd_4216120 : Nat := 2164896057034149644810423

theorem tailTrace_4216120 : CollatzResearch.WordTrace tailWord_4216120 prefixEnd_4216120 2164896057034149644810423 := by
  unfold tailWord_4216120
  simp only [CollatzResearch.WordTrace]
  refine ⟨76887264742862385407262907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102516352990483180543017209 76887264742862385407262907)
  ·
    refine ⟨115330897114293578110894361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76887264742862385407262907 115330897114293578110894361)
    ·
      refine ⟨86498172835720183583170771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115330897114293578110894361 86498172835720183583170771)
      ·
        refine ⟨129747259253580275374756157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86498172835720183583170771 129747259253580275374756157)
        ·
          refine ⟨48655222220092603265533559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129747259253580275374756157 48655222220092603265533559)
          ·
            refine ⟨72982833330138904898300339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48655222220092603265533559 72982833330138904898300339)
            ·
              refine ⟨109474249995208357347450509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72982833330138904898300339 109474249995208357347450509)
              ·
                refine ⟨41052843748203134005293941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109474249995208357347450509 41052843748203134005293941)
                ·
                  refine ⟨3848704101394043812996307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41052843748203134005293941 3848704101394043812996307)
                  ·
                    refine ⟨5773056152091065719494461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3848704101394043812996307 5773056152091065719494461)
                    ·
                      refine ⟨2164896057034149644810423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5773056152091065719494461 2164896057034149644810423)
                      ·
                        rfl

theorem cell23_4216120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_4216120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216120 prefixEnd_4216120 := by exact prefixLift 4216120
  have htrace : WordTrace (prefixWord ++ tailWord_4216120) baseStart_4216120 baseEnd_4216120 := by
    simpa [prefixWord, tailWord_4216120, baseEnd_4216120] using wordTrace_append hprefix tailTrace_4216120
  have hstable : (prefixWord ++ tailWord_4216120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216120).length < 2 ^ (prefixWord ++ tailWord_4216120).sum := by decide
  have hdescent : baseEnd_4216120 < baseStart_4216120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216160 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 4]
def baseStart_4216160 : Nat := 118140960795 + 4216160 * 2 ^ 59
def prefixEnd_4216160 : Nat := 4983230072969 + 3 ^ 40 * 4216160 * 2
def baseEnd_4216160 : Nat := 2164916596260329488310239

theorem tailTrace_4216160 : CollatzResearch.WordTrace tailWord_4216160 prefixEnd_4216160 2164916596260329488310239 := by
  unfold tailWord_4216160
  simp only [CollatzResearch.WordTrace]
  refine ⟨76887994202789928822990967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102517325603719905097321289 76887994202789928822990967)
  ·
    refine ⟨115331991304184893234486451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76887994202789928822990967 115331991304184893234486451)
    ·
      refine ⟨172997986956277339851729677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115331991304184893234486451 172997986956277339851729677)
      ·
        refine ⟨64874245108604002444398629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172997986956277339851729677 64874245108604002444398629)
        ·
          refine ⟨12163920957863250458324743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64874245108604002444398629 12163920957863250458324743)
          ·
            refine ⟨18245881436794875687487115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12163920957863250458324743 18245881436794875687487115)
            ·
              refine ⟨27368822155192313531230673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18245881436794875687487115 27368822155192313531230673)
              ·
                refine ⟨20526616616394235148423005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27368822155192313531230673 20526616616394235148423005)
                ·
                  refine ⟨7697481231147838180658627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20526616616394235148423005 7697481231147838180658627)
                  ·
                    refine ⟨11546221846721757270987941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7697481231147838180658627 11546221846721757270987941)
                    ·
                      refine ⟨2164916596260329488310239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11546221846721757270987941 2164916596260329488310239)
                      ·
                        rfl

theorem cell23_4216160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_4216160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216160 prefixEnd_4216160 := by exact prefixLift 4216160
  have htrace : WordTrace (prefixWord ++ tailWord_4216160) baseStart_4216160 baseEnd_4216160 := by
    simpa [prefixWord, tailWord_4216160, baseEnd_4216160] using wordTrace_append hprefix tailTrace_4216160
  have hstable : (prefixWord ++ tailWord_4216160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216160).length < 2 ^ (prefixWord ++ tailWord_4216160).sum := by decide
  have hdescent : baseEnd_4216160 < baseStart_4216160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216177 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 5, 2, 2]
def baseStart_4216177 : Nat := 118140960795 + 4216177 * 2 ^ 59
def prefixEnd_4216177 : Nat := 4983230072969 + 3 ^ 40 * 4216177 * 2
def baseEnd_4216177 : Nat := 2164925325431455921797661

theorem tailTrace_4216177 : CollatzResearch.WordTrace tailWord_4216177 prefixEnd_4216177 2164925325431455921797661 := by
  unfold tailWord_4216177
  simp only [CollatzResearch.WordTrace]
  refine ⟨153776608446518269549350785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102517738964345513032900523 153776608446518269549350785)
  ·
    refine ⟨115332456334888702162013089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153776608446518269549350785 115332456334888702162013089)
    ·
      refine ⟨86499342251166526621509817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115332456334888702162013089 86499342251166526621509817)
      ·
        refine ⟨64874506688374894966132363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86499342251166526621509817 64874506688374894966132363)
        ·
          refine ⟨97311760032562342449198545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64874506688374894966132363 97311760032562342449198545)
          ·
            refine ⟨72983820024421756836898909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97311760032562342449198545 72983820024421756836898909)
            ·
              refine ⟨27368932509158158813837091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72983820024421756836898909 27368932509158158813837091)
              ·
                refine ⟨41053398763737238220755637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27368932509158158813837091 41053398763737238220755637)
                ·
                  refine ⟨3848756134100366083195841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41053398763737238220755637 3848756134100366083195841)
                  ·
                    refine ⟨2886567100575274562396881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3848756134100366083195841 2886567100575274562396881)
                    ·
                      refine ⟨2164925325431455921797661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2886567100575274562396881 2164925325431455921797661)
                      ·
                        rfl

theorem cell23_4216177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_4216177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216177 prefixEnd_4216177 := by exact prefixLift 4216177
  have htrace : WordTrace (prefixWord ++ tailWord_4216177) baseStart_4216177 baseEnd_4216177 := by
    simpa [prefixWord, tailWord_4216177, baseEnd_4216177] using wordTrace_append hprefix tailTrace_4216177
  have hstable : (prefixWord ++ tailWord_4216177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216177).length < 2 ^ (prefixWord ++ tailWord_4216177).sum := by decide
  have hdescent : baseEnd_4216177 < baseStart_4216177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216181 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_4216181 : Nat := 118140960795 + 4216181 * 2 ^ 59
def prefixEnd_4216181 : Nat := 4983230072969 + 3 ^ 40 * 4216181 * 2
def baseEnd_4216181 : Nat := 2164927379354073906147643

theorem tailTrace_4216181 : CollatzResearch.WordTrace tailWord_4216181 prefixEnd_4216181 2164927379354073906147643 := by
  unfold tailWord_4216181
  simp only [CollatzResearch.WordTrace]
  refine ⟨153776754338503778232496397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102517836225669185488330931 153776754338503778232496397)
  ·
    refine ⟨57666282876938916837186149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153776754338503778232496397 57666282876938916837186149)
    ·
      refine ⟨10812428039426046906972403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57666282876938916837186149 10812428039426046906972403)
      ·
        refine ⟨16218642059139070360458605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10812428039426046906972403 16218642059139070360458605)
        ·
          refine ⟨6081990772177151385171977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16218642059139070360458605 6081990772177151385171977)
          ·
            refine ⟨4561493079132863538878983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6081990772177151385171977 4561493079132863538878983)
            ·
              refine ⟨6842239618699295308318475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4561493079132863538878983 6842239618699295308318475)
              ·
                refine ⟨10263359428048942962477713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6842239618699295308318475 10263359428048942962477713)
                ·
                  refine ⟨7697519571036707221858285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10263359428048942962477713 7697519571036707221858285)
                  ·
                    refine ⟨2886569839138765208196857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7697519571036707221858285 2886569839138765208196857)
                    ·
                      refine ⟨2164927379354073906147643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2886569839138765208196857 2164927379354073906147643)
                      ·
                        rfl

theorem cell23_4216181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_4216181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216181 prefixEnd_4216181 := by exact prefixLift 4216181
  have htrace : WordTrace (prefixWord ++ tailWord_4216181) baseStart_4216181 baseEnd_4216181 := by
    simpa [prefixWord, tailWord_4216181, baseEnd_4216181] using wordTrace_append hprefix tailTrace_4216181
  have hstable : (prefixWord ++ tailWord_4216181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216181).length < 2 ^ (prefixWord ++ tailWord_4216181).sum := by decide
  have hdescent : baseEnd_4216181 < baseStart_4216181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216213 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 1, 9]
def baseStart_4216213 : Nat := 118140960795 + 4216213 * 2 ^ 59
def prefixEnd_4216213 : Nat := 4983230072969 + 3 ^ 40 * 4216213 * 2
def baseEnd_4216213 : Nat := 721647936911672593649165

theorem tailTrace_4216213 : CollatzResearch.WordTrace tailWord_4216213 prefixEnd_4216213 721647936911672593649165 := by
  unfold tailWord_4216213
  simp only [CollatzResearch.WordTrace]
  refine ⟨153777921474387847697661293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102518614316258565131774195 153777921474387847697661293)
  ·
    refine ⟨57666720552895442886622985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153777921474387847697661293 57666720552895442886622985)
    ·
      refine ⟨43250040414671582164967239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57666720552895442886622985 43250040414671582164967239)
      ·
        refine ⟨64875060622007373247450859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43250040414671582164967239 64875060622007373247450859)
        ·
          refine ⟨97312590933011059871176289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64875060622007373247450859 97312590933011059871176289)
          ·
            refine ⟨72984443199758294903382217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97312590933011059871176289 72984443199758294903382217)
            ·
              refine ⟨54738332399818721177536663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72984443199758294903382217 54738332399818721177536663)
              ·
                refine ⟨82107498599728081766304995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54738332399818721177536663 82107498599728081766304995)
                ·
                  refine ⟨123161247899592122649457493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82107498599728081766304995 123161247899592122649457493)
                  ·
                    refine ⟨721647936911672593649165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 123161247899592122649457493 721647936911672593649165)
                    ·
                      rfl

theorem cell23_4216213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_4216213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216213 prefixEnd_4216213 := by exact prefixLift 4216213
  have htrace : WordTrace (prefixWord ++ tailWord_4216213) baseStart_4216213 baseEnd_4216213 := by
    simpa [prefixWord, tailWord_4216213, baseEnd_4216213] using wordTrace_append hprefix tailTrace_4216213
  have hstable : (prefixWord ++ tailWord_4216213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216213).length < 2 ^ (prefixWord ++ tailWord_4216213).sum := by decide
  have hdescent : baseEnd_4216213 < baseStart_4216213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216243 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 1, 8]
def baseStart_4216243 : Nat := 118140960795 + 4216243 * 2 ^ 59
def prefixEnd_4216243 : Nat := 4983230072969 + 3 ^ 40 * 4216243 * 2
def baseEnd_4216243 : Nat := 721653071718217554524119

theorem tailTrace_4216243 : CollatzResearch.WordTrace tailWord_4216243 prefixEnd_4216243 721653071718217554524119 := by
  unfold tailWord_4216243
  simp only [CollatzResearch.WordTrace]
  refine ⟨153779015664279162821253383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102519343776186108547502255 153779015664279162821253383)
  ·
    refine ⟨230668523496418744231880075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153779015664279162821253383 230668523496418744231880075)
    ·
      refine ⟨346002785244628116347820113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230668523496418744231880075 346002785244628116347820113)
      ·
        refine ⟨259502088933471087260865085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346002785244628116347820113 259502088933471087260865085)
        ·
          refine ⟨97313283350051657722824407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259502088933471087260865085 97313283350051657722824407)
          ·
            refine ⟨145969925025077486584236611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97313283350051657722824407 145969925025077486584236611)
            ·
              refine ⟨218954887537616229876354917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145969925025077486584236611 218954887537616229876354917)
              ·
                refine ⟨41054041413303043101816547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218954887537616229876354917 41054041413303043101816547)
                ·
                  refine ⟨61581062119954564652724821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41054041413303043101816547 61581062119954564652724821)
                  ·
                    refine ⟨721653071718217554524119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61581062119954564652724821 721653071718217554524119)
                    ·
                      rfl

theorem cell23_4216243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 8].length) (baseStart_4216243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216243 prefixEnd_4216243 := by exact prefixLift 4216243
  have htrace : WordTrace (prefixWord ++ tailWord_4216243) baseStart_4216243 baseEnd_4216243 := by
    simpa [prefixWord, tailWord_4216243, baseEnd_4216243] using wordTrace_append hprefix tailTrace_4216243
  have hstable : (prefixWord ++ tailWord_4216243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216243).length < 2 ^ (prefixWord ++ tailWord_4216243).sum := by decide
  have hdescent : baseEnd_4216243 < baseStart_4216243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216278 : List Nat := [5, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_4216278 : Nat := 118140960795 + 4216278 * 2 ^ 59
def prefixEnd_4216278 : Nat := 4983230072969 + 3 ^ 40 * 4216278 * 2
def baseEnd_4216278 : Nat := 2164977186977560026634697

theorem tailTrace_4216278 : CollatzResearch.WordTrace tailWord_4216278 prefixEnd_4216278 2164977186977560026634697 := by
  unfold tailWord_4216278
  simp only [CollatzResearch.WordTrace]
  refine ⟨9611268263697022737423593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102520194812768242532518325 9611268263697022737423593)
  ·
    refine ⟨7208451197772767053067695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9611268263697022737423593 7208451197772767053067695)
    ·
      refine ⟨10812676796659150579601543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7208451197772767053067695 10812676796659150579601543)
      ·
        refine ⟨16219015194988725869402315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10812676796659150579601543 16219015194988725869402315)
        ·
          refine ⟨24328522792483088804103473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16219015194988725869402315 24328522792483088804103473)
          ·
            refine ⟨18246392094362316603077605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24328522792483088804103473 18246392094362316603077605)
            ·
              refine ⟨3421198517692934363077051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18246392094362316603077605 3421198517692934363077051)
              ·
                refine ⟨5131797776539401544615577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3421198517692934363077051 5131797776539401544615577)
                ·
                  refine ⟨3848848332404551158461683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5131797776539401544615577 3848848332404551158461683)
                  ·
                    refine ⟨5773272498606826737692525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3848848332404551158461683 5773272498606826737692525)
                    ·
                      refine ⟨2164977186977560026634697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5773272498606826737692525 2164977186977560026634697)
                      ·
                        rfl

theorem cell23_4216278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_4216278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216278 prefixEnd_4216278 := by exact prefixLift 4216278
  have htrace : WordTrace (prefixWord ++ tailWord_4216278) baseStart_4216278 baseEnd_4216278 := by
    simpa [prefixWord, tailWord_4216278, baseEnd_4216278] using wordTrace_append hprefix tailTrace_4216278
  have hstable : (prefixWord ++ tailWord_4216278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216278).length < 2 ^ (prefixWord ++ tailWord_4216278).sum := by decide
  have hdescent : baseEnd_4216278 < baseStart_4216278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216280 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_4216280 : Nat := 118140960795 + 4216280 * 2 ^ 59
def prefixEnd_4216280 : Nat := 4983230072969 + 3 ^ 40 * 4216280 * 2
def baseEnd_4216280 : Nat := 2164978213938869018809687

theorem tailTrace_4216280 : CollatzResearch.WordTrace tailWord_4216280 prefixEnd_4216280 2164978213938869018809687 := by
  unfold tailWord_4216280
  simp only [CollatzResearch.WordTrace]
  refine ⟨76890182582572559070175147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102520243443430078760233529 76890182582572559070175147)
  ·
    refine ⟨115335273873858838605262721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76890182582572559070175147 115335273873858838605262721)
    ·
      refine ⟨86501455405394128953947041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115335273873858838605262721 86501455405394128953947041)
      ·
        refine ⟨64876091554045596715460281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86501455405394128953947041 64876091554045596715460281)
        ·
          refine ⟨48657068665534197536595211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64876091554045596715460281 48657068665534197536595211)
          ·
            refine ⟨72985602998301296304892817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48657068665534197536595211 72985602998301296304892817)
            ·
              refine ⟨54739202248725972228669613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72985602998301296304892817 54739202248725972228669613)
              ·
                refine ⟨20527200843272239585751105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54739202248725972228669613 20527200843272239585751105)
                ·
                  refine ⟨15395400632454179689313329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20527200843272239585751105 15395400632454179689313329)
                  ·
                    refine ⟨11546550474340634766984997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15395400632454179689313329 11546550474340634766984997)
                    ·
                      refine ⟨2164978213938869018809687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11546550474340634766984997 2164978213938869018809687)
                      ·
                        rfl

theorem cell23_4216280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_4216280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216280 prefixEnd_4216280 := by exact prefixLift 4216280
  have htrace : WordTrace (prefixWord ++ tailWord_4216280) baseStart_4216280 baseEnd_4216280 := by
    simpa [prefixWord, tailWord_4216280, baseEnd_4216280] using wordTrace_append hprefix tailTrace_4216280
  have hstable : (prefixWord ++ tailWord_4216280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216280).length < 2 ^ (prefixWord ++ tailWord_4216280).sum := by decide
  have hdescent : baseEnd_4216280 < baseStart_4216280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216300 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 3]
def baseStart_4216300 : Nat := 118140960795 + 4216300 * 2 ^ 59
def prefixEnd_4216300 : Nat := 4983230072969 + 3 ^ 40 * 4216300 * 2
def baseEnd_4216300 : Nat := 2164988483551958940559595

theorem tailTrace_4216300 : CollatzResearch.WordTrace tailWord_4216300 prefixEnd_4216300 2164988483551958940559595 := by
  unfold tailWord_4216300
  simp only [CollatzResearch.WordTrace]
  refine ⟨76890547312536330778039177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102520729750048441037385569 76890547312536330778039177)
  ·
    refine ⟨57667910484402248083529383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76890547312536330778039177 57667910484402248083529383)
    ·
      refine ⟨86501865726603372125294075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57667910484402248083529383 86501865726603372125294075)
      ·
        refine ⟨129752798589905058187941113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86501865726603372125294075 129752798589905058187941113)
        ·
          refine ⟨97314598942428793640955835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129752798589905058187941113 97314598942428793640955835)
          ·
            refine ⟨145971898413643190461433753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97314598942428793640955835 145971898413643190461433753)
            ·
              refine ⟨109478923810232392846075315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145971898413643190461433753 109478923810232392846075315)
              ·
                refine ⟨164218385715348589269112973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109478923810232392846075315 164218385715348589269112973)
                ·
                  refine ⟨61581894643255720975917365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164218385715348589269112973 61581894643255720975917365)
                  ·
                    refine ⟨5773302622805223841492253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61581894643255720975917365 5773302622805223841492253)
                    ·
                      refine ⟨2164988483551958940559595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5773302622805223841492253 2164988483551958940559595)
                      ·
                        rfl

theorem cell23_4216300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_4216300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216300 prefixEnd_4216300 := by exact prefixLift 4216300
  have htrace : WordTrace (prefixWord ++ tailWord_4216300) baseStart_4216300 baseEnd_4216300 := by
    simpa [prefixWord, tailWord_4216300, baseEnd_4216300] using wordTrace_append hprefix tailTrace_4216300
  have hstable : (prefixWord ++ tailWord_4216300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216300).length < 2 ^ (prefixWord ++ tailWord_4216300).sum := by decide
  have hdescent : baseEnd_4216300 < baseStart_4216300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216301 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_4216301 : Nat := 118140960795 + 4216301 * 2 ^ 59
def prefixEnd_4216301 : Nat := 4983230072969 + 3 ^ 40 * 4216301 * 2
def baseEnd_4216301 : Nat := 2164988997032613436647091

theorem tailTrace_4216301 : CollatzResearch.WordTrace tailWord_4216301 prefixEnd_4216301 2164988997032613436647091 := by
  unfold tailWord_4216301
  simp only [CollatzResearch.WordTrace]
  refine ⟨153781131098069038726864757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102520754065379359151243171 153781131098069038726864757)
  ·
    refine ⟨14416981040443972380643571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153781131098069038726864757 14416981040443972380643571)
    ·
      refine ⟨21625471560665958570965357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14416981040443972380643571 21625471560665958570965357)
      ·
        refine ⟨8109551835249734464112009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21625471560665958570965357 8109551835249734464112009)
        ·
          refine ⟨6082163876437300848084007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8109551835249734464112009 6082163876437300848084007)
          ·
            refine ⟨9123245814655951272126011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6082163876437300848084007 9123245814655951272126011)
            ·
              refine ⟨13684868721983926908189017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9123245814655951272126011 13684868721983926908189017)
              ·
                refine ⟨10263651541487945181141763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13684868721983926908189017 10263651541487945181141763)
                ·
                  refine ⟨15395477312231917771712645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10263651541487945181141763 15395477312231917771712645)
                  ·
                    refine ⟨2886651996043484582196121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15395477312231917771712645 2886651996043484582196121)
                    ·
                      refine ⟨2164988997032613436647091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2886651996043484582196121 2164988997032613436647091)
                      ·
                        rfl

theorem cell23_4216301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_4216301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216301 prefixEnd_4216301 := by exact prefixLift 4216301
  have htrace : WordTrace (prefixWord ++ tailWord_4216301) baseStart_4216301 baseEnd_4216301 := by
    simpa [prefixWord, tailWord_4216301, baseEnd_4216301] using wordTrace_append hprefix tailTrace_4216301
  have hstable : (prefixWord ++ tailWord_4216301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216301).length < 2 ^ (prefixWord ++ tailWord_4216301).sum := by decide
  have hdescent : baseEnd_4216301 < baseStart_4216301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216334 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_4216334 : Nat := 118140960795 + 4216334 * 2 ^ 59
def prefixEnd_4216334 : Nat := 4983230072969 + 3 ^ 40 * 4216334 * 2
def baseEnd_4216334 : Nat := 2165005941894211807534439

theorem tailTrace_4216334 : CollatzResearch.WordTrace tailWord_4216334 prefixEnd_4216334 2165005941894211807534439 := by
  unfold tailWord_4216334
  simp only [CollatzResearch.WordTrace]
  refine ⟨19222791838368685670352007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102521556471299656908544037 19222791838368685670352007)
  ·
    refine ⟨28834187757553028505528011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19222791838368685670352007 28834187757553028505528011)
    ·
      refine ⟨43251281636329542758292017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28834187757553028505528011 43251281636329542758292017)
      ·
        refine ⟨32438461227247157068719013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43251281636329542758292017 32438461227247157068719013)
        ·
          refine ⟨6082211480108841950384815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32438461227247157068719013 6082211480108841950384815)
          ·
            refine ⟨9123317220163262925577223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6082211480108841950384815 9123317220163262925577223)
            ·
              refine ⟨13684975830244894388365835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9123317220163262925577223 13684975830244894388365835)
              ·
                refine ⟨20527463745367341582548753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13684975830244894388365835 20527463745367341582548753)
                ·
                  refine ⟨15395597809025506186911565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20527463745367341582548753 15395597809025506186911565)
                  ·
                    refine ⟨5773349178384564820091837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15395597809025506186911565 5773349178384564820091837)
                    ·
                      refine ⟨2165005941894211807534439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5773349178384564820091837 2165005941894211807534439)
                      ·
                        rfl

theorem cell23_4216334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_4216334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216334 prefixEnd_4216334 := by exact prefixLift 4216334
  have htrace : WordTrace (prefixWord ++ tailWord_4216334) baseStart_4216334 baseEnd_4216334 := by
    simpa [prefixWord, tailWord_4216334, baseEnd_4216334] using wordTrace_append hprefix tailTrace_4216334
  have hstable : (prefixWord ++ tailWord_4216334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216334).length < 2 ^ (prefixWord ++ tailWord_4216334).sum := by decide
  have hdescent : baseEnd_4216334 < baseStart_4216334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216357 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 3, 6, 2]
def baseStart_4216357 : Nat := 118140960795 + 4216357 * 2 ^ 59
def prefixEnd_4216357 : Nat := 4983230072969 + 3 ^ 40 * 4216357 * 2
def baseEnd_4216357 : Nat := 2165017751949265217546833

theorem tailTrace_4216357 : CollatzResearch.WordTrace tailWord_4216357 prefixEnd_4216357 2165017751949265217546833 := by
  unfold tailWord_4216357
  simp only [CollatzResearch.WordTrace]
  refine ⟨153783173585866160290903325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102522115723910773527268883 153783173585866160290903325)
  ·
    refine ⟨57668690094699810109088747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153783173585866160290903325 57668690094699810109088747)
    ·
      refine ⟨86503035142049715163633121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57668690094699810109088747 86503035142049715163633121)
      ·
        refine ⟨64877276356537286372724841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86503035142049715163633121 64877276356537286372724841)
        ·
          refine ⟨48657957267402964779543631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64877276356537286372724841 48657957267402964779543631)
          ·
            refine ⟨72986935901104447169315447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48657957267402964779543631 72986935901104447169315447)
            ·
              refine ⟨109480403851656670753973171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72986935901104447169315447 109480403851656670753973171)
              ·
                refine ⟨164220605777485006130959757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109480403851656670753973171 164220605777485006130959757)
                ·
                  refine ⟨61582727166556877299109909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164220605777485006130959757 61582727166556877299109909)
                  ·
                    refine ⟨2886690335932353623395777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61582727166556877299109909 2886690335932353623395777)
                    ·
                      refine ⟨2165017751949265217546833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2886690335932353623395777 2165017751949265217546833)
                      ·
                        rfl

theorem cell23_4216357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_4216357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216357 prefixEnd_4216357 := by exact prefixLift 4216357
  have htrace : WordTrace (prefixWord ++ tailWord_4216357) baseStart_4216357 baseEnd_4216357 := by
    simpa [prefixWord, tailWord_4216357, baseEnd_4216357] using wordTrace_append hprefix tailTrace_4216357
  have hstable : (prefixWord ++ tailWord_4216357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216357).length < 2 ^ (prefixWord ++ tailWord_4216357).sum := by decide
  have hdescent : baseEnd_4216357 < baseStart_4216357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216400 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 6]
def baseStart_4216400 : Nat := 118140960795 + 4216400 * 2 ^ 59
def prefixEnd_4216400 : Nat := 4983230072969 + 3 ^ 40 * 4216400 * 2
def baseEnd_4216400 : Nat := 2165039831617408549309135

theorem tailTrace_4216400 : CollatzResearch.WordTrace tailWord_4216400 prefixEnd_4216400 2165039831617408549309135 := by
  unfold tailWord_4216400
  simp only [CollatzResearch.WordTrace]
  refine ⟨76892370962355189317359327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102523161283140252423145769 76892370962355189317359327)
  ·
    refine ⟨115338556443532783976038991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76892370962355189317359327 115338556443532783976038991)
    ·
      refine ⟨173007834665299175964058487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115338556443532783976038991 173007834665299175964058487)
      ·
        refine ⟨259511751997948763946087731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173007834665299175964058487 259511751997948763946087731)
        ·
          refine ⟨389267627996923145919131597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259511751997948763946087731 389267627996923145919131597)
          ·
            refine ⟨145975360498846179719674349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 389267627996923145919131597 145975360498846179719674349)
            ·
              refine ⟨54740760187067317394877881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145975360498846179719674349 54740760187067317394877881)
              ·
                refine ⟨41055570140300488046158411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54740760187067317394877881 41055570140300488046158411)
                ·
                  refine ⟨61583355210450732069237617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41055570140300488046158411 61583355210450732069237617)
                  ·
                    refine ⟨46187516407838049051928213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61583355210450732069237617 46187516407838049051928213)
                    ·
                      refine ⟨2165039831617408549309135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46187516407838049051928213 2165039831617408549309135)
                      ·
                        rfl

theorem cell23_4216400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_4216400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216400 prefixEnd_4216400 := by exact prefixLift 4216400
  have htrace : WordTrace (prefixWord ++ tailWord_4216400) baseStart_4216400 baseEnd_4216400 := by
    simpa [prefixWord, tailWord_4216400, baseEnd_4216400] using wordTrace_append hprefix tailTrace_4216400
  have hstable : (prefixWord ++ tailWord_4216400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216400).length < 2 ^ (prefixWord ++ tailWord_4216400).sum := by decide
  have hdescent : baseEnd_4216400 < baseStart_4216400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216410 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 2, 9]
def baseStart_4216410 : Nat := 118140960795 + 4216410 * 2 ^ 59
def prefixEnd_4216410 : Nat := 4983230072969 + 3 ^ 40 * 4216410 * 2
def baseEnd_4216410 : Nat := 721681655474651170061363

theorem tailTrace_4216410 : CollatzResearch.WordTrace tailWord_4216410 prefixEnd_4216410 721681655474651170061363 := by
  unfold tailWord_4216410
  simp only [CollatzResearch.WordTrace]
  refine ⟨38446276663668537585645671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102523404436449433561721789 38446276663668537585645671)
  ·
    refine ⟨57669414995502806378468507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38446276663668537585645671 57669414995502806378468507)
    ·
      refine ⟨86504122493254209567702761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57669414995502806378468507 86504122493254209567702761)
      ·
        refine ⟨64878091869940657175777071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86504122493254209567702761 64878091869940657175777071)
        ·
          refine ⟨97317137804910985763665607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64878091869940657175777071 97317137804910985763665607)
          ·
            refine ⟨145975706707366478645498411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97317137804910985763665607 145975706707366478645498411)
            ·
              refine ⟨218963560061049717968247617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145975706707366478645498411 218963560061049717968247617)
              ·
                refine ⟨164222670045787288476185713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218963560061049717968247617 164222670045787288476185713)
                ·
                  refine ⟨123167002534340466357139285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164222670045787288476185713 123167002534340466357139285)
                  ·
                    refine ⟨721681655474651170061363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 123167002534340466357139285 721681655474651170061363)
                    ·
                      rfl

theorem cell23_4216410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_4216410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216410 prefixEnd_4216410 := by exact prefixLift 4216410
  have htrace : WordTrace (prefixWord ++ tailWord_4216410) baseStart_4216410 baseEnd_4216410 := by
    simpa [prefixWord, tailWord_4216410, baseEnd_4216410] using wordTrace_append hprefix tailTrace_4216410
  have hstable : (prefixWord ++ tailWord_4216410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216410).length < 2 ^ (prefixWord ++ tailWord_4216410).sum := by decide
  have hdescent : baseEnd_4216410 < baseStart_4216410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216440 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 2, 10]
def baseStart_4216440 : Nat := 118140960795 + 4216440 * 2 ^ 59
def prefixEnd_4216440 : Nat := 4983230072969 + 3 ^ 40 * 4216440 * 2
def baseEnd_4216440 : Nat := 721686790281196130936317

theorem tailTrace_4216440 : CollatzResearch.WordTrace tailWord_4216440 prefixEnd_4216440 721686790281196130936317 := by
  unfold tailWord_4216440
  simp only [CollatzResearch.WordTrace]
  refine ⟨76893100422282732733087387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102524133896376976977449849 76893100422282732733087387)
  ·
    refine ⟨115339650633424099099631081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76893100422282732733087387 115339650633424099099631081)
    ·
      refine ⟨86504737975068074324723311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115339650633424099099631081 86504737975068074324723311)
      ·
        refine ⟨129757106962602111487084967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86504737975068074324723311 129757106962602111487084967)
        ·
          refine ⟨194635660443903167230627451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129757106962602111487084967 194635660443903167230627451)
          ·
            refine ⟨291953490665854750845941177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194635660443903167230627451 291953490665854750845941177)
            ·
              refine ⟨218965117999391063134455883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291953490665854750845941177 218965117999391063134455883)
              ·
                refine ⟨328447676999086594701683825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218965117999391063134455883 328447676999086594701683825)
                ·
                  refine ⟨246335757749314946026262869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328447676999086594701683825 246335757749314946026262869)
                  ·
                    refine ⟨721686790281196130936317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 246335757749314946026262869 721686790281196130936317)
                    ·
                      rfl

theorem cell23_4216440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_4216440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216440 prefixEnd_4216440 := by exact prefixLift 4216440
  have htrace : WordTrace (prefixWord ++ tailWord_4216440) baseStart_4216440 baseEnd_4216440 := by
    simpa [prefixWord, tailWord_4216440, baseEnd_4216440] using wordTrace_append hprefix tailTrace_4216440
  have hstable : (prefixWord ++ tailWord_4216440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216440).length < 2 ^ (prefixWord ++ tailWord_4216440).sum := by decide
  have hdescent : baseEnd_4216440 < baseStart_4216440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216478 : List Nat := [4, 3, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_4216478 : Nat := 118140960795 + 4216478 * 2 ^ 59
def prefixEnd_4216478 : Nat := 4983230072969 + 3 ^ 40 * 4216478 * 2
def baseEnd_4216478 : Nat := 721693294369486414711259

theorem tailTrace_4216478 : CollatzResearch.WordTrace tailWord_4216478 prefixEnd_4216478 721693294369486414711259 := by
  unfold tailWord_4216478
  simp only [CollatzResearch.WordTrace]
  refine ⟨19223448352303474744507261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102525057878951865304038725 19223448352303474744507261)
  ·
    refine ⟨7208793132113803029190223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19223448352303474744507261 7208793132113803029190223)
    ·
      refine ⟨10813189698170704543785335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7208793132113803029190223 10813189698170704543785335)
      ·
        refine ⟨16219784547256056815678003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10813189698170704543785335 16219784547256056815678003)
        ·
          refine ⟨24329676820884085223517005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16219784547256056815678003 24329676820884085223517005)
          ·
            refine ⟨9123628807831531958818877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24329676820884085223517005 9123628807831531958818877)
            ·
              refine ⟨3421360802936824484557079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9123628807831531958818877 3421360802936824484557079)
              ·
                refine ⟨5132041204405236726835619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3421360802936824484557079 5132041204405236726835619)
                ·
                  refine ⟨7698061806607855090253429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5132041204405236726835619 7698061806607855090253429)
                  ·
                    refine ⟨721693294369486414711259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7698061806607855090253429 721693294369486414711259)
                    ·
                      rfl

theorem cell23_4216478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_4216478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216478 prefixEnd_4216478 := by exact prefixLift 4216478
  have htrace : WordTrace (prefixWord ++ tailWord_4216478) baseStart_4216478 baseEnd_4216478 := by
    simpa [prefixWord, tailWord_4216478, baseEnd_4216478] using wordTrace_append hprefix tailTrace_4216478
  have hstable : (prefixWord ++ tailWord_4216478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216478).length < 2 ^ (prefixWord ++ tailWord_4216478).sum := by decide
  have hdescent : baseEnd_4216478 < baseStart_4216478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216484 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_4216484 : Nat := 118140960795 + 4216484 * 2 ^ 59
def prefixEnd_4216484 : Nat := 4983230072969 + 3 ^ 40 * 4216484 * 2
def baseEnd_4216484 : Nat := 2165082963992386220658749

theorem tailTrace_4216484 : CollatzResearch.WordTrace tailWord_4216484 prefixEnd_4216484 2165082963992386220658749 := by
  unfold tailWord_4216484
  simp only [CollatzResearch.WordTrace]
  refine ⟨76893902828203030490388253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102525203770937373987184337 76893902828203030490388253)
  ·
    refine ⟨28835213560576136433895595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76893902828203030490388253 28835213560576136433895595)
    ·
      refine ⟨43252820340864204650843393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28835213560576136433895595 43252820340864204650843393)
      ·
        refine ⟨32439615255648153488132545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43252820340864204650843393 32439615255648153488132545)
        ·
          refine ⟨24329711441736115116099409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32439615255648153488132545 24329711441736115116099409)
          ·
            refine ⟨18247283581302086337074557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24329711441736115116099409 18247283581302086337074557)
            ·
              refine ⟨6842731342988282376402959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18247283581302086337074557 6842731342988282376402959)
              ·
                refine ⟨10264097014482423564604439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6842731342988282376402959 10264097014482423564604439)
                ·
                  refine ⟨15396145521723635346906659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10264097014482423564604439 15396145521723635346906659)
                  ·
                    refine ⟨23094218282585453020359989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15396145521723635346906659 23094218282585453020359989)
                    ·
                      refine ⟨2165082963992386220658749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23094218282585453020359989 2165082963992386220658749)
                      ·
                        rfl

theorem cell23_4216484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_4216484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216484 prefixEnd_4216484 := by exact prefixLift 4216484
  have htrace : WordTrace (prefixWord ++ tailWord_4216484) baseStart_4216484 baseEnd_4216484 := by
    simpa [prefixWord, tailWord_4216484, baseEnd_4216484] using wordTrace_append hprefix tailTrace_4216484
  have hstable : (prefixWord ++ tailWord_4216484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216484).length < 2 ^ (prefixWord ++ tailWord_4216484).sum := by decide
  have hdescent : baseEnd_4216484 < baseStart_4216484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216532 : List Nat := [2, 4, 1, 3, 1, 2, 2, 3, 1, 2, 2]
def baseStart_4216532 : Nat := 118140960795 + 4216532 * 2 ^ 59
def prefixEnd_4216532 : Nat := 4983230072969 + 3 ^ 40 * 4216532 * 2
def baseEnd_4216532 : Nat := 2165107611063802032858529

theorem tailTrace_4216532 : CollatzResearch.WordTrace tailWord_4216532 prefixEnd_4216532 2165107611063802032858529 := by
  unfold tailWord_4216532
  simp only [CollatzResearch.WordTrace]
  refine ⟨76894778180116082589261925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102526370906821443452349233 76894778180116082589261925)
  ·
    refine ⟨14417770908771765485486611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76894778180116082589261925 14417770908771765485486611)
    ·
      refine ⟨21626656363157648228229917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14417770908771765485486611 21626656363157648228229917)
      ·
        refine ⟨8109996136184118085586219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21626656363157648228229917 8109996136184118085586219)
        ·
          refine ⟨12164994204276177128379329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8109996136184118085586219 12164994204276177128379329)
          ·
            refine ⟨9123745653207132846284497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12164994204276177128379329 9123745653207132846284497)
            ·
              refine ⟨6842809239905349634713373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9123745653207132846284497 6842809239905349634713373)
              ·
                refine ⟨2566053464964506113017515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6842809239905349634713373 2566053464964506113017515)
                ·
                  refine ⟨3849080197446759169526273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2566053464964506113017515 3849080197446759169526273)
                  ·
                    refine ⟨2886810148085069377144705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3849080197446759169526273 2886810148085069377144705)
                    ·
                      refine ⟨2165107611063802032858529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2886810148085069377144705 2165107611063802032858529)
                      ·
                        rfl

theorem cell23_4216532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_4216532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216532 prefixEnd_4216532 := by exact prefixLift 4216532
  have htrace : WordTrace (prefixWord ++ tailWord_4216532) baseStart_4216532 baseEnd_4216532 := by
    simpa [prefixWord, tailWord_4216532, baseEnd_4216532] using wordTrace_append hprefix tailTrace_4216532
  have hstable : (prefixWord ++ tailWord_4216532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216532).length < 2 ^ (prefixWord ++ tailWord_4216532).sum := by decide
  have hdescent : baseEnd_4216532 < baseStart_4216532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216622 : List Nat := [4, 1, 3, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_4216622 : Nat := 118140960795 + 4216622 * 2 ^ 59
def prefixEnd_4216622 : Nat := 4983230072969 + 3 ^ 40 * 4216622 * 2
def baseEnd_4216622 : Nat := 2165153824322706680733115

theorem tailTrace_4216622 : CollatzResearch.WordTrace tailWord_4216622 prefixEnd_4216622 2165153824322706680733115 := by
  unfold tailWord_4216622
  simp only [CollatzResearch.WordTrace]
  refine ⟨19224104866238263818662515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102528559286604073699533413 19224104866238263818662515)
  ·
    refine ⟨28836157299357395727993773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19224104866238263818662515 28836157299357395727993773)
    ·
      refine ⟨10813558987259023397997665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28836157299357395727993773 10813558987259023397997665)
      ·
        refine ⟨8110169240444267548498249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10813558987259023397997665 8110169240444267548498249)
        ·
          refine ⟨6082626930333200661373687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8110169240444267548498249 6082626930333200661373687)
          ·
            refine ⟨9123940395499800992060531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6082626930333200661373687 9123940395499800992060531)
            ·
              refine ⟨13685910593249701488090797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9123940395499800992060531 13685910593249701488090797)
              ·
                refine ⟨5132216472468638058034049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13685910593249701488090797 5132216472468638058034049)
                ·
                  refine ⟨3849162354351478543525537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5132216472468638058034049 3849162354351478543525537)
                  ·
                    refine ⟨2886871765763608907644153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3849162354351478543525537 2886871765763608907644153)
                    ·
                      refine ⟨2165153824322706680733115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2886871765763608907644153 2165153824322706680733115)
                      ·
                        rfl

theorem cell23_4216622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_4216622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216622 prefixEnd_4216622 := by exact prefixLift 4216622
  have htrace : WordTrace (prefixWord ++ tailWord_4216622) baseStart_4216622 baseEnd_4216622 := by
    simpa [prefixWord, tailWord_4216622, baseEnd_4216622] using wordTrace_append hprefix tailTrace_4216622
  have hstable : (prefixWord ++ tailWord_4216622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216622).length < 2 ^ (prefixWord ++ tailWord_4216622).sum := by decide
  have hdescent : baseEnd_4216622 < baseStart_4216622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216661 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_4216661 : Nat := 118140960795 + 4216661 * 2 ^ 59
def prefixEnd_4216661 : Nat := 4983230072969 + 3 ^ 40 * 4216661 * 2
def baseEnd_4216661 : Nat := 2165173850068232028145435

theorem tailTrace_4216661 : CollatzResearch.WordTrace tailWord_4216661 prefixEnd_4216661 2165173850068232028145435 := by
  unfold tailWord_4216661
  simp only [CollatzResearch.WordTrace]
  refine ⟨153794261376764820209969837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102529507584509880139979891 153794261376764820209969837)
  ·
    refine ⟨57672848016286807578738689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153794261376764820209969837 57672848016286807578738689)
    ·
      refine ⟨43254636012215105684054017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57672848016286807578738689 43254636012215105684054017)
      ·
        refine ⟨32440977009161329263040513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43254636012215105684054017 32440977009161329263040513)
        ·
          refine ⟨24330732756870996947280385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32440977009161329263040513 24330732756870996947280385)
          ·
            refine ⟨18248049567653247710460289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24330732756870996947280385 18248049567653247710460289)
            ·
              refine ⟨13686037175739935782845217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18248049567653247710460289 13686037175739935782845217)
              ·
                refine ⟨10264527881804951837133913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13686037175739935782845217 10264527881804951837133913)
                ·
                  refine ⟨7698395911353713877850435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10264527881804951837133913 7698395911353713877850435)
                  ·
                    refine ⟨11547593867030570816775653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7698395911353713877850435 11547593867030570816775653)
                    ·
                      refine ⟨2165173850068232028145435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11547593867030570816775653 2165173850068232028145435)
                      ·
                        rfl

theorem cell23_4216661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_4216661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216661 prefixEnd_4216661 := by exact prefixLift 4216661
  have htrace : WordTrace (prefixWord ++ tailWord_4216661) baseStart_4216661 baseEnd_4216661 := by
    simpa [prefixWord, tailWord_4216661, baseEnd_4216661] using wordTrace_append hprefix tailTrace_4216661
  have hstable : (prefixWord ++ tailWord_4216661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216661).length < 2 ^ (prefixWord ++ tailWord_4216661).sum := by decide
  have hdescent : baseEnd_4216661 < baseStart_4216661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216664 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 5, 4, 3]
def baseStart_4216664 : Nat := 118140960795 + 4216664 * 2 ^ 59
def prefixEnd_4216664 : Nat := 4983230072969 + 3 ^ 40 * 4216664 * 2
def baseEnd_4216664 : Nat := 2165175390510195516407921

theorem tailTrace_4216664 : CollatzResearch.WordTrace tailWord_4216664 prefixEnd_4216664 2165175390510195516407921 := by
  unfold tailWord_4216664
  simp only [CollatzResearch.WordTrace]
  refine ⟨76897185397876975861164523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102529580530502634481552697 76897185397876975861164523)
  ·
    refine ⟨115345778096815463791746785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76897185397876975861164523 115345778096815463791746785)
    ·
      refine ⟨86509333572611597843810089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115345778096815463791746785 86509333572611597843810089)
      ·
        refine ⟨64882000179458698382857567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86509333572611597843810089 64882000179458698382857567)
        ·
          refine ⟨97323000269188047574286351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64882000179458698382857567 97323000269188047574286351)
          ·
            refine ⟨145984500403782071361429527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97323000269188047574286351 145984500403782071361429527)
            ·
              refine ⟨218976750605673107042144291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145984500403782071361429527 218976750605673107042144291)
              ·
                refine ⟨328465125908509660563216437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218976750605673107042144291 328465125908509660563216437)
                ·
                  refine ⟨30793605553922780677801541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 328465125908509660563216437 30793605553922780677801541)
                  ·
                    refine ⟨5773801041360521377087789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30793605553922780677801541 5773801041360521377087789)
                    ·
                      refine ⟨2165175390510195516407921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5773801041360521377087789 2165175390510195516407921)
                      ·
                        rfl

theorem cell23_4216664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_4216664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216664 prefixEnd_4216664 := by exact prefixLift 4216664
  have htrace : WordTrace (prefixWord ++ tailWord_4216664) baseStart_4216664 baseEnd_4216664 := by
    simpa [prefixWord, tailWord_4216664, baseEnd_4216664] using wordTrace_append hprefix tailTrace_4216664
  have hstable : (prefixWord ++ tailWord_4216664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216664).length < 2 ^ (prefixWord ++ tailWord_4216664).sum := by decide
  have hdescent : baseEnd_4216664 < baseStart_4216664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216718 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 8]
def baseStart_4216718 : Nat := 118140960795 + 4216718 * 2 ^ 59
def prefixEnd_4216718 : Nat := 4983230072969 + 3 ^ 40 * 4216718 * 2
def baseEnd_4216718 : Nat := 240578124273948700570297

theorem tailTrace_4216718 : CollatzResearch.WordTrace tailWord_4216718 prefixEnd_4216718 240578124273948700570297 := by
  unfold tailWord_4216718
  simp only [CollatzResearch.WordTrace]
  refine ⟨19224542542194789868099351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102530893558372212629863205 19224542542194789868099351)
  ·
    refine ⟨28836813813292184802149027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19224542542194789868099351 28836813813292184802149027)
    ·
      refine ⟨43255220719938277203223541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28836813813292184802149027 43255220719938277203223541)
      ·
        refine ⟨4055176942494213487802207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43255220719938277203223541 4055176942494213487802207)
        ·
          refine ⟨6082765413741320231703311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4055176942494213487802207 6082765413741320231703311)
          ·
            refine ⟨9124148120611980347554967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6082765413741320231703311 9124148120611980347554967)
            ·
              refine ⟨13686222180917970521332451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9124148120611980347554967 13686222180917970521332451)
              ·
                refine ⟨20529333271376955781998677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13686222180917970521332451 20529333271376955781998677)
                ·
                  refine ⟨240578124273948700570297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20529333271376955781998677 240578124273948700570297)
                  ·
                    rfl

theorem cell23_4216718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_4216718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216718 prefixEnd_4216718 := by exact prefixLift 4216718
  have htrace : WordTrace (prefixWord ++ tailWord_4216718) baseStart_4216718 baseEnd_4216718 := by
    simpa [prefixWord, tailWord_4216718, baseEnd_4216718] using wordTrace_append hprefix tailTrace_4216718
  have hstable : (prefixWord ++ tailWord_4216718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216718).length < 2 ^ (prefixWord ++ tailWord_4216718).sum := by decide
  have hdescent : baseEnd_4216718 < baseStart_4216718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216751 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 2, 6, 2]
def baseStart_4216751 : Nat := 118140960795 + 4216751 * 2 ^ 59
def prefixEnd_4216751 : Nat := 4983230072969 + 3 ^ 40 * 4216751 * 2
def baseEnd_4216751 : Nat := 2165220063327136676020021

theorem tailTrace_4216751 : CollatzResearch.WordTrace tailWord_4216751 prefixEnd_4216751 2165220063327136676020021 := by
  unfold tailWord_4216751
  simp only [CollatzResearch.WordTrace]
  refine ⟨153797543946438765580746107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102531695964292510387164071 153797543946438765580746107)
  ·
    refine ⟨230696315919658148371119161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153797543946438765580746107 230696315919658148371119161)
    ·
      refine ⟨173022236939743611278339371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230696315919658148371119161 173022236939743611278339371)
      ·
        refine ⟨259533355409615416917509057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173022236939743611278339371 259533355409615416917509057)
        ·
          refine ⟨194650016557211562688131793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259533355409615416917509057 194650016557211562688131793)
          ·
            refine ⟨145987512417908672016098845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194650016557211562688131793 145987512417908672016098845)
            ·
              refine ⟨54745317156715752006037067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145987512417908672016098845 54745317156715752006037067)
              ·
                refine ⟨82117975735073628009055601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54745317156715752006037067 82117975735073628009055601)
                ·
                  refine ⟨61588481801305221006791701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82117975735073628009055601 61588481801305221006791701)
                  ·
                    refine ⟨2886960084436182234693361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61588481801305221006791701 2886960084436182234693361)
                    ·
                      refine ⟨2165220063327136676020021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2886960084436182234693361 2165220063327136676020021)
                      ·
                        rfl

theorem cell23_4216751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 6, 2].length) (baseStart_4216751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216751 prefixEnd_4216751 := by exact prefixLift 4216751
  have htrace : WordTrace (prefixWord ++ tailWord_4216751) baseStart_4216751 baseEnd_4216751 := by
    simpa [prefixWord, tailWord_4216751, baseEnd_4216751] using wordTrace_append hprefix tailTrace_4216751
  have hstable : (prefixWord ++ tailWord_4216751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216751).length < 2 ^ (prefixWord ++ tailWord_4216751).sum := by decide
  have hdescent : baseEnd_4216751 < baseStart_4216751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216756 : List Nat := [2, 5, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_4216756 : Nat := 118140960795 + 4216756 * 2 ^ 59
def prefixEnd_4216756 : Nat := 4983230072969 + 3 ^ 40 * 4216756 * 2
def baseEnd_4216756 : Nat := 721740876910136385485833

theorem tailTrace_4216756 : CollatzResearch.WordTrace tailWord_4216756 prefixEnd_4216756 721740876910136385485833 := by
  unfold tailWord_4216756
  simp only [CollatzResearch.WordTrace]
  refine ⟨76898863155710325717339061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102531817540947100956452081 76898863155710325717339061)
  ·
    refine ⟨7209268420847843036000537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76898863155710325717339061 7209268420847843036000537)
    ·
      refine ⟨5406951315635882277000403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7209268420847843036000537 5406951315635882277000403)
      ·
        refine ⟨8110426973453823415500605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5406951315635882277000403 8110426973453823415500605)
        ·
          refine ⟨3041410115045183780812727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8110426973453823415500605 3041410115045183780812727)
          ·
            refine ⟨4562115172567775671219091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3041410115045183780812727 4562115172567775671219091)
            ·
              refine ⟨6843172758851663506828637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4562115172567775671219091 6843172758851663506828637)
              ·
                refine ⟨2566189784569373815060739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6843172758851663506828637 2566189784569373815060739)
                ·
                  refine ⟨3849284676854060722591109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2566189784569373815060739 3849284676854060722591109)
                  ·
                    refine ⟨721740876910136385485833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3849284676854060722591109 721740876910136385485833)
                    ·
                      rfl

theorem cell23_4216756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_4216756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216756 prefixEnd_4216756 := by exact prefixLift 4216756
  have htrace : WordTrace (prefixWord ++ tailWord_4216756) baseStart_4216756 baseEnd_4216756 := by
    simpa [prefixWord, tailWord_4216756, baseEnd_4216756] using wordTrace_append hprefix tailTrace_4216756
  have hstable : (prefixWord ++ tailWord_4216756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216756).length < 2 ^ (prefixWord ++ tailWord_4216756).sum := by decide
  have hdescent : baseEnd_4216756 < baseStart_4216756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216761 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 6, 4]
def baseStart_4216761 : Nat := 118140960795 + 4216761 * 2 ^ 59
def prefixEnd_4216761 : Nat := 4983230072969 + 3 ^ 40 * 4216761 * 2
def baseEnd_4216761 : Nat := 721741732711227212298325

theorem tailTrace_4216761 : CollatzResearch.WordTrace tailWord_4216761 prefixEnd_4216761 721741732711227212298325 := by
  unfold tailWord_4216761
  simp only [CollatzResearch.WordTrace]
  refine ⟨153797908676402537288610137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102531939117601691525740091 153797908676402537288610137)
  ·
    refine ⟨115348431507301902966457603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153797908676402537288610137 115348431507301902966457603)
    ·
      refine ⟨173022647260952854449686405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115348431507301902966457603 173022647260952854449686405)
      ·
        refine ⟨32441746361428660209316201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173022647260952854449686405 32441746361428660209316201)
        ·
          refine ⟨24331309771071495156987151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32441746361428660209316201 24331309771071495156987151)
          ·
            refine ⟨36496964656607242735480727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24331309771071495156987151 36496964656607242735480727)
            ·
              refine ⟨54745446984910864103221091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36496964656607242735480727 54745446984910864103221091)
              ·
                refine ⟨82118170477366296154831637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54745446984910864103221091 82118170477366296154831637)
                ·
                  refine ⟨3849289241126545132257733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82118170477366296154831637 3849289241126545132257733)
                  ·
                    refine ⟨721741732711227212298325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3849289241126545132257733 721741732711227212298325)
                    ·
                      rfl

theorem cell23_4216761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 4].length) (baseStart_4216761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216761 prefixEnd_4216761 := by exact prefixLift 4216761
  have htrace : WordTrace (prefixWord ++ tailWord_4216761) baseStart_4216761 baseEnd_4216761 := by
    simpa [prefixWord, tailWord_4216761, baseEnd_4216761] using wordTrace_append hprefix tailTrace_4216761
  have hstable : (prefixWord ++ tailWord_4216761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216761).length < 2 ^ (prefixWord ++ tailWord_4216761).sum := by decide
  have hdescent : baseEnd_4216761 < baseStart_4216761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216788 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_4216788 : Nat := 118140960795 + 4216788 * 2 ^ 59
def prefixEnd_4216788 : Nat := 4983230072969 + 3 ^ 40 * 4216788 * 2
def baseEnd_4216788 : Nat := 2165239062111353031257351

theorem tailTrace_4216788 : CollatzResearch.WordTrace tailWord_4216788 prefixEnd_4216788 2165239062111353031257351 := by
  unfold tailWord_4216788
  simp only [CollatzResearch.WordTrace]
  refine ⟨76899446723652360449921509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102532595631536480599895345 76899446723652360449921509)
  ·
    refine ⟨14418646260684817584360283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76899446723652360449921509 14418646260684817584360283)
    ·
      refine ⟨21627969391027226376540425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14418646260684817584360283 21627969391027226376540425)
      ·
        refine ⟨16220977043270419782405319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21627969391027226376540425 16220977043270419782405319)
        ·
          refine ⟨24331465564905629673607979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16220977043270419782405319 24331465564905629673607979)
          ·
            refine ⟨36497198347358444510411969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24331465564905629673607979 36497198347358444510411969)
            ·
              refine ⟨27372898760518833382808977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36497198347358444510411969 27372898760518833382808977)
              ·
                refine ⟨20529674070389125037106733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27372898760518833382808977 20529674070389125037106733)
                ·
                  refine ⟨7698627776395921888915025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20529674070389125037106733 7698627776395921888915025)
                  ·
                    refine ⟨5773970832296941416686269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7698627776395921888915025 5773970832296941416686269)
                    ·
                      refine ⟨2165239062111353031257351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5773970832296941416686269 2165239062111353031257351)
                      ·
                        rfl

theorem cell23_4216788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_4216788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216788 prefixEnd_4216788 := by exact prefixLift 4216788
  have htrace : WordTrace (prefixWord ++ tailWord_4216788) baseStart_4216788 baseEnd_4216788 := by
    simpa [prefixWord, tailWord_4216788, baseEnd_4216788] using wordTrace_append hprefix tailTrace_4216788
  have hstable : (prefixWord ++ tailWord_4216788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216788).length < 2 ^ (prefixWord ++ tailWord_4216788).sum := by decide
  have hdescent : baseEnd_4216788 < baseStart_4216788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216822 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_4216822 : Nat := 118140960795 + 4216822 * 2 ^ 59
def prefixEnd_4216822 : Nat := 4983230072969 + 3 ^ 40 * 4216822 * 2
def baseEnd_4216822 : Nat := 2165256520453605898232195

theorem tailTrace_4216822 : CollatzResearch.WordTrace tailWord_4216822 prefixEnd_4216822 2165256520453605898232195 := by
  unfold tailWord_4216822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9612508345573846544161295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102533422352787696471053813 9612508345573846544161295)
  ·
    refine ⟨14418762518360769816241943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9612508345573846544161295 14418762518360769816241943)
    ·
      refine ⟨21628143777541154724362915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14418762518360769816241943 21628143777541154724362915)
      ·
        refine ⟨32442215666311732086544373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21628143777541154724362915 32442215666311732086544373)
        ·
          refine ⟨3041457718716724883113535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32442215666311732086544373 3041457718716724883113535)
          ·
            refine ⟨4562186578075087324670303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3041457718716724883113535 4562186578075087324670303)
            ·
              refine ⟨6843279867112630987005455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4562186578075087324670303 6843279867112630987005455)
              ·
                refine ⟨10264919800668946480508183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6843279867112630987005455 10264919800668946480508183)
                ·
                  refine ⟨15397379701003419720762275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10264919800668946480508183 15397379701003419720762275)
                  ·
                    refine ⟨23096069551505129581143413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15397379701003419720762275 23096069551505129581143413)
                    ·
                      refine ⟨2165256520453605898232195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23096069551505129581143413 2165256520453605898232195)
                      ·
                        rfl

theorem cell23_4216822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_4216822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216822 prefixEnd_4216822 := by exact prefixLift 4216822
  have htrace : WordTrace (prefixWord ++ tailWord_4216822) baseStart_4216822 baseEnd_4216822 := by
    simpa [prefixWord, tailWord_4216822, baseEnd_4216822] using wordTrace_append hprefix tailTrace_4216822
  have hstable : (prefixWord ++ tailWord_4216822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216822).length < 2 ^ (prefixWord ++ tailWord_4216822).sum := by decide
  have hdescent : baseEnd_4216822 < baseStart_4216822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216836 : List Nat := [2, 3, 2, 4, 1, 1, 1, 4, 1, 2, 2]
def baseStart_4216836 : Nat := 118140960795 + 4216836 * 2 ^ 59
def prefixEnd_4216836 : Nat := 4983230072969 + 3 ^ 40 * 4216836 * 2
def baseEnd_4216836 : Nat := 2165263709182768843457131

theorem tailTrace_4216836 : CollatzResearch.WordTrace tailWord_4216836 prefixEnd_4216836 2165263709182768843457131 := by
  unfold tailWord_4216836
  simp only [CollatzResearch.WordTrace]
  refine ⟨76900322075565412548795181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102533762767420550065060241 76900322075565412548795181)
  ·
    refine ⟨28837620778337029705798193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76900322075565412548795181 28837620778337029705798193)
    ·
      refine ⟨21628215583752772279348645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28837620778337029705798193 21628215583752772279348645)
      ·
        refine ⟨4055290421953644802377871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21628215583752772279348645 4055290421953644802377871)
        ·
          refine ⟨6082935632930467203566807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4055290421953644802377871 6082935632930467203566807)
          ·
            refine ⟨9124403449395700805350211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6082935632930467203566807 9124403449395700805350211)
            ·
              refine ⟨13686605174093551208025317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9124403449395700805350211 13686605174093551208025317)
              ·
                refine ⟨2566238470142540851504747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13686605174093551208025317 2566238470142540851504747)
                ·
                  refine ⟨3849357705213811277257121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2566238470142540851504747 3849357705213811277257121)
                  ·
                    refine ⟨2887018278910358457942841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3849357705213811277257121 2887018278910358457942841)
                    ·
                      refine ⟨2165263709182768843457131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887018278910358457942841 2165263709182768843457131)
                      ·
                        rfl

theorem cell23_4216836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_4216836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216836 prefixEnd_4216836 := by exact prefixLift 4216836
  have htrace : WordTrace (prefixWord ++ tailWord_4216836) baseStart_4216836 baseEnd_4216836 := by
    simpa [prefixWord, tailWord_4216836, baseEnd_4216836] using wordTrace_append hprefix tailTrace_4216836
  have hstable : (prefixWord ++ tailWord_4216836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216836).length < 2 ^ (prefixWord ++ tailWord_4216836).sum := by decide
  have hdescent : baseEnd_4216836 < baseStart_4216836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216891 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 3]
def baseStart_4216891 : Nat := 118140960795 + 4216891 * 2 ^ 59
def prefixEnd_4216891 : Nat := 4983230072969 + 3 ^ 40 * 4216891 * 2
def baseEnd_4216891 : Nat := 2165291950618766128269377

theorem tailTrace_4216891 : CollatzResearch.WordTrace tailWord_4216891 prefixEnd_4216891 2165291950618766128269377 := by
  unfold tailWord_4216891
  simp only [CollatzResearch.WordTrace]
  refine ⟨153802650165931569490842527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102535100110621046327228351 153802650165931569490842527)
  ·
    refine ⟨230703975248897354236263791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153802650165931569490842527 230703975248897354236263791)
    ·
      refine ⟨346055962873346031354395687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230703975248897354236263791 346055962873346031354395687)
      ·
        refine ⟨519083944310019047031593531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346055962873346031354395687 519083944310019047031593531)
        ·
          refine ⟨778625916465028570547390297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519083944310019047031593531 778625916465028570547390297)
          ·
            refine ⟨583969437348771427910542723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 778625916465028570547390297 583969437348771427910542723)
            ·
              refine ⟨875954156023157141865814085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583969437348771427910542723 875954156023157141865814085)
              ·
                refine ⟨164241404254341964099840141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 875954156023157141865814085 164241404254341964099840141)
                ·
                  refine ⟨61590526595378236537440053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164241404254341964099840141 61590526595378236537440053)
                  ·
                    refine ⟨5774111868316709675385005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61590526595378236537440053 5774111868316709675385005)
                    ·
                      refine ⟨2165291950618766128269377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5774111868316709675385005 2165291950618766128269377)
                      ·
                        rfl

theorem cell23_4216891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 3].length) (baseStart_4216891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216891 prefixEnd_4216891 := by exact prefixLift 4216891
  have htrace : WordTrace (prefixWord ++ tailWord_4216891) baseStart_4216891 baseEnd_4216891 := by
    simpa [prefixWord, tailWord_4216891, baseEnd_4216891] using wordTrace_append hprefix tailTrace_4216891
  have hstable : (prefixWord ++ tailWord_4216891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216891).length < 2 ^ (prefixWord ++ tailWord_4216891).sum := by decide
  have hdescent : baseEnd_4216891 < baseStart_4216891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216908 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 2, 3, 3]
def baseStart_4216908 : Nat := 118140960795 + 4216908 * 2 ^ 59
def prefixEnd_4216908 : Nat := 4983230072969 + 3 ^ 40 * 4216908 * 2
def baseEnd_4216908 : Nat := 2165300679789892561756799

theorem tailTrace_4216908 : CollatzResearch.WordTrace tailWord_4216908 prefixEnd_4216908 2165300679789892561756799 := by
  unfold tailWord_4216908
  simp only [CollatzResearch.WordTrace]
  refine ⟨76901635103434990697105689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102535513471246654262807585 76901635103434990697105689)
  ·
    refine ⟨57676226327576243022829267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76901635103434990697105689 57676226327576243022829267)
    ·
      refine ⟨86514339491364364534243901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57676226327576243022829267 86514339491364364534243901)
      ·
        refine ⟨32442877309261636700341463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86514339491364364534243901 32442877309261636700341463)
        ·
          refine ⟨48664315963892455050512195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32442877309261636700341463 48664315963892455050512195)
          ·
            refine ⟨72996473945838682575768293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48664315963892455050512195 72996473945838682575768293)
            ·
              refine ⟨13686838864844752982956555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72996473945838682575768293 13686838864844752982956555)
              ·
                refine ⟨20530258297267129474434833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13686838864844752982956555 20530258297267129474434833)
                ·
                  refine ⟨15397693722950347105826125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20530258297267129474434833 15397693722950347105826125)
                  ·
                    refine ⟨5774135146106380164684797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15397693722950347105826125 5774135146106380164684797)
                    ·
                      refine ⟨2165300679789892561756799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5774135146106380164684797 2165300679789892561756799)
                      ·
                        rfl

theorem cell23_4216908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_4216908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216908 prefixEnd_4216908 := by exact prefixLift 4216908
  have htrace : WordTrace (prefixWord ++ tailWord_4216908) baseStart_4216908 baseEnd_4216908 := by
    simpa [prefixWord, tailWord_4216908, baseEnd_4216908] using wordTrace_append hprefix tailTrace_4216908
  have hstable : (prefixWord ++ tailWord_4216908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216908).length < 2 ^ (prefixWord ++ tailWord_4216908).sum := by decide
  have hdescent : baseEnd_4216908 < baseStart_4216908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4216911 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 4, 5]
def baseStart_4216911 : Nat := 118140960795 + 4216911 * 2 ^ 59
def prefixEnd_4216911 : Nat := 4983230072969 + 3 ^ 40 * 4216911 * 2
def baseEnd_4216911 : Nat := 721767406743952016673095

theorem tailTrace_4216911 : CollatzResearch.WordTrace tailWord_4216911 prefixEnd_4216911 721767406743952016673095 := by
  unfold tailWord_4216911
  simp only [CollatzResearch.WordTrace]
  refine ⟨153803379625859112906570587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102535586417239408604380391 153803379625859112906570587)
  ·
    refine ⟨230705069438788669359855881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153803379625859112906570587 230705069438788669359855881)
    ·
      refine ⟨173028802079091502019891911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230705069438788669359855881 173028802079091502019891911)
      ·
        refine ⟨259543203118637253029837867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173028802079091502019891911 259543203118637253029837867)
        ·
          refine ⟨389314804677955879544756801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259543203118637253029837867 389314804677955879544756801)
          ·
            refine ⟨291986103508466909658567601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389314804677955879544756801 291986103508466909658567601)
            ·
              refine ⟨218989577631350182243925701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291986103508466909658567601 218989577631350182243925701)
              ·
                refine ⟨41060545805878159170736069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218989577631350182243925701 41060545805878159170736069)
                ·
                  refine ⟨7698852338602154844513013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41060545805878159170736069 7698852338602154844513013)
                  ·
                    refine ⟨721767406743952016673095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7698852338602154844513013 721767406743952016673095)
                    ·
                      rfl

theorem cell23_4216911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 5].length) (baseStart_4216911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4216911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4216911 prefixEnd_4216911 := by exact prefixLift 4216911
  have htrace : WordTrace (prefixWord ++ tailWord_4216911) baseStart_4216911 baseEnd_4216911 := by
    simpa [prefixWord, tailWord_4216911, baseEnd_4216911] using wordTrace_append hprefix tailTrace_4216911
  have hstable : (prefixWord ++ tailWord_4216911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4216911).length < 2 ^ (prefixWord ++ tailWord_4216911).sum := by decide
  have hdescent : baseEnd_4216911 < baseStart_4216911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4216911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217005 : List Nat := [1, 5, 2, 1, 2, 1, 1, 4, 6]
def baseStart_4217005 : Nat := 118140960795 + 4217005 * 2 ^ 59
def prefixEnd_4217005 : Nat := 4983230072969 + 3 ^ 40 * 4217005 * 2
def baseEnd_4217005 : Nat := 240594498601486520249317

theorem tailTrace_4217005 : CollatzResearch.WordTrace tailWord_4217005 prefixEnd_4217005 240594498601486520249317 := by
  unfold tailWord_4217005
  simp only [CollatzResearch.WordTrace]
  refine ⟨153806808087518566960492469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102537872058345711306994979 153806808087518566960492469)
  ·
    refine ⟨14419388258204865652546169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153806808087518566960492469 14419388258204865652546169)
    ·
      refine ⟨10814541193653649239409627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14419388258204865652546169 10814541193653649239409627)
      ·
        refine ⟨16221811790480473859114441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10814541193653649239409627 16221811790480473859114441)
        ·
          refine ⟨12166358842860355394335831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16221811790480473859114441 12166358842860355394335831)
          ·
            refine ⟨18249538264290533091503747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12166358842860355394335831 18249538264290533091503747)
            ·
              refine ⟨27374307396435799637255621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18249538264290533091503747 27374307396435799637255621)
              ·
                refine ⟨5132682636831712431985429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27374307396435799637255621 5132682636831712431985429)
                ·
                  refine ⟨240594498601486520249317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5132682636831712431985429 240594498601486520249317)
                  ·
                    rfl

theorem cell23_4217005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_4217005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217005 prefixEnd_4217005 := by exact prefixLift 4217005
  have htrace : WordTrace (prefixWord ++ tailWord_4217005) baseStart_4217005 baseEnd_4217005 := by
    simpa [prefixWord, tailWord_4217005, baseEnd_4217005] using wordTrace_append hprefix tailTrace_4217005
  have hstable : (prefixWord ++ tailWord_4217005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217005).length < 2 ^ (prefixWord ++ tailWord_4217005).sum := by decide
  have hdescent : baseEnd_4217005 < baseStart_4217005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217009 : List Nat := [1, 2, 2, 5, 2, 1, 1, 4, 1, 4]
def baseStart_4217009 : Nat := 118140960795 + 4217009 * 2 ^ 59
def prefixEnd_4217009 : Nat := 4983230072969 + 3 ^ 40 * 4217009 * 2
def baseEnd_4217009 : Nat := 721784180445332222197945

theorem tailTrace_4217009 : CollatzResearch.WordTrace tailWord_4217009 prefixEnd_4217009 721784180445332222197945 := by
  unfold tailWord_4217009
  simp only [CollatzResearch.WordTrace]
  refine ⟨153806953979504075643638081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102537969319669383762425387 153806953979504075643638081)
  ·
    refine ⟨115355215484628056732728561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153806953979504075643638081 115355215484628056732728561)
    ·
      refine ⟨86516411613471042549546421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115355215484628056732728561 86516411613471042549546421)
      ·
        refine ⟨8110913588762910239019977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86516411613471042549546421 8110913588762910239019977)
        ·
          refine ⟨6083185191572182679264983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8110913588762910239019977 6083185191572182679264983)
          ·
            refine ⟨9124777787358274018897475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6083185191572182679264983 9124777787358274018897475)
            ·
              refine ⟨13687166681037411028346213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9124777787358274018897475 13687166681037411028346213)
              ·
                refine ⟨2566343752694514567814915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13687166681037411028346213 2566343752694514567814915)
                ·
                  refine ⟨3849515629041771851722373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2566343752694514567814915 3849515629041771851722373)
                  ·
                    refine ⟨721784180445332222197945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3849515629041771851722373 721784180445332222197945)
                    ·
                      rfl

theorem cell23_4217009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_4217009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217009 prefixEnd_4217009 := by exact prefixLift 4217009
  have htrace : WordTrace (prefixWord ++ tailWord_4217009) baseStart_4217009 baseEnd_4217009 := by
    simpa [prefixWord, tailWord_4217009, baseEnd_4217009] using wordTrace_append hprefix tailTrace_4217009
  have hstable : (prefixWord ++ tailWord_4217009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217009).length < 2 ^ (prefixWord ++ tailWord_4217009).sum := by decide
  have hdescent : baseEnd_4217009 < baseStart_4217009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217018 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 3, 5]
def baseStart_4217018 : Nat := 118140960795 + 4217018 * 2 ^ 59
def prefixEnd_4217018 : Nat := 4983230072969 + 3 ^ 40 * 4217018 * 2
def baseEnd_4217018 : Nat := 721785720887295710460431

theorem tailTrace_4217018 : CollatzResearch.WordTrace tailWord_4217018 prefixEnd_4217018 721785720887295710460431 := by
  unfold tailWord_4217018
  simp only [CollatzResearch.WordTrace]
  refine ⟨38451820559117867545178927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102538188157647646787143805 38451820559117867545178927)
  ·
    refine ⟨57677730838676801317768391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38451820559117867545178927 57677730838676801317768391)
    ·
      refine ⟨86516596258015201976652587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57677730838676801317768391 86516596258015201976652587)
      ·
        refine ⟨129774894387022802964978881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86516596258015201976652587 129774894387022802964978881)
        ·
          refine ⟨97331170790267102223734161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129774894387022802964978881 97331170790267102223734161)
          ·
            refine ⟨72998378092700326667800621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97331170790267102223734161 72998378092700326667800621)
            ·
              refine ⟨27374391784762622500425233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72998378092700326667800621 27374391784762622500425233)
              ·
                refine ⟨20530793838571966875318925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27374391784762622500425233 20530793838571966875318925)
                ·
                  refine ⟨7699047689464487578244597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20530793838571966875318925 7699047689464487578244597)
                  ·
                    refine ⟨721785720887295710460431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7699047689464487578244597 721785720887295710460431)
                    ·
                      rfl

theorem cell23_4217018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_4217018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217018 prefixEnd_4217018 := by exact prefixLift 4217018
  have htrace : WordTrace (prefixWord ++ tailWord_4217018) baseStart_4217018 baseEnd_4217018 := by
    simpa [prefixWord, tailWord_4217018, baseEnd_4217018] using wordTrace_append hprefix tailTrace_4217018
  have hstable : (prefixWord ++ tailWord_4217018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217018).length < 2 ^ (prefixWord ++ tailWord_4217018).sum := by decide
  have hdescent : baseEnd_4217018 < baseStart_4217018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217036 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 2, 2, 3]
def baseStart_4217036 : Nat := 118140960795 + 4217036 * 2 ^ 59
def prefixEnd_4217036 : Nat := 4983230072969 + 3 ^ 40 * 4217036 * 2
def baseEnd_4217036 : Nat := 2165366405313668060956211

theorem tailTrace_4217036 : CollatzResearch.WordTrace tailWord_4217036 prefixEnd_4217036 2165366405313668060956211 := by
  unfold tailWord_4217036
  simp only [CollatzResearch.WordTrace]
  refine ⟨76903969375203129627435481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102538625833604172836580641 76903969375203129627435481)
  ·
    refine ⟨57677977031402347220576611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76903969375203129627435481 57677977031402347220576611)
    ·
      refine ⟨86516965547103520830864917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57677977031402347220576611 86516965547103520830864917)
      ·
        refine ⟨4055482760020477538946793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86516965547103520830864917 4055482760020477538946793)
        ·
          refine ⟨3041612070015358154210095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4055482760020477538946793 3041612070015358154210095)
          ·
            refine ⟨4562418105023037231315143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3041612070015358154210095 4562418105023037231315143)
            ·
              refine ⟨6843627157534555846972715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4562418105023037231315143 6843627157534555846972715)
              ·
                refine ⟨10265440736301833770459073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6843627157534555846972715 10265440736301833770459073)
                ·
                  refine ⟨7699080552226375327844305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10265440736301833770459073 7699080552226375327844305)
                  ·
                    refine ⟨5774310414169781495883229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7699080552226375327844305 5774310414169781495883229)
                    ·
                      refine ⟨2165366405313668060956211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5774310414169781495883229 2165366405313668060956211)
                      ·
                        rfl

theorem cell23_4217036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_4217036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217036 prefixEnd_4217036 := by exact prefixLift 4217036
  have htrace : WordTrace (prefixWord ++ tailWord_4217036) baseStart_4217036 baseEnd_4217036 := by
    simpa [prefixWord, tailWord_4217036, baseEnd_4217036] using wordTrace_append hprefix tailTrace_4217036
  have hstable : (prefixWord ++ tailWord_4217036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217036).length < 2 ^ (prefixWord ++ tailWord_4217036).sum := by decide
  have hdescent : baseEnd_4217036 < baseStart_4217036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217042 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_4217042 : Nat := 118140960795 + 4217042 * 2 ^ 59
def prefixEnd_4217042 : Nat := 4983230072969 + 3 ^ 40 * 4217042 * 2
def baseEnd_4217042 : Nat := 2165369486197595037481183

theorem tailTrace_4217042 : CollatzResearch.WordTrace tailWord_4217042 prefixEnd_4217042 2165369486197595037481183 := by
  unfold tailWord_4217042
  simp only [CollatzResearch.WordTrace]
  refine ⟨38452039397096130569897345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102538771725589681519726253 38452039397096130569897345)
  ·
    refine ⟨28839029547822097927423009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38452039397096130569897345 28839029547822097927423009)
    ·
      refine ⟨21629272160866573445567257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28839029547822097927423009 21629272160866573445567257)
      ·
        refine ⟨16221954120649930084175443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21629272160866573445567257 16221954120649930084175443)
        ·
          refine ⟨24332931180974895126263165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16221954120649930084175443 24332931180974895126263165)
          ·
            refine ⟨9124849192865585672348687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24332931180974895126263165 9124849192865585672348687)
            ·
              refine ⟨13687273789298378508523031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9124849192865585672348687 13687273789298378508523031)
              ·
                refine ⟨20530910683947567762784547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13687273789298378508523031 20530910683947567762784547)
                ·
                  refine ⟨30796366025921351644176821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20530910683947567762784547 30796366025921351644176821)
                  ·
                    refine ⟨2887159314930126716641577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30796366025921351644176821 2887159314930126716641577)
                    ·
                      refine ⟨2165369486197595037481183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887159314930126716641577 2165369486197595037481183)
                      ·
                        rfl

theorem cell23_4217042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_4217042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217042 prefixEnd_4217042 := by exact prefixLift 4217042
  have htrace : WordTrace (prefixWord ++ tailWord_4217042) baseStart_4217042 baseEnd_4217042 := by
    simpa [prefixWord, tailWord_4217042, baseEnd_4217042] using wordTrace_append hprefix tailTrace_4217042
  have hstable : (prefixWord ++ tailWord_4217042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217042).length < 2 ^ (prefixWord ++ tailWord_4217042).sum := by decide
  have hdescent : baseEnd_4217042 < baseStart_4217042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217068 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_4217068 : Nat := 118140960795 + 4217068 * 2 ^ 59
def prefixEnd_4217068 : Nat := 4983230072969 + 3 ^ 40 * 4217068 * 2
def baseEnd_4217068 : Nat := 2165382836694611935756063

theorem tailTrace_4217068 : CollatzResearch.WordTrace tailWord_4217068 prefixEnd_4217068 2165382836694611935756063 := by
  unfold tailWord_4217068
  simp only [CollatzResearch.WordTrace]
  refine ⟨76904552943145164360017929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102539403924193552480023905 76904552943145164360017929)
  ·
    refine ⟨57678414707358873270013447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76904552943145164360017929 57678414707358873270013447)
    ·
      refine ⟨86517622061038309905020171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57678414707358873270013447 86517622061038309905020171)
      ·
        refine ⟨129776433091557464857530257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86517622061038309905020171 129776433091557464857530257)
        ·
          refine ⟨97332324818668098643147693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129776433091557464857530257 97332324818668098643147693)
          ·
            refine ⟨36499621807000536991180385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97332324818668098643147693 36499621807000536991180385)
            ·
              refine ⟨27374716355250402743385289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36499621807000536991180385 27374716355250402743385289)
              ·
                refine ⟨20531037266437802057538967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27374716355250402743385289 20531037266437802057538967)
                ·
                  refine ⟨30796555899656703086308451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20531037266437802057538967 30796555899656703086308451)
                  ·
                    refine ⟨46194833849485054629462677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30796555899656703086308451 46194833849485054629462677)
                    ·
                      refine ⟨2165382836694611935756063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46194833849485054629462677 2165382836694611935756063)
                      ·
                        rfl

theorem cell23_4217068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_4217068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217068 prefixEnd_4217068 := by exact prefixLift 4217068
  have htrace : WordTrace (prefixWord ++ tailWord_4217068) baseStart_4217068 baseEnd_4217068 := by
    simpa [prefixWord, tailWord_4217068, baseEnd_4217068] using wordTrace_append hprefix tailTrace_4217068
  have hstable : (prefixWord ++ tailWord_4217068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217068).length < 2 ^ (prefixWord ++ tailWord_4217068).sum := by decide
  have hdescent : baseEnd_4217068 < baseStart_4217068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217133 : List Nat := [1, 5, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_4217133 : Nat := 118140960795 + 4217133 * 2 ^ 59
def prefixEnd_4217133 : Nat := 4983230072969 + 3 ^ 40 * 4217133 * 2
def baseEnd_4217133 : Nat := 721805404312384727147755

theorem tailTrace_4217133 : CollatzResearch.WordTrace tailWord_4217133 prefixEnd_4217133 721805404312384727147755 := by
  unfold tailWord_4217133
  simp only [CollatzResearch.WordTrace]
  refine ⟨153811476631054844821152053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102540984420703229880768035 153811476631054844821152053)
  ·
    refine ⟨14419825934161391701983005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153811476631054844821152053 14419825934161391701983005)
    ·
      refine ⟨5407434725310521888243627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14419825934161391701983005 5407434725310521888243627)
      ·
        refine ⟨8111152087965782832365441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5407434725310521888243627 8111152087965782832365441)
        ·
          refine ⟨6083364065974337124274081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8111152087965782832365441 6083364065974337124274081)
          ·
            refine ⟨4562523049480752843205561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6083364065974337124274081 4562523049480752843205561)
            ·
              refine ⟨3421892287110564632404171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4562523049480752843205561 3421892287110564632404171)
              ·
                refine ⟨5132838430665846948606257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3421892287110564632404171 5132838430665846948606257)
                ·
                  refine ⟨3849628822999385211454693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5132838430665846948606257 3849628822999385211454693)
                  ·
                    refine ⟨721805404312384727147755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3849628822999385211454693 721805404312384727147755)
                    ·
                      rfl

theorem cell23_4217133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_4217133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217133 prefixEnd_4217133 := by exact prefixLift 4217133
  have htrace : WordTrace (prefixWord ++ tailWord_4217133) baseStart_4217133 baseEnd_4217133 := by
    simpa [prefixWord, tailWord_4217133, baseEnd_4217133] using wordTrace_append hprefix tailTrace_4217133
  have hstable : (prefixWord ++ tailWord_4217133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217133).length < 2 ^ (prefixWord ++ tailWord_4217133).sum := by decide
  have hdescent : baseEnd_4217133 < baseStart_4217133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217175 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_4217175 : Nat := 118140960795 + 4217175 * 2 ^ 59
def prefixEnd_4217175 : Nat := 4983230072969 + 3 ^ 40 * 4217175 * 2
def baseEnd_4217175 : Nat := 2165437779124643017118071

theorem tailTrace_4217175 : CollatzResearch.WordTrace tailWord_4217175 prefixEnd_4217175 2165437779124643017118071 := by
  unfold tailWord_4217175
  simp only [CollatzResearch.WordTrace]
  refine ⟨153813008496902685994180979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102542005664601790662787319 153813008496902685994180979)
  ·
    refine ⟨230719512745354028991271469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153813008496902685994180979 230719512745354028991271469)
    ·
      refine ⟨86519817279507760871726801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230719512745354028991271469 86519817279507760871726801)
      ·
        refine ⟨64889862959630820653795101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86519817279507760871726801 64889862959630820653795101)
        ·
          refine ⟨24333698609861557745173163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64889862959630820653795101 24333698609861557745173163)
          ·
            refine ⟨36500547914792336617759745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24333698609861557745173163 36500547914792336617759745)
            ·
              refine ⟨27375410936094252463319809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36500547914792336617759745 27375410936094252463319809)
              ·
                refine ⟨20531558202070689347489857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27375410936094252463319809 20531558202070689347489857)
                ·
                  refine ⟨15398668651553017010617393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20531558202070689347489857 15398668651553017010617393)
                  ·
                    refine ⟨11549001488664762757963045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15398668651553017010617393 11549001488664762757963045)
                    ·
                      refine ⟨2165437779124643017118071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11549001488664762757963045 2165437779124643017118071)
                      ·
                        rfl

theorem cell23_4217175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_4217175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217175 prefixEnd_4217175 := by exact prefixLift 4217175
  have htrace : WordTrace (prefixWord ++ tailWord_4217175) baseStart_4217175 baseEnd_4217175 := by
    simpa [prefixWord, tailWord_4217175, baseEnd_4217175] using wordTrace_append hprefix tailTrace_4217175
  have hstable : (prefixWord ++ tailWord_4217175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217175).length < 2 ^ (prefixWord ++ tailWord_4217175).sum := by decide
  have hdescent : baseEnd_4217175 < baseStart_4217175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217192 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_4217192 : Nat := 118140960795 + 4217192 * 2 ^ 59
def prefixEnd_4217192 : Nat := 4983230072969 + 3 ^ 40 * 4217192 * 2
def baseEnd_4217192 : Nat := 2165446508295769450605493

theorem tailTrace_4217192 : CollatzResearch.WordTrace tailWord_4217192 prefixEnd_4217192 2165446508295769450605493 := by
  unfold tailWord_4217192
  simp only [CollatzResearch.WordTrace]
  refine ⟨76906814268920548948774915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102542419025227398598366553 76906814268920548948774915)
  ·
    refine ⟨115360221403380823423162373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76906814268920548948774915 115360221403380823423162373)
    ·
      refine ⟨21630041513133904391842945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115360221403380823423162373 21630041513133904391842945)
      ·
        refine ⟨16222531134850428293882209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21630041513133904391842945 16222531134850428293882209)
        ·
          refine ⟨12166898351137821220411657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16222531134850428293882209 12166898351137821220411657)
          ·
            refine ⟨9125173763353365915308743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12166898351137821220411657 9125173763353365915308743)
            ·
              refine ⟨13687760645030048872963115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9125173763353365915308743 13687760645030048872963115)
              ·
                refine ⟨20531640967545073309444673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13687760645030048872963115 20531640967545073309444673)
                ·
                  refine ⟨15398730725658804982083505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20531640967545073309444673 15398730725658804982083505)
                  ·
                    refine ⟨11549048044244103736562629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15398730725658804982083505 11549048044244103736562629)
                    ·
                      refine ⟨2165446508295769450605493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11549048044244103736562629 2165446508295769450605493)
                      ·
                        rfl

theorem cell23_4217192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_4217192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217192 prefixEnd_4217192 := by exact prefixLift 4217192
  have htrace : WordTrace (prefixWord ++ tailWord_4217192) baseStart_4217192 baseEnd_4217192 := by
    simpa [prefixWord, tailWord_4217192, baseEnd_4217192] using wordTrace_append hprefix tailTrace_4217192
  have hstable : (prefixWord ++ tailWord_4217192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217192).length < 2 ^ (prefixWord ++ tailWord_4217192).sum := by decide
  have hdescent : baseEnd_4217192 < baseStart_4217192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217195 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 3]
def baseStart_4217195 : Nat := 118140960795 + 4217195 * 2 ^ 59
def prefixEnd_4217195 : Nat := 4983230072969 + 3 ^ 40 * 4217195 * 2
def baseEnd_4217195 : Nat := 2165448048737732938867979

theorem tailTrace_4217195 : CollatzResearch.WordTrace tailWord_4217195 prefixEnd_4217195 2165448048737732938867979 := by
  unfold tailWord_4217195
  simp only [CollatzResearch.WordTrace]
  refine ⟨153813737956830229409909039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102542491971220152939939359 153813737956830229409909039)
  ·
    refine ⟨230720606935245344114863559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153813737956830229409909039 230720606935245344114863559)
    ·
      refine ⟨346080910402868016172295339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230720606935245344114863559 346080910402868016172295339)
      ·
        refine ⟨519121365604302024258443009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346080910402868016172295339 519121365604302024258443009)
        ·
          refine ⟨389341024203226518193832257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 519121365604302024258443009 389341024203226518193832257)
          ·
            refine ⟨292005768152419888645374193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389341024203226518193832257 292005768152419888645374193)
            ·
              refine ⟨219004326114314916484030645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292005768152419888645374193 219004326114314916484030645)
              ·
                refine ⟨20531655573217023420377873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 219004326114314916484030645 20531655573217023420377873)
                ·
                  refine ⟨15398741679912767565283405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20531655573217023420377873 15398741679912767565283405)
                  ·
                    refine ⟨5774528129967287836981277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15398741679912767565283405 5774528129967287836981277)
                    ·
                      refine ⟨2165448048737732938867979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5774528129967287836981277 2165448048737732938867979)
                      ·
                        rfl

theorem cell23_4217195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 3].length) (baseStart_4217195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217195 prefixEnd_4217195 := by exact prefixLift 4217195
  have htrace : WordTrace (prefixWord ++ tailWord_4217195) baseStart_4217195 baseEnd_4217195 := by
    simpa [prefixWord, tailWord_4217195, baseEnd_4217195] using wordTrace_append hprefix tailTrace_4217195
  have hstable : (prefixWord ++ tailWord_4217195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217195).length < 2 ^ (prefixWord ++ tailWord_4217195).sum := by decide
  have hdescent : baseEnd_4217195 < baseStart_4217195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217219 : List Nat := [1, 1, 1, 3, 6, 1, 2, 3, 5]
def baseStart_4217219 : Nat := 118140960795 + 4217219 * 2 ^ 59
def prefixEnd_4217219 : Nat := 4983230072969 + 3 ^ 40 * 4217219 * 2
def baseEnd_4217219 : Nat := 240606708030382316107541

theorem tailTrace_4217219 : CollatzResearch.WordTrace tailWord_4217219 prefixEnd_4217219 240606708030382316107541 := by
  unfold tailWord_4217219
  simp only [CollatzResearch.WordTrace]
  refine ⟨153814613308743281508782711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102543075539162187672521807 153814613308743281508782711)
  ·
    refine ⟨230721919963114922263174067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153814613308743281508782711 230721919963114922263174067)
    ·
      refine ⟨346082879944672383394761101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230721919963114922263174067 346082879944672383394761101)
      ·
        refine ⟨129781079979252143773035413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346082879944672383394761101 129781079979252143773035413)
        ·
          refine ⟨6083488124027444239361035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 129781079979252143773035413 6083488124027444239361035)
          ·
            refine ⟨9125232186041166359041553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6083488124027444239361035 9125232186041166359041553)
            ·
              refine ⟨6843924139530874769281165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9125232186041166359041553 6843924139530874769281165)
              ·
                refine ⟨2566471552324078038480437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6843924139530874769281165 2566471552324078038480437)
                ·
                  refine ⟨240606708030382316107541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2566471552324078038480437 240606708030382316107541)
                  ·
                    rfl

theorem cell23_4217219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 5].length) (baseStart_4217219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217219 prefixEnd_4217219 := by exact prefixLift 4217219
  have htrace : WordTrace (prefixWord ++ tailWord_4217219) baseStart_4217219 baseEnd_4217219 := by
    simpa [prefixWord, tailWord_4217219, baseEnd_4217219] using wordTrace_append hprefix tailTrace_4217219
  have hstable : (prefixWord ++ tailWord_4217219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217219).length < 2 ^ (prefixWord ++ tailWord_4217219).sum := by decide
  have hdescent : baseEnd_4217219 < baseStart_4217219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217272 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 2, 2, 3]
def baseStart_4217272 : Nat := 118140960795 + 4217272 * 2 ^ 59
def prefixEnd_4217272 : Nat := 4983230072969 + 3 ^ 40 * 4217272 * 2
def baseEnd_4217272 : Nat := 2165487586748129137605125

theorem tailTrace_4217272 : CollatzResearch.WordTrace tailWord_4217272 prefixEnd_4217272 2165487586748129137605125 := by
  unfold tailWord_4217272
  simp only [CollatzResearch.WordTrace]
  refine ⟨76908273188775635780231035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102544364251700847706974713 76908273188775635780231035)
  ·
    refine ⟨115362409783163453670346553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76908273188775635780231035 115362409783163453670346553)
    ·
      refine ⟨86521807337372590252759915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115362409783163453670346553 86521807337372590252759915)
      ·
        refine ⟨129782711006058885379139873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86521807337372590252759915 129782711006058885379139873)
        ·
          refine ⟨97337033254544164034354905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129782711006058885379139873 97337033254544164034354905)
          ·
            refine ⟨73002774940908123025766179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97337033254544164034354905 73002774940908123025766179)
            ·
              refine ⟨109504162411362184538649269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73002774940908123025766179 109504162411362184538649269)
              ·
                refine ⟨10266015226065204800498369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109504162411362184538649269 10266015226065204800498369)
                ·
                  refine ⟨7699511419548903600373777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10266015226065204800498369 7699511419548903600373777)
                  ·
                    refine ⟨5774633564661677700280333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7699511419548903600373777 5774633564661677700280333)
                    ·
                      refine ⟨2165487586748129137605125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5774633564661677700280333 2165487586748129137605125)
                      ·
                        rfl

theorem cell23_4217272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_4217272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217272 prefixEnd_4217272 := by exact prefixLift 4217272
  have htrace : WordTrace (prefixWord ++ tailWord_4217272) baseStart_4217272 baseEnd_4217272 := by
    simpa [prefixWord, tailWord_4217272, baseEnd_4217272] using wordTrace_append hprefix tailTrace_4217272
  have hstable : (prefixWord ++ tailWord_4217272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217272).length < 2 ^ (prefixWord ++ tailWord_4217272).sum := by decide
  have hdescent : baseEnd_4217272 < baseStart_4217272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217319 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_4217319 : Nat := 118140960795 + 4217319 * 2 ^ 59
def prefixEnd_4217319 : Nat := 4983230072969 + 3 ^ 40 * 4217319 * 2
def baseEnd_4217319 : Nat := 2165511720338890453717409

theorem tailTrace_4217319 : CollatzResearch.WordTrace tailWord_4217319 prefixEnd_4217319 2165511720338890453717409 := by
  unfold tailWord_4217319
  simp only [CollatzResearch.WordTrace]
  refine ⟨153818260608380998587423011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102545507072253999058282007 153818260608380998587423011)
  ·
    refine ⟨230727390912571497881134517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153818260608380998587423011 230727390912571497881134517)
    ·
      refine ⟨21630692898053577926356361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 230727390912571497881134517 21630692898053577926356361)
      ·
        refine ⟨16223019673540183444767271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21630692898053577926356361 16223019673540183444767271)
        ·
          refine ⟨24334529510310275167150907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16223019673540183444767271 24334529510310275167150907)
          ·
            refine ⟨36501794265465412750726361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24334529510310275167150907 36501794265465412750726361)
            ·
              refine ⟨27376345699099059563044771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36501794265465412750726361 27376345699099059563044771)
              ·
                refine ⟨41064518548648589344567157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27376345699099059563044771 41064518548648589344567157)
                ·
                  refine ⟨3849798613935805251053171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41064518548648589344567157 3849798613935805251053171)
                  ·
                    refine ⟨5774697920903707876579757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3849798613935805251053171 5774697920903707876579757)
                    ·
                      refine ⟨2165511720338890453717409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5774697920903707876579757 2165511720338890453717409)
                      ·
                        rfl

theorem cell23_4217319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_4217319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217319 prefixEnd_4217319 := by exact prefixLift 4217319
  have htrace : WordTrace (prefixWord ++ tailWord_4217319) baseStart_4217319 baseEnd_4217319 := by
    simpa [prefixWord, tailWord_4217319, baseEnd_4217319] using wordTrace_append hprefix tailTrace_4217319
  have hstable : (prefixWord ++ tailWord_4217319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217319).length < 2 ^ (prefixWord ++ tailWord_4217319).sum := by decide
  have hdescent : baseEnd_4217319 < baseStart_4217319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217336 : List Nat := [2, 1, 2, 1, 1, 4, 2, 5, 1, 1, 3]
def baseStart_4217336 : Nat := 118140960795 + 4217336 * 2 ^ 59
def prefixEnd_4217336 : Nat := 4983230072969 + 3 ^ 40 * 4217336 * 2
def baseEnd_4217336 : Nat := 2165520449510016887204831

theorem tailTrace_4217336 : CollatzResearch.WordTrace tailWord_4217336 prefixEnd_4217336 2165520449510016887204831 := by
  unfold tailWord_4217336
  simp only [CollatzResearch.WordTrace]
  refine ⟨76909440324659705245395931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102545920432879606993861241 76909440324659705245395931)
  ·
    refine ⟨115364160486989557868093897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76909440324659705245395931 115364160486989557868093897)
    ·
      refine ⟨86523120365242168401070423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115364160486989557868093897 86523120365242168401070423)
      ·
        refine ⟨129784680547863252601605635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86523120365242168401070423 129784680547863252601605635)
        ·
          refine ⟨194677020821794878902408453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129784680547863252601605635 194677020821794878902408453)
          ·
            refine ⟨36501941404086539794201585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194677020821794878902408453 36501941404086539794201585)
            ·
              refine ⟨27376456053064904845651189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36501941404086539794201585 27376456053064904845651189)
              ·
                refine ⟨2566542754974834829279799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27376456053064904845651189 2566542754974834829279799)
                ·
                  refine ⟨3849814132462252243919699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2566542754974834829279799 3849814132462252243919699)
                  ·
                    refine ⟨5774721198693378365879549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3849814132462252243919699 5774721198693378365879549)
                    ·
                      refine ⟨2165520449510016887204831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5774721198693378365879549 2165520449510016887204831)
                      ·
                        rfl

theorem cell23_4217336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 1, 1, 3].length) (baseStart_4217336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217336 prefixEnd_4217336 := by exact prefixLift 4217336
  have htrace : WordTrace (prefixWord ++ tailWord_4217336) baseStart_4217336 baseEnd_4217336 := by
    simpa [prefixWord, tailWord_4217336, baseEnd_4217336] using wordTrace_append hprefix tailTrace_4217336
  have hstable : (prefixWord ++ tailWord_4217336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217336).length < 2 ^ (prefixWord ++ tailWord_4217336).sum := by decide
  have hdescent : baseEnd_4217336 < baseStart_4217336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217379 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 3]
def baseStart_4217379 : Nat := 118140960795 + 4217379 * 2 ^ 59
def prefixEnd_4217379 : Nat := 4983230072969 + 3 ^ 40 * 4217379 * 2
def baseEnd_4217379 : Nat := 2165542529178160218967133

theorem tailTrace_4217379 : CollatzResearch.WordTrace tailWord_4217379 prefixEnd_4217379 2165542529178160218967133 := by
  unfold tailWord_4217379
  simp only [CollatzResearch.WordTrace]
  refine ⟨153820448988163628834607191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102546965992109085889738127 153820448988163628834607191)
  ·
    refine ⟨230730673482245443251910787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153820448988163628834607191 230730673482245443251910787)
    ·
      refine ⟨346096010223368164877866181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230730673482245443251910787 346096010223368164877866181)
      ·
        refine ⟨64893001916881530914599909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 346096010223368164877866181 64893001916881530914599909)
        ·
          refine ⟨12167437859415287046487483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64893001916881530914599909 12167437859415287046487483)
          ·
            refine ⟨18251156789122930569731225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12167437859415287046487483 18251156789122930569731225)
            ·
              refine ⟨13688367591842197927298419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18251156789122930569731225 13688367591842197927298419)
              ·
                refine ⟨20532551387763296890947629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13688367591842197927298419 20532551387763296890947629)
                ·
                  refine ⟨7699706770411236334105361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20532551387763296890947629 7699706770411236334105361)
                  ·
                    refine ⟨5774780077808427250579021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7699706770411236334105361 5774780077808427250579021)
                    ·
                      refine ⟨2165542529178160218967133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5774780077808427250579021 2165542529178160218967133)
                      ·
                        rfl

theorem cell23_4217379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_4217379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217379 prefixEnd_4217379 := by exact prefixLift 4217379
  have htrace : WordTrace (prefixWord ++ tailWord_4217379) baseStart_4217379 baseEnd_4217379 := by
    simpa [prefixWord, tailWord_4217379, baseEnd_4217379] using wordTrace_append hprefix tailTrace_4217379
  have hstable : (prefixWord ++ tailWord_4217379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217379).length < 2 ^ (prefixWord ++ tailWord_4217379).sum := by decide
  have hdescent : baseEnd_4217379 < baseStart_4217379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217380 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 2, 3, 2]
def baseStart_4217380 : Nat := 118140960795 + 4217380 * 2 ^ 59
def prefixEnd_4217380 : Nat := 4983230072969 + 3 ^ 40 * 4217380 * 2
def baseEnd_4217380 : Nat := 2165543042658814715054629

theorem tailTrace_4217380 : CollatzResearch.WordTrace tailWord_4217380 prefixEnd_4217380 2165543042658814715054629 := by
  unfold tailWord_4217380
  simp only [CollatzResearch.WordTrace]
  refine ⟨76910242730580003002696797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102546990307440004003595729 76910242730580003002696797)
  ·
    refine ⟨28841341023967501126011299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76910242730580003002696797 28841341023967501126011299)
    ·
      refine ⟨43262011535951251689016949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28841341023967501126011299 43262011535951251689016949)
      ·
        refine ⟨4055813581495429845845339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43262011535951251689016949 4055813581495429845845339)
        ·
          refine ⟨6083720372243144768768009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4055813581495429845845339 6083720372243144768768009)
          ·
            refine ⟨4562790279182358576576007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6083720372243144768768009 4562790279182358576576007)
            ·
              refine ⟨6844185418773537864864011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4562790279182358576576007 6844185418773537864864011)
              ·
                refine ⟨10266278128160306797296017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6844185418773537864864011 10266278128160306797296017)
                ·
                  refine ⟨7699708596120230097972013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10266278128160306797296017 7699708596120230097972013)
                  ·
                    refine ⟨2887390723545086286739505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7699708596120230097972013 2887390723545086286739505)
                    ·
                      refine ⟨2165543042658814715054629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887390723545086286739505 2165543042658814715054629)
                      ·
                        rfl

theorem cell23_4217380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_4217380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217380 prefixEnd_4217380 := by exact prefixLift 4217380
  have htrace : WordTrace (prefixWord ++ tailWord_4217380) baseStart_4217380 baseEnd_4217380 := by
    simpa [prefixWord, tailWord_4217380, baseEnd_4217380] using wordTrace_append hprefix tailTrace_4217380
  have hstable : (prefixWord ++ tailWord_4217380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217380).length < 2 ^ (prefixWord ++ tailWord_4217380).sum := by decide
  have hdescent : baseEnd_4217380 < baseStart_4217380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217390 : List Nat := [4, 1, 3, 1, 4, 1, 2, 1, 1, 5]
def baseStart_4217390 : Nat := 118140960795 + 4217390 * 2 ^ 59
def prefixEnd_4217390 : Nat := 4983230072969 + 3 ^ 40 * 4217390 * 2
def baseEnd_4217390 : Nat := 721849392488453225309861

theorem tailTrace_4217390 : CollatzResearch.WordTrace tailWord_4217390 prefixEnd_4217390 721849392488453225309861 := by
  unfold tailWord_4217390
  simp only [CollatzResearch.WordTrace]
  refine ⟨19227606273890472214157203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102547233460749185142171749 19227606273890472214157203)
  ·
    refine ⟨28841409410835708321235805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19227606273890472214157203 28841409410835708321235805)
    ·
      refine ⟨10815528529063390620463427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28841409410835708321235805 10815528529063390620463427)
      ·
        refine ⟨16223292793595085930695141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10815528529063390620463427 16223292793595085930695141)
        ·
          refine ⟨3041867398799078612005339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16223292793595085930695141 3041867398799078612005339)
          ·
            refine ⟨4562801098198617918008009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3041867398799078612005339 4562801098198617918008009)
            ·
              refine ⟨3422100823648963438506007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4562801098198617918008009 3422100823648963438506007)
              ·
                refine ⟨5133151235473445157759011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3422100823648963438506007 5133151235473445157759011)
                ·
                  refine ⟨7699726853210167736638517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5133151235473445157759011 7699726853210167736638517)
                  ·
                    refine ⟨721849392488453225309861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7699726853210167736638517 721849392488453225309861)
                    ·
                      rfl

theorem cell23_4217390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_4217390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217390 prefixEnd_4217390 := by exact prefixLift 4217390
  have htrace : WordTrace (prefixWord ++ tailWord_4217390) baseStart_4217390 baseEnd_4217390 := by
    simpa [prefixWord, tailWord_4217390, baseEnd_4217390] using wordTrace_append hprefix tailTrace_4217390
  have hstable : (prefixWord ++ tailWord_4217390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217390).length < 2 ^ (prefixWord ++ tailWord_4217390).sum := by decide
  have hdescent : baseEnd_4217390 < baseStart_4217390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217393 : List Nat := [1, 2, 2, 3, 1, 1, 3, 5, 1, 2, 2]
def baseStart_4217393 : Nat := 118140960795 + 4217393 * 2 ^ 59
def prefixEnd_4217393 : Nat := 4983230072969 + 3 ^ 40 * 4217393 * 2
def baseEnd_4217393 : Nat := 2165549717907323164192069

theorem tailTrace_4217393 : CollatzResearch.WordTrace tailWord_4217393 prefixEnd_4217393 2165549717907323164192069 := by
  unfold tailWord_4217393
  simp only [CollatzResearch.WordTrace]
  refine ⟨153820959610112909225616833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102547306406741939483744555 153820959610112909225616833)
  ·
    refine ⟨115365719707584681919212625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153820959610112909225616833 115365719707584681919212625)
    ·
      refine ⟨86524289780688511439409469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115365719707584681919212625 86524289780688511439409469)
      ·
        refine ⟨32446608667758191789778551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86524289780688511439409469 32446608667758191789778551)
        ·
          refine ⟨48669913001637287684667827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32446608667758191789778551 48669913001637287684667827)
          ·
            refine ⟨73004869502455931527001741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48669913001637287684667827 73004869502455931527001741)
            ·
              refine ⟨27376826063420974322625653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73004869502455931527001741 27376826063420974322625653)
              ·
                refine ⟨2566577443445716342746155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27376826063420974322625653 2566577443445716342746155)
                ·
                  refine ⟨3849866165168574514119233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2566577443445716342746155 3849866165168574514119233)
                  ·
                    refine ⟨2887399623876430885589425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3849866165168574514119233 2887399623876430885589425)
                    ·
                      refine ⟨2165549717907323164192069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887399623876430885589425 2165549717907323164192069)
                      ·
                        rfl

theorem cell23_4217393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_4217393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217393 prefixEnd_4217393 := by exact prefixLift 4217393
  have htrace : WordTrace (prefixWord ++ tailWord_4217393) baseStart_4217393 baseEnd_4217393 := by
    simpa [prefixWord, tailWord_4217393, baseEnd_4217393] using wordTrace_append hprefix tailTrace_4217393
  have hstable : (prefixWord ++ tailWord_4217393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217393).length < 2 ^ (prefixWord ++ tailWord_4217393).sum := by decide
  have hdescent : baseEnd_4217393 < baseStart_4217393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217419 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 5, 3, 2]
def baseStart_4217419 : Nat := 118140960795 + 4217419 * 2 ^ 59
def prefixEnd_4217419 : Nat := 4983230072969 + 3 ^ 40 * 4217419 * 2
def baseEnd_4217419 : Nat := 2165563068404340062466949

theorem tailTrace_4217419 : CollatzResearch.WordTrace tailWord_4217419 prefixEnd_4217419 2165563068404340062466949 := by
  unfold tailWord_4217419
  simp only [CollatzResearch.WordTrace]
  refine ⟨153821907908018715666063311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102547938605345810444042207 153821907908018715666063311)
  ·
    refine ⟨230732861862028073499094967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153821907908018715666063311 230732861862028073499094967)
    ·
      refine ⟨346099292793042110248642451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230732861862028073499094967 346099292793042110248642451)
      ·
        refine ⟨519148939189563165372963677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346099292793042110248642451 519148939189563165372963677)
        ·
          refine ⟨194680852196086187014861379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 519148939189563165372963677 194680852196086187014861379)
          ·
            refine ⟨292021278294129280522292069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194680852196086187014861379 292021278294129280522292069)
            ·
              refine ⟨54753989680149240097929763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 292021278294129280522292069 54753989680149240097929763)
              ·
                refine ⟨82130984520223860146894645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54753989680149240097929763 82130984520223860146894645)
                ·
                  refine ⟨7699779798770986888771373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82130984520223860146894645 7699779798770986888771373)
                  ·
                    refine ⟨2887417424539120083289265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7699779798770986888771373 2887417424539120083289265)
                    ·
                      refine ⟨2165563068404340062466949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887417424539120083289265 2165563068404340062466949)
                      ·
                        rfl

theorem cell23_4217419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 3, 2].length) (baseStart_4217419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217419 prefixEnd_4217419 := by exact prefixLift 4217419
  have htrace : WordTrace (prefixWord ++ tailWord_4217419) baseStart_4217419 baseEnd_4217419 := by
    simpa [prefixWord, tailWord_4217419, baseEnd_4217419] using wordTrace_append hprefix tailTrace_4217419
  have hstable : (prefixWord ++ tailWord_4217419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217419).length < 2 ^ (prefixWord ++ tailWord_4217419).sum := by decide
  have hdescent : baseEnd_4217419 < baseStart_4217419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217432 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_4217432 : Nat := 118140960795 + 4217432 * 2 ^ 59
def prefixEnd_4217432 : Nat := 4983230072969 + 3 ^ 40 * 4217432 * 2
def baseEnd_4217432 : Nat := 2165569743652848511604389

theorem tailTrace_4217432 : CollatzResearch.WordTrace tailWord_4217432 prefixEnd_4217432 2165569743652848511604389 := by
  unfold tailWord_4217432
  simp only [CollatzResearch.WordTrace]
  refine ⟨76911191028485809443143275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102548254704647745924191033 76911191028485809443143275)
  ·
    refine ⟨115366786542728714164714913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76911191028485809443143275 115366786542728714164714913)
    ·
      refine ⟨86525089907046535623536185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115366786542728714164714913 86525089907046535623536185)
      ·
        refine ⟨64893817430284901717652139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86525089907046535623536185 64893817430284901717652139)
        ·
          refine ⟨97340726145427352576478209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64893817430284901717652139 97340726145427352576478209)
          ·
            refine ⟨73005544609070514432358657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97340726145427352576478209 73005544609070514432358657)
            ·
              refine ⟨54754158456802885824268993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73005544609070514432358657 54754158456802885824268993)
              ·
                refine ⟨41065618842602164368201745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54754158456802885824268993 41065618842602164368201745)
                ·
                  refine ⟨30799214131951623276151309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41065618842602164368201745 30799214131951623276151309)
                  ·
                    refine ⟨11549705299481858728556741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30799214131951623276151309 11549705299481858728556741)
                    ·
                      refine ⟨2165569743652848511604389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11549705299481858728556741 2165569743652848511604389)
                      ·
                        rfl

theorem cell23_4217432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_4217432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217432 prefixEnd_4217432 := by exact prefixLift 4217432
  have htrace : WordTrace (prefixWord ++ tailWord_4217432) baseStart_4217432 baseEnd_4217432 := by
    simpa [prefixWord, tailWord_4217432, baseEnd_4217432] using wordTrace_append hprefix tailTrace_4217432
  have hstable : (prefixWord ++ tailWord_4217432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217432).length < 2 ^ (prefixWord ++ tailWord_4217432).sum := by decide
  have hdescent : baseEnd_4217432 < baseStart_4217432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217449 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 3, 4, 2]
def baseStart_4217449 : Nat := 118140960795 + 4217449 * 2 ^ 59
def prefixEnd_4217449 : Nat := 4983230072969 + 3 ^ 40 * 4217449 * 2
def baseEnd_4217449 : Nat := 2165578472823974945091811

theorem tailTrace_4217449 : CollatzResearch.WordTrace tailWord_4217449 prefixEnd_4217449 2165578472823974945091811 := by
  unfold tailWord_4217449
  simp only [CollatzResearch.WordTrace]
  refine ⟨153823002097910030789655401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102548668065273353859770267 153823002097910030789655401)
  ·
    refine ⟨115367251573432523092241551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153823002097910030789655401 115367251573432523092241551)
    ·
      refine ⟨173050877360148784638362327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115367251573432523092241551 173050877360148784638362327)
      ·
        refine ⟨259576316040223176957543491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173050877360148784638362327 259576316040223176957543491)
        ·
          refine ⟨389364474060334765436315237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259576316040223176957543491 389364474060334765436315237)
          ·
            refine ⟨73005838886312768519309107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 389364474060334765436315237 73005838886312768519309107)
            ·
              refine ⟨109508758329469152778963661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73005838886312768519309107 109508758329469152778963661)
              ·
                refine ⟨41065784373550932292111373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109508758329469152778963661 41065784373550932292111373)
                ·
                  refine ⟨15399669140081599609541765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41065784373550932292111373 15399669140081599609541765)
                  ·
                    refine ⟨2887437963765299926789081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15399669140081599609541765 2887437963765299926789081)
                    ·
                      refine ⟨2165578472823974945091811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887437963765299926789081 2165578472823974945091811)
                      ·
                        rfl

theorem cell23_4217449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 4, 2].length) (baseStart_4217449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217449 prefixEnd_4217449 := by exact prefixLift 4217449
  have htrace : WordTrace (prefixWord ++ tailWord_4217449) baseStart_4217449 baseEnd_4217449 := by
    simpa [prefixWord, tailWord_4217449, baseEnd_4217449] using wordTrace_append hprefix tailTrace_4217449
  have hstable : (prefixWord ++ tailWord_4217449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217449).length < 2 ^ (prefixWord ++ tailWord_4217449).sum := by decide
  have hdescent : baseEnd_4217449 < baseStart_4217449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217452 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_4217452 : Nat := 118140960795 + 4217452 * 2 ^ 59
def prefixEnd_4217452 : Nat := 4983230072969 + 3 ^ 40 * 4217452 * 2
def baseEnd_4217452 : Nat := 2165580013265938433354297

theorem tailTrace_4217452 : CollatzResearch.WordTrace tailWord_4217452 prefixEnd_4217452 2165580013265938433354297 := by
  unfold tailWord_4217452
  simp only [CollatzResearch.WordTrace]
  refine ⟨76911555758449581151007305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102548741011266108201343073 76911555758449581151007305)
  ·
    refine ⟨57683666818837185863255479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76911555758449581151007305 57683666818837185863255479)
    ·
      refine ⟨86525500228255778794883219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57683666818837185863255479 86525500228255778794883219)
      ·
        refine ⟨129788250342383668192324829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86525500228255778794883219 129788250342383668192324829)
        ·
          refine ⟨48670593878393875572121811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129788250342383668192324829 48670593878393875572121811)
          ·
            refine ⟨73005890817590813358182717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48670593878393875572121811 73005890817590813358182717)
            ·
              refine ⟨27377209056596555009318519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73005890817590813358182717 27377209056596555009318519)
              ·
                refine ⟨41065813584894832513977779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27377209056596555009318519 41065813584894832513977779)
                ·
                  refine ⟨61598720377342248770966669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41065813584894832513977779 61598720377342248770966669)
                  ·
                    refine ⟨23099520141503343289112501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61598720377342248770966669 23099520141503343289112501)
                    ·
                      refine ⟨2165580013265938433354297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23099520141503343289112501 2165580013265938433354297)
                      ·
                        rfl

theorem cell23_4217452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_4217452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217452 prefixEnd_4217452 := by exact prefixLift 4217452
  have htrace : WordTrace (prefixWord ++ tailWord_4217452) baseStart_4217452 baseEnd_4217452 := by
    simpa [prefixWord, tailWord_4217452, baseEnd_4217452] using wordTrace_append hprefix tailTrace_4217452
  have hstable : (prefixWord ++ tailWord_4217452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217452).length < 2 ^ (prefixWord ++ tailWord_4217452).sum := by decide
  have hdescent : baseEnd_4217452 < baseStart_4217452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217453 : List Nat := [1, 5, 1, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_4217453 : Nat := 118140960795 + 4217453 * 2 ^ 59
def prefixEnd_4217453 : Nat := 4983230072969 + 3 ^ 40 * 4217453 * 2
def baseEnd_4217453 : Nat := 2165580526746592929441793

theorem tailTrace_4217453 : CollatzResearch.WordTrace tailWord_4217453 prefixEnd_4217453 2165580526746592929441793 := by
  unfold tailWord_4217453
  simp only [CollatzResearch.WordTrace]
  refine ⟨153823147989895539472801013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102548765326597026315200675 153823147989895539472801013)
  ·
    refine ⟨14420920124052706825575095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153823147989895539472801013 14420920124052706825575095)
    ·
      refine ⟨21631380186079060238362643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14420920124052706825575095 21631380186079060238362643)
      ·
        refine ⟨32447070279118590357543965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21631380186079060238362643 32447070279118590357543965)
        ·
          refine ⟨12167651354669471384078987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32447070279118590357543965 12167651354669471384078987)
          ·
            refine ⟨18251477032004207076118481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12167651354669471384078987 18251477032004207076118481)
            ·
              refine ⟨13688607774003155307088861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18251477032004207076118481 13688607774003155307088861)
              ·
                refine ⟨5133227915251183240158323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13688607774003155307088861 5133227915251183240158323)
                ·
                  refine ⟨7699841872876774860237485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5133227915251183240158323 7699841872876774860237485)
                  ·
                    refine ⟨2887440702328790572589057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7699841872876774860237485 2887440702328790572589057)
                    ·
                      refine ⟨2165580526746592929441793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887440702328790572589057 2165580526746592929441793)
                      ·
                        rfl

theorem cell23_4217453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_4217453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217453 prefixEnd_4217453 := by exact prefixLift 4217453
  have htrace : WordTrace (prefixWord ++ tailWord_4217453) baseStart_4217453 baseEnd_4217453 := by
    simpa [prefixWord, tailWord_4217453, baseEnd_4217453] using wordTrace_append hprefix tailTrace_4217453
  have hstable : (prefixWord ++ tailWord_4217453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217453).length < 2 ^ (prefixWord ++ tailWord_4217453).sum := by decide
  have hdescent : baseEnd_4217453 < baseStart_4217453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217519 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 2, 5]
def baseStart_4217519 : Nat := 118140960795 + 4217519 * 2 ^ 59
def prefixEnd_4217519 : Nat := 4983230072969 + 3 ^ 40 * 4217519 * 2
def baseEnd_4217519 : Nat := 721871472156596557072163

theorem tailTrace_4217519 : CollatzResearch.WordTrace tailWord_4217519 prefixEnd_4217519 721871472156596557072163 := by
  unfold tailWord_4217519
  simp only [CollatzResearch.WordTrace]
  refine ⟨153825555207656432744703611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102550370138437621829802407 153825555207656432744703611)
  ·
    refine ⟨230738332811484649117055417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153825555207656432744703611 230738332811484649117055417)
    ·
      refine ⟨173053749608613486837791563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230738332811484649117055417 173053749608613486837791563)
      ·
        refine ⟨259580624412920230256687345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173053749608613486837791563 259580624412920230256687345)
        ·
          refine ⟨194685468309690172692515509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259580624412920230256687345 194685468309690172692515509)
          ·
            refine ⟨18251762654033453689923329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 194685468309690172692515509 18251762654033453689923329)
            ·
              refine ⟨13688821990525090267442497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18251762654033453689923329 13688821990525090267442497)
              ·
                refine ⟨10266616492893817700581873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13688821990525090267442497 10266616492893817700581873)
                ·
                  refine ⟨7699962369670363275436405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10266616492893817700581873 7699962369670363275436405)
                  ·
                    refine ⟨721871472156596557072163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7699962369670363275436405 721871472156596557072163)
                    ·
                      rfl

theorem cell23_4217519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 5].length) (baseStart_4217519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217519 prefixEnd_4217519 := by exact prefixLift 4217519
  have htrace : WordTrace (prefixWord ++ tailWord_4217519) baseStart_4217519 baseEnd_4217519 := by
    simpa [prefixWord, tailWord_4217519, baseEnd_4217519] using wordTrace_append hprefix tailTrace_4217519
  have hstable : (prefixWord ++ tailWord_4217519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217519).length < 2 ^ (prefixWord ++ tailWord_4217519).sum := by decide
  have hdescent : baseEnd_4217519 < baseStart_4217519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217523 : List Nat := [1, 1, 1, 2, 3, 6, 2, 2, 5]
def baseStart_4217523 : Nat := 118140960795 + 4217523 * 2 ^ 59
def prefixEnd_4217523 : Nat := 4983230072969 + 3 ^ 40 * 4217523 * 2
def baseEnd_4217523 : Nat := 240624052265823072840719

theorem tailTrace_4217523 : CollatzResearch.WordTrace tailWord_4217523 prefixEnd_4217523 240624052265823072840719 := by
  unfold tailWord_4217523
  simp only [CollatzResearch.WordTrace]
  refine ⟨153825701099641941427849223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102550467399761294285232815 153825701099641941427849223)
  ·
    refine ⟨230738551649462912141773835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153825701099641941427849223 230738551649462912141773835)
    ·
      refine ⟨346107827474194368212660753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230738551649462912141773835 346107827474194368212660753)
      ·
        refine ⟨259580870605645776159495565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346107827474194368212660753 259580870605645776159495565)
        ·
          refine ⟨97342826477117166059810837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259580870605645776159495565 97342826477117166059810837)
          ·
            refine ⟨4562944991114867159053633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97342826477117166059810837 4562944991114867159053633)
            ·
              refine ⟨3422208743336150369290225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4562944991114867159053633 3422208743336150369290225)
              ·
                refine ⟨2566656557502112776967669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3422208743336150369290225 2566656557502112776967669)
                ·
                  refine ⟨240624052265823072840719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2566656557502112776967669 240624052265823072840719)
                  ·
                    rfl

theorem cell23_4217523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 5].length) (baseStart_4217523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217523 prefixEnd_4217523 := by exact prefixLift 4217523
  have htrace : WordTrace (prefixWord ++ tailWord_4217523) baseStart_4217523 baseEnd_4217523 := by
    simpa [prefixWord, tailWord_4217523, baseEnd_4217523] using wordTrace_append hprefix tailTrace_4217523
  have hstable : (prefixWord ++ tailWord_4217523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217523).length < 2 ^ (prefixWord ++ tailWord_4217523).sum := by decide
  have hdescent : baseEnd_4217523 < baseStart_4217523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217569 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_4217569 : Nat := 118140960795 + 4217569 * 2 ^ 59
def prefixEnd_4217569 : Nat := 4983230072969 + 3 ^ 40 * 4217569 * 2
def baseEnd_4217569 : Nat := 2165640090502514475591259

theorem tailTrace_4217569 : CollatzResearch.WordTrace tailWord_4217569 prefixEnd_4217569 2165640090502514475591259 := by
  unfold tailWord_4217569
  simp only [CollatzResearch.WordTrace]
  refine ⟨153827378857475291284023761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102551585904983527522682507 153827378857475291284023761)
  ·
    refine ⟨115370534143106468463017821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153827378857475291284023761 115370534143106468463017821)
    ·
      refine ⟨43263950303664925673631683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115370534143106468463017821 43263950303664925673631683)
      ·
        refine ⟨64895925455497388510447525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43263950303664925673631683 64895925455497388510447525)
        ·
          refine ⟨12167986022905760345708911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64895925455497388510447525 12167986022905760345708911)
          ·
            refine ⟨18251979034358640518563367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12167986022905760345708911 18251979034358640518563367)
            ·
              refine ⟨27377968551537960777845051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18251979034358640518563367 27377968551537960777845051)
              ·
                refine ⟨41066952827306941166767577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27377968551537960777845051 41066952827306941166767577)
                ·
                  refine ⟨30800214620480205875075683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41066952827306941166767577 30800214620480205875075683)
                  ·
                    refine ⟨46200321930720308812613525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30800214620480205875075683 46200321930720308812613525)
                    ·
                      refine ⟨2165640090502514475591259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46200321930720308812613525 2165640090502514475591259)
                      ·
                        rfl

theorem cell23_4217569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_4217569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217569 prefixEnd_4217569 := by exact prefixLift 4217569
  have htrace : WordTrace (prefixWord ++ tailWord_4217569) baseStart_4217569 baseEnd_4217569 := by
    simpa [prefixWord, tailWord_4217569, baseEnd_4217569] using wordTrace_append hprefix tailTrace_4217569
  have hstable : (prefixWord ++ tailWord_4217569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217569).length < 2 ^ (prefixWord ++ tailWord_4217569).sum := by decide
  have hdescent : baseEnd_4217569 < baseStart_4217569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217583 : List Nat := [1, 1, 2, 1, 5, 2, 2, 4, 1, 4]
def baseStart_4217583 : Nat := 118140960795 + 4217583 * 2 ^ 59
def prefixEnd_4217583 : Nat := 4983230072969 + 3 ^ 40 * 4217583 * 2
def baseEnd_4217583 : Nat := 721882426410559140272065

theorem tailTrace_4217583 : CollatzResearch.WordTrace tailWord_4217583 prefixEnd_4217583 721882426410559140272065 := by
  unfold tailWord_4217583
  simp only [CollatzResearch.WordTrace]
  refine ⟨153827889479424571675033403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102551926319616381116688935 153827889479424571675033403)
  ·
    refine ⟨230741834219136857512550105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153827889479424571675033403 230741834219136857512550105)
    ·
      refine ⟨173056375664352643134412579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230741834219136857512550105 173056375664352643134412579)
      ·
        refine ⟨259584563496528964701618869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173056375664352643134412579 259584563496528964701618869)
        ·
          refine ⟨24336052827799590440776769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 259584563496528964701618869 24336052827799590440776769)
          ·
            refine ⟨18252039620849692830582577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24336052827799590440776769 18252039620849692830582577)
            ·
              refine ⟨13689029715637269622936933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18252039620849692830582577 13689029715637269622936933)
              ·
                refine ⟨2566693071681988054300675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13689029715637269622936933 2566693071681988054300675)
                ·
                  refine ⟨3850039607522982081451013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2566693071681988054300675 3850039607522982081451013)
                  ·
                    refine ⟨721882426410559140272065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3850039607522982081451013 721882426410559140272065)
                    ·
                      rfl

theorem cell23_4217583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 1, 4].length) (baseStart_4217583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217583 prefixEnd_4217583 := by exact prefixLift 4217583
  have htrace : WordTrace (prefixWord ++ tailWord_4217583) baseStart_4217583 baseEnd_4217583 := by
    simpa [prefixWord, tailWord_4217583, baseEnd_4217583] using wordTrace_append hprefix tailTrace_4217583
  have hstable : (prefixWord ++ tailWord_4217583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217583).length < 2 ^ (prefixWord ++ tailWord_4217583).sum := by decide
  have hdescent : baseEnd_4217583 < baseStart_4217583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217609 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 3, 5]
def baseStart_4217609 : Nat := 118140960795 + 4217609 * 2 ^ 59
def prefixEnd_4217609 : Nat := 4983230072969 + 3 ^ 40 * 4217609 * 2
def baseEnd_4217609 : Nat := 721886876576231439697025

theorem tailTrace_4217609 : CollatzResearch.WordTrace tailWord_4217609 prefixEnd_4217609 721886876576231439697025 := by
  unfold tailWord_4217609
  simp only [CollatzResearch.WordTrace]
  refine ⟨153828837777330378115479881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102552558518220252076986587 153828837777330378115479881)
  ·
    refine ⟨115371628332997783586609911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153828837777330378115479881 115371628332997783586609911)
    ·
      refine ⟨173057442499496675379914867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115371628332997783586609911 173057442499496675379914867)
      ·
        refine ⟨259586163749245013069872301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173057442499496675379914867 259586163749245013069872301)
        ·
          refine ⟨97344811405966879901202113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259586163749245013069872301 97344811405966879901202113)
          ·
            refine ⟨73008608554475159925901585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97344811405966879901202113 73008608554475159925901585)
            ·
              refine ⟨54756456415856369944426189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73008608554475159925901585 54756456415856369944426189)
              ·
                refine ⟨20533671155946138729159821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54756456415856369944426189 20533671155946138729159821)
                ·
                  refine ⟨7700126683479802023434933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20533671155946138729159821 7700126683479802023434933)
                  ·
                    refine ⟨721886876576231439697025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7700126683479802023434933 721886876576231439697025)
                    ·
                      rfl

theorem cell23_4217609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 5].length) (baseStart_4217609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217609 prefixEnd_4217609 := by exact prefixLift 4217609
  have htrace : WordTrace (prefixWord ++ tailWord_4217609) baseStart_4217609 baseEnd_4217609 := by
    simpa [prefixWord, tailWord_4217609, baseEnd_4217609] using wordTrace_append hprefix tailTrace_4217609
  have hstable : (prefixWord ++ tailWord_4217609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217609).length < 2 ^ (prefixWord ++ tailWord_4217609).sum := by decide
  have hdescent : baseEnd_4217609 < baseStart_4217609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217626 : List Nat := [3, 1, 1, 3, 2, 1, 1, 5, 1, 5]
def baseStart_4217626 : Nat := 118140960795 + 4217626 * 2 ^ 59
def prefixEnd_4217626 : Nat := 4983230072969 + 3 ^ 40 * 4217626 * 2
def baseEnd_4217626 : Nat := 721889786299940250859499

theorem tailTrace_4217626 : CollatzResearch.WordTrace tailWord_4217626 prefixEnd_4217626 721889786299940250859499 := by
  unfold tailWord_4217626
  simp only [CollatzResearch.WordTrace]
  refine ⟨38457364454567197504712183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102552971878845860012565821 38457364454567197504712183)
  ·
    refine ⟨57686046681850796257068275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38457364454567197504712183 57686046681850796257068275)
    ·
      refine ⟨86529070022776194385602413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57686046681850796257068275 86529070022776194385602413)
      ·
        refine ⟨32448401258541072894600905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86529070022776194385602413 32448401258541072894600905)
        ·
          refine ⟨24336300943905804670950679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32448401258541072894600905 24336300943905804670950679)
          ·
            refine ⟨36504451415858707006426019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24336300943905804670950679 36504451415858707006426019)
            ·
              refine ⟨54756677123788060509639029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36504451415858707006426019 54756677123788060509639029)
              ·
                refine ⟨5133438480355130672778659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54756677123788060509639029 5133438480355130672778659)
                ·
                  refine ⟨7700157720532696009167989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5133438480355130672778659 7700157720532696009167989)
                  ·
                    refine ⟨721889786299940250859499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7700157720532696009167989 721889786299940250859499)
                    ·
                      rfl

theorem cell23_4217626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_4217626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217626 prefixEnd_4217626 := by exact prefixLift 4217626
  have htrace : WordTrace (prefixWord ++ tailWord_4217626) baseStart_4217626 baseEnd_4217626 := by
    simpa [prefixWord, tailWord_4217626, baseEnd_4217626] using wordTrace_append hprefix tailTrace_4217626
  have hstable : (prefixWord ++ tailWord_4217626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217626).length < 2 ^ (prefixWord ++ tailWord_4217626).sum := by decide
  have hdescent : baseEnd_4217626 < baseStart_4217626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217633 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 2, 3, 2]
def baseStart_4217633 : Nat := 118140960795 + 4217633 * 2 ^ 59
def prefixEnd_4217633 : Nat := 4983230072969 + 3 ^ 40 * 4217633 * 2
def baseEnd_4217633 : Nat := 2165672953264402225190965

theorem tailTrace_4217633 : CollatzResearch.WordTrace tailWord_4217633 prefixEnd_4217633 2165672953264402225190965 := by
  unfold tailWord_4217633
  simp only [CollatzResearch.WordTrace]
  refine ⟨153829713129243430214353553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102553142086162286809569035 153829713129243430214353553)
  ·
    refine ⟨115372284846932572660765165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153829713129243430214353553 115372284846932572660765165)
    ·
      refine ⟨43264606817599714747786937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115372284846932572660765165 43264606817599714747786937)
      ·
        refine ⟨32448455113199786060840203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43264606817599714747786937 32448455113199786060840203)
        ·
          refine ⟨48672682669799679091260305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32448455113199786060840203 48672682669799679091260305)
          ·
            refine ⟨36504512002349759318445229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48672682669799679091260305 36504512002349759318445229)
            ·
              refine ⟨13689192000881159744416961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36504512002349759318445229 13689192000881159744416961)
              ·
                refine ⟨10266894000660869808312721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13689192000881159744416961 10266894000660869808312721)
                ·
                  refine ⟨7700170500495652356234541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10266894000660869808312721 7700170500495652356234541)
                  ·
                    refine ⟨2887563937685869633587953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7700170500495652356234541 2887563937685869633587953)
                    ·
                      refine ⟨2165672953264402225190965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887563937685869633587953 2165672953264402225190965)
                      ·
                        rfl

theorem cell23_4217633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_4217633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217633 prefixEnd_4217633 := by exact prefixLift 4217633
  have htrace : WordTrace (prefixWord ++ tailWord_4217633) baseStart_4217633 baseEnd_4217633 := by
    simpa [prefixWord, tailWord_4217633, baseEnd_4217633] using wordTrace_append hprefix tailTrace_4217633
  have hstable : (prefixWord ++ tailWord_4217633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217633).length < 2 ^ (prefixWord ++ tailWord_4217633).sum := by decide
  have hdescent : baseEnd_4217633 < baseStart_4217633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217663 : List Nat := [1, 1, 2, 2, 5, 1, 3, 2, 1, 1, 4]
def baseStart_4217663 : Nat := 118140960795 + 4217663 * 2 ^ 59
def prefixEnd_4217663 : Nat := 4983230072969 + 3 ^ 40 * 4217663 * 2
def baseEnd_4217663 : Nat := 2165688357684037107815827

theorem tailTrace_4217663 : CollatzResearch.WordTrace tailWord_4217663 prefixEnd_4217663 2165688357684037107815827 := by
  unfold tailWord_4217663
  simp only [CollatzResearch.WordTrace]
  refine ⟨153830807319134745337945643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102553871546089830225297095 153830807319134745337945643)
  ·
    refine ⟨230746210978702118006918465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153830807319134745337945643 230746210978702118006918465)
    ·
      refine ⟨173059658234026588505188849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230746210978702118006918465 173059658234026588505188849)
      ·
        refine ⟨129794743675519941378891637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173059658234026588505188849 129794743675519941378891637)
        ·
          refine ⟨12168257219579994504271091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129794743675519941378891637 12168257219579994504271091)
          ·
            refine ⟨18252385829369991756406637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12168257219579994504271091 18252385829369991756406637)
            ·
              refine ⟨6844644686013746908652489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18252385829369991756406637 6844644686013746908652489)
              ·
                refine ⟨5133483514510310181489367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6844644686013746908652489 5133483514510310181489367)
                ·
                  refine ⟨7700225271765465272234051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5133483514510310181489367 7700225271765465272234051)
                  ·
                    refine ⟨11550337907648197908351077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7700225271765465272234051 11550337907648197908351077)
                    ·
                      refine ⟨2165688357684037107815827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11550337907648197908351077 2165688357684037107815827)
                      ·
                        rfl

theorem cell23_4217663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_4217663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217663 prefixEnd_4217663 := by exact prefixLift 4217663
  have htrace : WordTrace (prefixWord ++ tailWord_4217663) baseStart_4217663 baseEnd_4217663 := by
    simpa [prefixWord, tailWord_4217663, baseEnd_4217663] using wordTrace_append hprefix tailTrace_4217663
  have hstable : (prefixWord ++ tailWord_4217663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217663).length < 2 ^ (prefixWord ++ tailWord_4217663).sum := by decide
  have hdescent : baseEnd_4217663 < baseStart_4217663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217676 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_4217676 : Nat := 118140960795 + 4217676 * 2 ^ 59
def prefixEnd_4217676 : Nat := 4983230072969 + 3 ^ 40 * 4217676 * 2
def baseEnd_4217676 : Nat := 2165695032932545556953267

theorem tailTrace_4217676 : CollatzResearch.WordTrace tailWord_4217676 prefixEnd_4217676 2165695032932545556953267 := by
  unfold tailWord_4217676
  simp only [CollatzResearch.WordTrace]
  refine ⟨76915640734043824279084441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102554187645391765705445921 76915640734043824279084441)
  ·
    refine ⟨57686730550532868209313331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76915640734043824279084441 57686730550532868209313331)
    ·
      refine ⟨86530095825799302313969997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57686730550532868209313331 86530095825799302313969997)
      ·
        refine ⟨32448785934674738367738749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86530095825799302313969997 32448785934674738367738749)
        ·
          refine ⟨12168294725503026887902031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32448785934674738367738749 12168294725503026887902031)
          ·
            refine ⟨18252442088254540331853047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12168294725503026887902031 18252442088254540331853047)
            ·
              refine ⟨27378663132381810497779571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18252442088254540331853047 27378663132381810497779571)
              ·
                refine ⟨41067994698572715746669357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27378663132381810497779571 41067994698572715746669357)
                ·
                  refine ⟨15400498011964768405001009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41067994698572715746669357 15400498011964768405001009)
                  ·
                    refine ⟨11550373508973576303750757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15400498011964768405001009 11550373508973576303750757)
                    ·
                      refine ⟨2165695032932545556953267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11550373508973576303750757 2165695032932545556953267)
                      ·
                        rfl

theorem cell23_4217676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_4217676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217676 prefixEnd_4217676 := by exact prefixLift 4217676
  have htrace : WordTrace (prefixWord ++ tailWord_4217676) baseStart_4217676 baseEnd_4217676 := by
    simpa [prefixWord, tailWord_4217676, baseEnd_4217676] using wordTrace_append hprefix tailTrace_4217676
  have hstable : (prefixWord ++ tailWord_4217676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217676).length < 2 ^ (prefixWord ++ tailWord_4217676).sum := by decide
  have hdescent : baseEnd_4217676 < baseStart_4217676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217677 : List Nat := [1, 6, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_4217677 : Nat := 118140960795 + 4217677 * 2 ^ 59
def prefixEnd_4217677 : Nat := 4983230072969 + 3 ^ 40 * 4217677 * 2
def baseEnd_4217677 : Nat := 721898515471066684346921

theorem tailTrace_4217677 : CollatzResearch.WordTrace tailWord_4217677 prefixEnd_4217677 721898515471066684346921 := by
  unfold tailWord_4217677
  simp only [CollatzResearch.WordTrace]
  refine ⟨153831317941084025728955285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102554211960722683819303523 153831317941084025728955285)
  ·
    refine ⟨7210843028488313706044779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 153831317941084025728955285 7210843028488313706044779)
    ·
      refine ⟨10816264542732470559067169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7210843028488313706044779 10816264542732470559067169)
      ·
        refine ⟨8112198407049352919300377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10816264542732470559067169 8112198407049352919300377)
        ·
          refine ⟨6084148805287014689475283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8112198407049352919300377 6084148805287014689475283)
          ·
            refine ⟨9126223207930522034212925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6084148805287014689475283 9126223207930522034212925)
            ·
              refine ⟨3422333702973945762829847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9126223207930522034212925 3422333702973945762829847)
              ·
                refine ⟨5133500554460918644244771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3422333702973945762829847 5133500554460918644244771)
                ·
                  refine ⟨7700250831691377966367157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5133500554460918644244771 7700250831691377966367157)
                  ·
                    refine ⟨721898515471066684346921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7700250831691377966367157 721898515471066684346921)
                    ·
                      rfl

theorem cell23_4217677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_4217677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217677 prefixEnd_4217677 := by exact prefixLift 4217677
  have htrace : WordTrace (prefixWord ++ tailWord_4217677) baseStart_4217677 baseEnd_4217677 := by
    simpa [prefixWord, tailWord_4217677, baseEnd_4217677] using wordTrace_append hprefix tailTrace_4217677
  have hstable : (prefixWord ++ tailWord_4217677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217677).length < 2 ^ (prefixWord ++ tailWord_4217677).sum := by decide
  have hdescent : baseEnd_4217677 < baseStart_4217677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217696 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 3]
def baseStart_4217696 : Nat := 118140960795 + 4217696 * 2 ^ 59
def prefixEnd_4217696 : Nat := 4983230072969 + 3 ^ 40 * 4217696 * 2
def baseEnd_4217696 : Nat := 2165705302545635478703175

theorem tailTrace_4217696 : CollatzResearch.WordTrace tailWord_4217696 prefixEnd_4217696 2165705302545635478703175 := by
  unfold tailWord_4217696
  simp only [CollatzResearch.WordTrace]
  refine ⟨76916005464007595986948471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102554673952010127982597961 76916005464007595986948471)
  ·
    refine ⟨115374008196011393980422707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76916005464007595986948471 115374008196011393980422707)
    ·
      refine ⟨173061012294017090970634061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115374008196011393980422707 173061012294017090970634061)
      ·
        refine ⟨64897879610256409113987773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173061012294017090970634061 64897879610256409113987773)
        ·
          refine ⟨24336704853846153417745415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64897879610256409113987773 24336704853846153417745415)
          ·
            refine ⟨36505057280769230126618123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24336704853846153417745415 36505057280769230126618123)
            ·
              refine ⟨54757585921153845189927185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36505057280769230126618123 54757585921153845189927185)
              ·
                refine ⟨41068189440865383892445389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54757585921153845189927185 41068189440865383892445389)
                ·
                  refine ⟨15400571040324518959667021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41068189440865383892445389 15400571040324518959667021)
                  ·
                    refine ⟨5775214140121694609875133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15400571040324518959667021 5775214140121694609875133)
                    ·
                      refine ⟨2165705302545635478703175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5775214140121694609875133 2165705302545635478703175)
                      ·
                        rfl

theorem cell23_4217696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_4217696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217696 prefixEnd_4217696 := by exact prefixLift 4217696
  have htrace : WordTrace (prefixWord ++ tailWord_4217696) baseStart_4217696 baseEnd_4217696 := by
    simpa [prefixWord, tailWord_4217696, baseEnd_4217696] using wordTrace_append hprefix tailTrace_4217696
  have hstable : (prefixWord ++ tailWord_4217696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217696).length < 2 ^ (prefixWord ++ tailWord_4217696).sum := by decide
  have hdescent : baseEnd_4217696 < baseStart_4217696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217710 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_4217710 : Nat := 118140960795 + 4217710 * 2 ^ 59
def prefixEnd_4217710 : Nat := 4983230072969 + 3 ^ 40 * 4217710 * 2
def baseEnd_4217710 : Nat := 2165712491274798423928111

theorem tailTrace_4217710 : CollatzResearch.WordTrace tailWord_4217710 prefixEnd_4217710 2165712491274798423928111 := by
  unfold tailWord_4217710
  simp only [CollatzResearch.WordTrace]
  refine ⟨19229065193745559045613323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102555014366642981576604389 19229065193745559045613323)
  ·
    refine ⟨28843597790618338568419985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19229065193745559045613323 28843597790618338568419985)
    ·
      refine ⟨21632698342963753926314989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28843597790618338568419985 21632698342963753926314989)
      ·
        refine ⟨8112261878611407722368121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21632698342963753926314989 8112261878611407722368121)
        ·
          refine ⟨6084196408958555791776091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8112261878611407722368121 6084196408958555791776091)
          ·
            refine ⟨9126294613437833687664137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6084196408958555791776091 9126294613437833687664137)
            ·
              refine ⟨6844720960078375265748103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9126294613437833687664137 6844720960078375265748103)
              ·
                refine ⟨10267081440117562898622155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6844720960078375265748103 10267081440117562898622155)
                ·
                  refine ⟨15400622160176344347933233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10267081440117562898622155 15400622160176344347933233)
                  ·
                    refine ⟨11550466620132258260949925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15400622160176344347933233 11550466620132258260949925)
                    ·
                      refine ⟨2165712491274798423928111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11550466620132258260949925 2165712491274798423928111)
                      ·
                        rfl

theorem cell23_4217710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_4217710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217710 prefixEnd_4217710 := by exact prefixLift 4217710
  have htrace : WordTrace (prefixWord ++ tailWord_4217710) baseStart_4217710 baseEnd_4217710 := by
    simpa [prefixWord, tailWord_4217710, baseEnd_4217710] using wordTrace_append hprefix tailTrace_4217710
  have hstable : (prefixWord ++ tailWord_4217710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217710).length < 2 ^ (prefixWord ++ tailWord_4217710).sum := by decide
  have hdescent : baseEnd_4217710 < baseStart_4217710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217713 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 1, 3, 3]
def baseStart_4217713 : Nat := 118140960795 + 4217713 * 2 ^ 59
def prefixEnd_4217713 : Nat := 4983230072969 + 3 ^ 40 * 4217713 * 2
def baseEnd_4217713 : Nat := 2165714031716761912190597

theorem tailTrace_4217713 : CollatzResearch.WordTrace tailWord_4217713 prefixEnd_4217713 2165714031716761912190597 := by
  unfold tailWord_4217713
  simp only [CollatzResearch.WordTrace]
  refine ⟨153832630968953603877265793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102555087312635735918177195 153832630968953603877265793)
  ·
    refine ⟨115374473226715202907949345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153832630968953603877265793 115374473226715202907949345)
    ·
      refine ⟨86530854920036402180962009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115374473226715202907949345 86530854920036402180962009)
      ·
        refine ⟨64898141190027301635721507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86530854920036402180962009 64898141190027301635721507)
        ·
          refine ⟨97347211785040952453582261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64898141190027301635721507 97347211785040952453582261)
          ·
            refine ⟨9126301104847589292523337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97347211785040952453582261 9126301104847589292523337)
            ·
              refine ⟨6844725828635691969392503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9126301104847589292523337 6844725828635691969392503)
              ·
                refine ⟨10267088742953537954088755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6844725828635691969392503 10267088742953537954088755)
                ·
                  refine ⟨15400633114430306931133133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10267088742953537954088755 15400633114430306931133133)
                  ·
                    refine ⟨5775237417911365099174925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15400633114430306931133133 5775237417911365099174925)
                    ·
                      refine ⟨2165714031716761912190597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5775237417911365099174925 2165714031716761912190597)
                      ·
                        rfl

theorem cell23_4217713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_4217713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217713 prefixEnd_4217713 := by exact prefixLift 4217713
  have htrace : WordTrace (prefixWord ++ tailWord_4217713) baseStart_4217713 baseEnd_4217713 := by
    simpa [prefixWord, tailWord_4217713, baseEnd_4217713] using wordTrace_append hprefix tailTrace_4217713
  have hstable : (prefixWord ++ tailWord_4217713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217713).length < 2 ^ (prefixWord ++ tailWord_4217713).sum := by decide
  have hdescent : baseEnd_4217713 < baseStart_4217713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217723 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 3, 3, 2]
def baseStart_4217723 : Nat := 118140960795 + 4217723 * 2 ^ 59
def prefixEnd_4217723 : Nat := 4983230072969 + 3 ^ 40 * 4217723 * 2
def baseEnd_4217723 : Nat := 2165719166523306873065551

theorem tailTrace_4217723 : CollatzResearch.WordTrace tailWord_4217723 prefixEnd_4217723 2165719166523306873065551 := by
  unfold tailWord_4217723
  simp only [CollatzResearch.WordTrace]
  refine ⟨153832995698917375585129823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102555330465944917056753215 153832995698917375585129823)
  ·
    refine ⟨230749493548376063377694735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153832995698917375585129823 230749493548376063377694735)
    ·
      refine ⟨346124240322564095066542103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230749493548376063377694735 346124240322564095066542103)
      ·
        refine ⟨519186360483846142599813155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346124240322564095066542103 519186360483846142599813155)
        ·
          refine ⟨778779540725769213899719733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519186360483846142599813155 778779540725769213899719733)
          ·
            refine ⟨73010581943040863803098725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 778779540725769213899719733 73010581943040863803098725)
            ·
              refine ⟨13689484114320161963081011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73010581943040863803098725 13689484114320161963081011)
              ·
                refine ⟨20534226171480242944621517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13689484114320161963081011 20534226171480242944621517)
                ·
                  refine ⟨7700334814305091104233069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20534226171480242944621517 7700334814305091104233069)
                  ·
                    refine ⟨2887625555364409164087401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7700334814305091104233069 2887625555364409164087401)
                    ·
                      refine ⟨2165719166523306873065551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887625555364409164087401 2165719166523306873065551)
                      ·
                        rfl

theorem cell23_4217723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 3, 2].length) (baseStart_4217723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217723 prefixEnd_4217723 := by exact prefixLift 4217723
  have htrace : WordTrace (prefixWord ++ tailWord_4217723) baseStart_4217723 baseEnd_4217723 := by
    simpa [prefixWord, tailWord_4217723, baseEnd_4217723] using wordTrace_append hprefix tailTrace_4217723
  have hstable : (prefixWord ++ tailWord_4217723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217723).length < 2 ^ (prefixWord ++ tailWord_4217723).sum := by decide
  have hdescent : baseEnd_4217723 < baseStart_4217723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217782 : List Nat := [5, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_4217782 : Nat := 118140960795 + 4217782 * 2 ^ 59
def prefixEnd_4217782 : Nat := 4983230072969 + 3 ^ 40 * 4217782 * 2
def baseEnd_4217782 : Nat := 2165749461881922142227781

theorem tailTrace_4217782 : CollatzResearch.WordTrace tailWord_4217782 prefixEnd_4217782 2165749461881922142227781 := by
  unfold tailWord_4217782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9614696725356476791345475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102556765070469085774351733 9614696725356476791345475)
  ·
    refine ⟨14422045088034715187018213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9614696725356476791345475 14422045088034715187018213)
    ·
      refine ⟨2704133454006509097565915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14422045088034715187018213 2704133454006509097565915)
      ·
        refine ⟨4056200181009763646348873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2704133454006509097565915 4056200181009763646348873)
        ·
          refine ⟨3042150135757322734761655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4056200181009763646348873 3042150135757322734761655)
          ·
            refine ⟨4563225203635984102142483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3042150135757322734761655 4563225203635984102142483)
            ·
              refine ⟨6844837805453976153213725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4563225203635984102142483 6844837805453976153213725)
              ·
                refine ⟨2566814177045241057455147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6844837805453976153213725 2566814177045241057455147)
                ·
                  refine ⟨3850221265567861586182721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2566814177045241057455147 3850221265567861586182721)
                  ·
                    refine ⟨2887665949175896189637041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3850221265567861586182721 2887665949175896189637041)
                    ·
                      refine ⟨2165749461881922142227781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887665949175896189637041 2165749461881922142227781)
                      ·
                        rfl

theorem cell23_4217782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_4217782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217782 prefixEnd_4217782 := by exact prefixLift 4217782
  have htrace : WordTrace (prefixWord ++ tailWord_4217782) baseStart_4217782 baseEnd_4217782 := by
    simpa [prefixWord, tailWord_4217782, baseEnd_4217782] using wordTrace_append hprefix tailTrace_4217782
  have hstable : (prefixWord ++ tailWord_4217782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217782).length < 2 ^ (prefixWord ++ tailWord_4217782).sum := by decide
  have hdescent : baseEnd_4217782 < baseStart_4217782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217810 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 7]
def baseStart_4217810 : Nat := 118140960795 + 4217810 * 2 ^ 59
def prefixEnd_4217810 : Nat := 4983230072969 + 3 ^ 40 * 4217810 * 2
def baseEnd_4217810 : Nat := 240640426593360892519739

theorem tailTrace_4217810 : CollatzResearch.WordTrace tailWord_4217810 prefixEnd_4217810 240640426593360892519739 := by
  unfold tailWord_4217810
  simp only [CollatzResearch.WordTrace]
  refine ⟨38459042212400547360886721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102557445899734792962364589 38459042212400547360886721)
  ·
    refine ⟨28844281659300410520665041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38459042212400547360886721 28844281659300410520665041)
    ·
      refine ⟨21633211244475307890498781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28844281659300410520665041 21633211244475307890498781)
      ·
        refine ⟨8112454216678240458937043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21633211244475307890498781 8112454216678240458937043)
        ·
          refine ⟨12168681325017360688405565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8112454216678240458937043 12168681325017360688405565)
          ·
            refine ⟨4563255496881510258152087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12168681325017360688405565 4563255496881510258152087)
            ·
              refine ⟨6844883245322265387228131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4563255496881510258152087 6844883245322265387228131)
              ·
                refine ⟨10267324867983398080842197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6844883245322265387228131 10267324867983398080842197)
                ·
                  refine ⟨240640426593360892519739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10267324867983398080842197 240640426593360892519739)
                  ·
                    rfl

theorem cell23_4217810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_4217810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217810 prefixEnd_4217810 := by exact prefixLift 4217810
  have htrace : WordTrace (prefixWord ++ tailWord_4217810) baseStart_4217810 baseEnd_4217810 := by
    simpa [prefixWord, tailWord_4217810, baseEnd_4217810] using wordTrace_append hprefix tailTrace_4217810
  have hstable : (prefixWord ++ tailWord_4217810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217810).length < 2 ^ (prefixWord ++ tailWord_4217810).sum := by decide
  have hdescent : baseEnd_4217810 < baseStart_4217810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217816 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_4217816 : Nat := 118140960795 + 4217816 * 2 ^ 59
def prefixEnd_4217816 : Nat := 4983230072969 + 3 ^ 40 * 4217816 * 2
def baseEnd_4217816 : Nat := 2165766920224175009202623

theorem tailTrace_4217816 : CollatzResearch.WordTrace tailWord_4217816 prefixEnd_4217816 2165766920224175009202623 := by
  unfold tailWord_4217816
  simp only [CollatzResearch.WordTrace]
  refine ⟨76918193843790226234132651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102557591791720301645510201 76918193843790226234132651)
  ·
    refine ⟨115377290765685339351198977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76918193843790226234132651 115377290765685339351198977)
    ·
      refine ⟨86532968074264004513399233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115377290765685339351198977 86532968074264004513399233)
      ·
        refine ⟨64899726055698003385049425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86532968074264004513399233 64899726055698003385049425)
        ·
          refine ⟨48674794541773502538787069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64899726055698003385049425 48674794541773502538787069)
          ·
            refine ⟨18253047953165063452045151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48674794541773502538787069 18253047953165063452045151)
            ·
              refine ⟨27379571929747595178067727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18253047953165063452045151 27379571929747595178067727)
              ·
                refine ⟨41069357894621392767101591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27379571929747595178067727 41069357894621392767101591)
                ·
                  refine ⟨61604036841932089150652387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41069357894621392767101591 61604036841932089150652387)
                  ·
                    refine ⟨92406055262898133725978581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61604036841932089150652387 92406055262898133725978581)
                    ·
                      refine ⟨2165766920224175009202623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92406055262898133725978581 2165766920224175009202623)
                      ·
                        rfl

theorem cell23_4217816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_4217816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217816 prefixEnd_4217816 := by exact prefixLift 4217816
  have htrace : WordTrace (prefixWord ++ tailWord_4217816) baseStart_4217816 baseEnd_4217816 := by
    simpa [prefixWord, tailWord_4217816, baseEnd_4217816] using wordTrace_append hprefix tailTrace_4217816
  have hstable : (prefixWord ++ tailWord_4217816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217816).length < 2 ^ (prefixWord ++ tailWord_4217816).sum := by decide
  have hdescent : baseEnd_4217816 < baseStart_4217816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217821 : List Nat := [1, 4, 3, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_4217821 : Nat := 118140960795 + 4217821 * 2 ^ 59
def prefixEnd_4217821 : Nat := 4983230072969 + 3 ^ 40 * 4217821 * 2
def baseEnd_4217821 : Nat := 2165769487627447489640101

theorem tailTrace_4217821 : CollatzResearch.WordTrace tailWord_4217821 prefixEnd_4217821 2165769487627447489640101 := by
  unfold tailWord_4217821
  simp only [CollatzResearch.WordTrace]
  refine ⟨153836570052562338322197317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102557713368374892214798211 153836570052562338322197317)
  ·
    refine ⟨28844356884855438435411997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153836570052562338322197317 28844356884855438435411997)
    ·
      refine ⟨10816633831820789413279499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28844356884855438435411997 10816633831820789413279499)
      ·
        refine ⟨16224950747731184119919249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10816633831820789413279499 16224950747731184119919249)
        ·
          refine ⟨12168713060798388089939437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16224950747731184119919249 12168713060798388089939437)
          ·
            refine ⟨4563267397799395533727289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12168713060798388089939437 4563267397799395533727289)
            ·
              refine ⟨3422450548349546650295467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4563267397799395533727289 3422450548349546650295467)
              ·
                refine ⟨5133675822524319975443201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3422450548349546650295467 5133675822524319975443201)
                ·
                  refine ⟨3850256866893239981582401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5133675822524319975443201 3850256866893239981582401)
                  ·
                    refine ⟨2887692650169929986186801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3850256866893239981582401 2887692650169929986186801)
                    ·
                      refine ⟨2165769487627447489640101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887692650169929986186801 2165769487627447489640101)
                      ·
                        rfl

theorem cell23_4217821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_4217821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217821 prefixEnd_4217821 := by exact prefixLift 4217821
  have htrace : WordTrace (prefixWord ++ tailWord_4217821) baseStart_4217821 baseEnd_4217821 := by
    simpa [prefixWord, tailWord_4217821, baseEnd_4217821] using wordTrace_append hprefix tailTrace_4217821
  have hstable : (prefixWord ++ tailWord_4217821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217821).length < 2 ^ (prefixWord ++ tailWord_4217821).sum := by decide
  have hdescent : baseEnd_4217821 < baseStart_4217821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217843 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 6, 4, 2]
def baseStart_4217843 : Nat := 118140960795 + 4217843 * 2 ^ 59
def prefixEnd_4217843 : Nat := 4983230072969 + 3 ^ 40 * 4217843 * 2
def baseEnd_4217843 : Nat := 2165780784201846403564999

theorem tailTrace_4217843 : CollatzResearch.WordTrace tailWord_4217843 prefixEnd_4217843 2165780784201846403564999 := by
  unfold tailWord_4217843
  simp only [CollatzResearch.WordTrace]
  refine ⟨153837372458482636079498183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102558248305655090719665455 153837372458482636079498183)
  ·
    refine ⟨230756058687723954119247275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153837372458482636079498183 230756058687723954119247275)
    ·
      refine ⟨346134088031585931178870913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230756058687723954119247275 346134088031585931178870913)
      ·
        refine ⟨259600566023689448384153185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346134088031585931178870913 259600566023689448384153185)
        ·
          refine ⟨194700424517767086288114889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259600566023689448384153185 194700424517767086288114889)
          ·
            refine ⟨146025318388325314716086167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194700424517767086288114889 146025318388325314716086167)
            ·
              refine ⟨219037977582487972074129251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146025318388325314716086167 219037977582487972074129251)
              ·
                refine ⟨328556966373731958111193877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219037977582487972074129251 328556966373731958111193877)
                ·
                  refine ⟨15401107798768685536462213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 328556966373731958111193877 15401107798768685536462213)
                  ·
                    refine ⟨2887707712269128538086665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15401107798768685536462213 2887707712269128538086665)
                    ·
                      refine ⟨2165780784201846403564999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887707712269128538086665 2165780784201846403564999)
                      ·
                        rfl

theorem cell23_4217843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 4, 2].length) (baseStart_4217843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217843 prefixEnd_4217843 := by exact prefixLift 4217843
  have htrace : WordTrace (prefixWord ++ tailWord_4217843) baseStart_4217843 baseEnd_4217843 := by
    simpa [prefixWord, tailWord_4217843, baseEnd_4217843] using wordTrace_append hprefix tailTrace_4217843
  have hstable : (prefixWord ++ tailWord_4217843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217843).length < 2 ^ (prefixWord ++ tailWord_4217843).sum := by decide
  have hdescent : baseEnd_4217843 < baseStart_4217843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217856 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 4]
def baseStart_4217856 : Nat := 118140960795 + 4217856 * 2 ^ 59
def prefixEnd_4217856 : Nat := 4983230072969 + 3 ^ 40 * 4217856 * 2
def baseEnd_4217856 : Nat := 2165787459450354852702439

theorem tailTrace_4217856 : CollatzResearch.WordTrace tailWord_4217856 prefixEnd_4217856 2165787459450354852702439 := by
  unfold tailWord_4217856
  simp only [CollatzResearch.WordTrace]
  refine ⟨76918923303717769649860711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102558564404957026199814281 76918923303717769649860711)
  ·
    refine ⟨115378384955576654474791067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76918923303717769649860711 115378384955576654474791067)
    ·
      refine ⟨173067577433364981712186601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115378384955576654474791067 173067577433364981712186601)
      ·
        refine ⟨129800683075023736284139951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173067577433364981712186601 129800683075023736284139951)
        ·
          refine ⟨194701024612535604426209927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129800683075023736284139951 194701024612535604426209927)
          ·
            refine ⟨292051536918803406639314891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194701024612535604426209927 292051536918803406639314891)
            ·
              refine ⟨438077305378205109958972337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292051536918803406639314891 438077305378205109958972337)
              ·
                refine ⟨328557979033653832469229253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438077305378205109958972337 328557979033653832469229253)
                ·
                  refine ⟨61604621068810093587980485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 328557979033653832469229253 61604621068810093587980485)
                  ·
                    refine ⟨11550866450401892547746341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61604621068810093587980485 11550866450401892547746341)
                    ·
                      refine ⟨2165787459450354852702439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11550866450401892547746341 2165787459450354852702439)
                      ·
                        rfl

theorem cell23_4217856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_4217856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217856 prefixEnd_4217856 := by exact prefixLift 4217856
  have htrace : WordTrace (prefixWord ++ tailWord_4217856) baseStart_4217856 baseEnd_4217856 := by
    simpa [prefixWord, tailWord_4217856, baseEnd_4217856] using wordTrace_append hprefix tailTrace_4217856
  have hstable : (prefixWord ++ tailWord_4217856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217856).length < 2 ^ (prefixWord ++ tailWord_4217856).sum := by decide
  have hdescent : baseEnd_4217856 < baseStart_4217856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217920 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 4, 3, 2]
def baseStart_4217920 : Nat := 118140960795 + 4217920 * 2 ^ 59
def prefixEnd_4217920 : Nat := 4983230072969 + 3 ^ 40 * 4217920 * 2
def baseEnd_4217920 : Nat := 2165820322212242602302145

theorem tailTrace_4217920 : CollatzResearch.WordTrace tailWord_4217920 prefixEnd_4217920 2165820322212242602302145 := by
  unfold tailWord_4217920
  simp only [CollatzResearch.WordTrace]
  refine ⟨76920090439601839115025607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102560120586135785486700809 76920090439601839115025607)
  ·
    refine ⟨115380135659402758672538411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76920090439601839115025607 115380135659402758672538411)
    ·
      refine ⟨173070203489104138008807617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115380135659402758672538411 173070203489104138008807617)
      ·
        refine ⟨129802652616828103506605713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173070203489104138008807617 129802652616828103506605713)
        ·
          refine ⟨97351989462621077629954285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129802652616828103506605713 97351989462621077629954285)
          ·
            refine ⟨36506996048482904111232857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97351989462621077629954285 36506996048482904111232857)
            ·
              refine ⟨27380247036362178083424643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36506996048482904111232857 27380247036362178083424643)
              ·
                refine ⟨41070370554543267125136965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27380247036362178083424643 41070370554543267125136965)
                ·
                  refine ⟨7700694478976862585963181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41070370554543267125136965 7700694478976862585963181)
                  ·
                    refine ⟨2887760429616323469736193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7700694478976862585963181 2887760429616323469736193)
                    ·
                      refine ⟨2165820322212242602302145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887760429616323469736193 2165820322212242602302145)
                      ·
                        rfl

theorem cell23_4217920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4, 3, 2].length) (baseStart_4217920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217920 prefixEnd_4217920 := by exact prefixLift 4217920
  have htrace : WordTrace (prefixWord ++ tailWord_4217920) baseStart_4217920 baseEnd_4217920 := by
    simpa [prefixWord, tailWord_4217920, baseEnd_4217920] using wordTrace_append hprefix tailTrace_4217920
  have hstable : (prefixWord ++ tailWord_4217920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217920).length < 2 ^ (prefixWord ++ tailWord_4217920).sum := by decide
  have hdescent : baseEnd_4217920 < baseStart_4217920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217927 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 3, 1, 3]
def baseStart_4217927 : Nat := 118140960795 + 4217927 * 2 ^ 59
def prefixEnd_4217927 : Nat := 4983230072969 + 3 ^ 40 * 4217927 * 2
def baseEnd_4217927 : Nat := 2165823916576824074914613

theorem tailTrace_4217927 : CollatzResearch.WordTrace tailWord_4217927 prefixEnd_4217927 2165823916576824074914613 := by
  unfold tailWord_4217927
  simp only [CollatzResearch.WordTrace]
  refine ⟨153840436190178318425556035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102560290793452212283704023 153840436190178318425556035)
  ·
    refine ⟨230760654285267477638334053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153840436190178318425556035 230760654285267477638334053)
    ·
      refine ⟨43267622678487652057187635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230760654285267477638334053 43267622678487652057187635)
      ·
        refine ⟨64901434017731478085781453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43267622678487652057187635 64901434017731478085781453)
        ·
          refine ⟨24338037756649304282168045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64901434017731478085781453 24338037756649304282168045)
          ·
            refine ⟨9126764158743489105813017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24338037756649304282168045 9126764158743489105813017)
            ·
              refine ⟨6845073119057616829359763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9126764158743489105813017 6845073119057616829359763)
              ·
                refine ⟨10267609678586425244039645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6845073119057616829359763 10267609678586425244039645)
                ·
                  refine ⟨3850353629469909466514867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10267609678586425244039645 3850353629469909466514867)
                  ·
                    refine ⟨5775530444204864199772301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3850353629469909466514867 5775530444204864199772301)
                    ·
                      refine ⟨2165823916576824074914613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5775530444204864199772301 2165823916576824074914613)
                      ·
                        rfl

theorem cell23_4217927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_4217927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217927 prefixEnd_4217927 := by exact prefixLift 4217927
  have htrace : WordTrace (prefixWord ++ tailWord_4217927) baseStart_4217927 baseEnd_4217927 := by
    simpa [prefixWord, tailWord_4217927, baseEnd_4217927] using wordTrace_append hprefix tailTrace_4217927
  have hstable : (prefixWord ++ tailWord_4217927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217927).length < 2 ^ (prefixWord ++ tailWord_4217927).sum := by decide
  have hdescent : baseEnd_4217927 < baseStart_4217927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217970 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_4217970 : Nat := 118140960795 + 4217970 * 2 ^ 59
def prefixEnd_4217970 : Nat := 4983230072969 + 3 ^ 40 * 4217970 * 2
def baseEnd_4217970 : Nat := 2165845996244967406676915

theorem tailTrace_4217970 : CollatzResearch.WordTrace tailWord_4217970 prefixEnd_4217970 2165845996244967406676915 := by
  unfold tailWord_4217970
  simp only [CollatzResearch.WordTrace]
  refine ⟨38460501132255634192342841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102561336352681691179580909 38460501132255634192342841)
  ·
    refine ⟨28845375849191725644257131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38460501132255634192342841 28845375849191725644257131)
    ·
      refine ⟨43268063773787588466385697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28845375849191725644257131 43268063773787588466385697)
      ·
        refine ⟨32451047830340691349789273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43268063773787588466385697 32451047830340691349789273)
        ·
          refine ⟨24338285872755518512341955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32451047830340691349789273 24338285872755518512341955)
          ·
            refine ⟨36507428809133277768512933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24338285872755518512341955 36507428809133277768512933)
            ·
              refine ⟨6845142901712489581596175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36507428809133277768512933 6845142901712489581596175)
              ·
                refine ⟨10267714352568734372394263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6845142901712489581596175 10267714352568734372394263)
                ·
                  refine ⟨15401571528853101558591395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10267714352568734372394263 15401571528853101558591395)
                  ·
                    refine ⟨23102357293279652337887093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15401571528853101558591395 23102357293279652337887093)
                    ·
                      refine ⟨2165845996244967406676915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23102357293279652337887093 2165845996244967406676915)
                      ·
                        rfl

theorem cell23_4217970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_4217970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217970 prefixEnd_4217970 := by exact prefixLift 4217970
  have htrace : WordTrace (prefixWord ++ tailWord_4217970) baseStart_4217970 baseEnd_4217970 := by
    simpa [prefixWord, tailWord_4217970, baseEnd_4217970] using wordTrace_append hprefix tailTrace_4217970
  have hstable : (prefixWord ++ tailWord_4217970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217970).length < 2 ^ (prefixWord ++ tailWord_4217970).sum := by decide
  have hdescent : baseEnd_4217970 < baseStart_4217970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217984 : List Nat := [2, 1, 1, 2, 1, 3, 2, 6, 1, 2, 2]
def baseStart_4217984 : Nat := 118140960795 + 4217984 * 2 ^ 59
def prefixEnd_4217984 : Nat := 4983230072969 + 3 ^ 40 * 4217984 * 2
def baseEnd_4217984 : Nat := 2165853184974130351901851

theorem tailTrace_4217984 : CollatzResearch.WordTrace tailWord_4217984 prefixEnd_4217984 2165853184974130351901851 := by
  unfold tailWord_4217984
  simp only [CollatzResearch.WordTrace]
  refine ⟨76921257575485908580190503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102561676767314544773587337 76921257575485908580190503)
  ·
    refine ⟨115381886363228862870285755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76921257575485908580190503 115381886363228862870285755)
    ·
      refine ⟨173072829544843294305428633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115381886363228862870285755 173072829544843294305428633)
      ·
        refine ⟨129804622158632470729071475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173072829544843294305428633 129804622158632470729071475)
        ·
          refine ⟨194706933237948706093607213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129804622158632470729071475 194706933237948706093607213)
          ·
            refine ⟨73015099964230764785102705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194706933237948706093607213 73015099964230764785102705)
            ·
              refine ⟨54761324973173073588827029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73015099964230764785102705 54761324973173073588827029)
              ·
                refine ⟨2566937108117487824476267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54761324973173073588827029 2566937108117487824476267)
                ·
                  refine ⟨3850405662176231736714401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2566937108117487824476267 3850405662176231736714401)
                  ·
                    refine ⟨2887804246632173802535801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3850405662176231736714401 2887804246632173802535801)
                    ·
                      refine ⟨2165853184974130351901851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887804246632173802535801 2165853184974130351901851)
                      ·
                        rfl

theorem cell23_4217984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 1, 2, 2].length) (baseStart_4217984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4217984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4217984 prefixEnd_4217984 := by exact prefixLift 4217984
  have htrace : WordTrace (prefixWord ++ tailWord_4217984) baseStart_4217984 baseEnd_4217984 := by
    simpa [prefixWord, tailWord_4217984, baseEnd_4217984] using wordTrace_append hprefix tailTrace_4217984
  have hstable : (prefixWord ++ tailWord_4217984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217984).length < 2 ^ (prefixWord ++ tailWord_4217984).sum := by decide
  have hdescent : baseEnd_4217984 < baseStart_4217984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218000 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 6, 1, 3]
def baseStart_4218000 : Nat := 118140960795 + 4218000 * 2 ^ 59
def prefixEnd_4218000 : Nat := 4983230072969 + 3 ^ 40 * 4218000 * 2
def baseEnd_4218000 : Nat := 2165861400664602289301777

theorem tailTrace_4218000 : CollatzResearch.WordTrace tailWord_4218000 prefixEnd_4218000 2165861400664602289301777 := by
  unfold tailWord_4218000
  simp only [CollatzResearch.WordTrace]
  refine ⟨76921549359456925946481727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102562065812609234595308969 76921549359456925946481727)
  ·
    refine ⟨115382324039185388919722591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76921549359456925946481727 115382324039185388919722591)
    ·
      refine ⟨173073486058778083379583887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115382324039185388919722591 173073486058778083379583887)
      ·
        refine ⟨259610229088167125069375831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173073486058778083379583887 259610229088167125069375831)
        ·
          refine ⟨389415343632250687604063747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259610229088167125069375831 389415343632250687604063747)
          ·
            refine ⟨584123015448376031406095621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389415343632250687604063747 584123015448376031406095621)
            ·
              refine ⟨109523065396570505888642929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 584123015448376031406095621 109523065396570505888642929)
              ·
                refine ⟨82142299047427879416482197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109523065396570505888642929 82142299047427879416482197)
                ·
                  refine ⟨3850420267848181847647603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82142299047427879416482197 3850420267848181847647603)
                  ·
                    refine ⟨5775630401772272771471405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3850420267848181847647603 5775630401772272771471405)
                    ·
                      refine ⟨2165861400664602289301777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5775630401772272771471405 2165861400664602289301777)
                      ·
                        rfl

theorem cell23_4218000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 6, 1, 3].length) (baseStart_4218000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218000 prefixEnd_4218000 := by exact prefixLift 4218000
  have htrace : WordTrace (prefixWord ++ tailWord_4218000) baseStart_4218000 baseEnd_4218000 := by
    simpa [prefixWord, tailWord_4218000, baseEnd_4218000] using wordTrace_append hprefix tailTrace_4218000
  have hstable : (prefixWord ++ tailWord_4218000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218000).length < 2 ^ (prefixWord ++ tailWord_4218000).sum := by decide
  have hdescent : baseEnd_4218000 < baseStart_4218000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218034 : List Nat := [3, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3]
def baseStart_4218034 : Nat := 118140960795 + 4218034 * 2 ^ 59
def prefixEnd_4218034 : Nat := 4983230072969 + 3 ^ 40 * 4218034 * 2
def baseEnd_4218034 : Nat := 2165878859006855156276621

theorem tailTrace_4218034 : CollatzResearch.WordTrace tailWord_4218034 prefixEnd_4218034 2165878859006855156276621 := by
  unfold tailWord_4218034
  simp only [CollatzResearch.WordTrace]
  refine ⟨38461084700197668924925289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102562892533860450466467437 38461084700197668924925289)
  ·
    refine ⟨28845813525148251693693967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38461084700197668924925289 28845813525148251693693967)
    ·
      refine ⟨43268720287722377540540951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28845813525148251693693967 43268720287722377540540951)
      ·
        refine ⟨64903080431583566310811427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43268720287722377540540951 64903080431583566310811427)
        ·
          refine ⟨97354620647375349466217141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64903080431583566310811427 97354620647375349466217141)
          ·
            refine ⟨9126995685691439012457857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97354620647375349466217141 9126995685691439012457857)
            ·
              refine ⟨6845246764268579259343393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9126995685691439012457857 6845246764268579259343393)
              ·
                refine ⟨5133935073201434444507545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6845246764268579259343393 5133935073201434444507545)
                ·
                  refine ⟨3850451304901075833380659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5133935073201434444507545 3850451304901075833380659)
                  ·
                    refine ⟨5775676957351613750070989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3850451304901075833380659 5775676957351613750070989)
                    ·
                      refine ⟨2165878859006855156276621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5775676957351613750070989 2165878859006855156276621)
                      ·
                        rfl

theorem cell23_4218034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_4218034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218034 prefixEnd_4218034 := by exact prefixLift 4218034
  have htrace : WordTrace (prefixWord ++ tailWord_4218034) baseStart_4218034 baseEnd_4218034 := by
    simpa [prefixWord, tailWord_4218034, baseEnd_4218034] using wordTrace_append hprefix tailTrace_4218034
  have hstable : (prefixWord ++ tailWord_4218034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218034).length < 2 ^ (prefixWord ++ tailWord_4218034).sum := by decide
  have hdescent : baseEnd_4218034 < baseStart_4218034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218043 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 5]
def baseStart_4218043 : Nat := 118140960795 + 4218043 * 2 ^ 59
def prefixEnd_4218043 : Nat := 4983230072969 + 3 ^ 40 * 4218043 * 2
def baseEnd_4218043 : Nat := 2165883480332745621064079

theorem tailTrace_4218043 : CollatzResearch.WordTrace tailWord_4218043 prefixEnd_4218043 2165883480332745621064079 := by
  unfold tailWord_4218043
  simp only [CollatzResearch.WordTrace]
  refine ⟨153844667057758070236778783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102563111371838713491185855 153844667057758070236778783)
  ·
    refine ⟨230767000586637105355168175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153844667057758070236778783 230767000586637105355168175)
    ·
      refine ⟨346150500879955658032752263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230767000586637105355168175 346150500879955658032752263)
      ·
        refine ⟨519225751319933487049128395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346150500879955658032752263 519225751319933487049128395)
        ·
          refine ⟨778838626979900230573692593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519225751319933487049128395 778838626979900230573692593)
          ·
            refine ⟨584128970234925172930269445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 778838626979900230573692593 584128970234925172930269445)
            ·
              refine ⟨109524181919048469924425521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 584128970234925172930269445 109524181919048469924425521)
              ·
                refine ⟨82143136439286352443319141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109524181919048469924425521 82143136439286352443319141)
                ·
                  refine ⟨15401838082366191083122339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82143136439286352443319141 15401838082366191083122339)
                  ·
                    refine ⟨23102757123549286624683509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15401838082366191083122339 23102757123549286624683509)
                    ·
                      refine ⟨2165883480332745621064079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23102757123549286624683509 2165883480332745621064079)
                      ·
                        rfl

theorem cell23_4218043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 5].length) (baseStart_4218043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218043 prefixEnd_4218043 := by exact prefixLift 4218043
  have htrace : WordTrace (prefixWord ++ tailWord_4218043) baseStart_4218043 baseEnd_4218043 := by
    simpa [prefixWord, tailWord_4218043, baseEnd_4218043] using wordTrace_append hprefix tailTrace_4218043
  have hstable : (prefixWord ++ tailWord_4218043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218043).length < 2 ^ (prefixWord ++ tailWord_4218043).sum := by decide
  have hdescent : baseEnd_4218043 < baseStart_4218043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218073 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 7]
def baseStart_4218073 : Nat := 118140960795 + 4218073 * 2 ^ 59
def prefixEnd_4218073 : Nat := 4983230072969 + 3 ^ 40 * 4218073 * 2
def baseEnd_4218073 : Nat := 2165898884752380503688941

theorem tailTrace_4218073 : CollatzResearch.WordTrace tailWord_4218073 prefixEnd_4218073 2165898884752380503688941 := by
  unfold tailWord_4218073
  simp only [CollatzResearch.WordTrace]
  refine ⟨153845761247649385360370873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102563840831766256906913915 153845761247649385360370873)
  ·
    refine ⟨115384320935737039020278155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153845761247649385360370873 115384320935737039020278155)
    ·
      refine ⟨173076481403605558530417233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115384320935737039020278155 173076481403605558530417233)
      ·
        refine ⟨129807361052704168897812925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173076481403605558530417233 129807361052704168897812925)
        ·
          refine ⟨48677760394764063336679847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129807361052704168897812925 48677760394764063336679847)
          ·
            refine ⟨73016640592146095005019771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48677760394764063336679847 73016640592146095005019771)
            ·
              refine ⟨109524960888219142507529657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73016640592146095005019771 109524960888219142507529657)
              ·
                refine ⟨82143720666164356880647243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109524960888219142507529657 82143720666164356880647243)
                ·
                  refine ⟨123215580999246535320970865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82143720666164356880647243 123215580999246535320970865)
                  ·
                    refine ⟨92411685749434901490728149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 123215580999246535320970865 92411685749434901490728149)
                    ·
                      refine ⟨2165898884752380503688941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92411685749434901490728149 2165898884752380503688941)
                      ·
                        rfl

theorem cell23_4218073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_4218073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218073 prefixEnd_4218073 := by exact prefixLift 4218073
  have htrace : WordTrace (prefixWord ++ tailWord_4218073) baseStart_4218073 baseEnd_4218073 := by
    simpa [prefixWord, tailWord_4218073, baseEnd_4218073] using wordTrace_append hprefix tailTrace_4218073
  have hstable : (prefixWord ++ tailWord_4218073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218073).length < 2 ^ (prefixWord ++ tailWord_4218073).sum := by decide
  have hdescent : baseEnd_4218073 < baseStart_4218073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218091 : List Nat := [1, 1, 1, 1, 2, 8, 1, 2, 2, 2, 2]
def baseStart_4218091 : Nat := 118140960795 + 4218091 * 2 ^ 59
def prefixEnd_4218091 : Nat := 4983230072969 + 3 ^ 40 * 4218091 * 2
def baseEnd_4218091 : Nat := 2165908127404161433263859

theorem tailTrace_4218091 : CollatzResearch.WordTrace tailWord_4218091 prefixEnd_4218091 2165908127404161433263859 := by
  unfold tailWord_4218091
  simp only [CollatzResearch.WordTrace]
  refine ⟨153846417761584174434526127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102564278507722782956350751 153846417761584174434526127)
  ·
    refine ⟨230769626642376261651789191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153846417761584174434526127 230769626642376261651789191)
    ·
      refine ⟨346154439963564392477683787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230769626642376261651789191 346154439963564392477683787)
      ·
        refine ⟨519231659945346588716525681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346154439963564392477683787 519231659945346588716525681)
        ·
          refine ⟨389423744959009941537394261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 519231659945346588716525681 389423744959009941537394261)
          ·
            refine ⟨4563559511238397752391339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 389423744959009941537394261 4563559511238397752391339)
            ·
              refine ⟨6845339266857596628587009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4563559511238397752391339 6845339266857596628587009)
              ·
                refine ⟨5134004450143197471440257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6845339266857596628587009 5134004450143197471440257)
                ·
                  refine ⟨3850503337607398103580193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5134004450143197471440257 3850503337607398103580193)
                  ·
                    refine ⟨2887877503205548577685145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3850503337607398103580193 2887877503205548577685145)
                    ·
                      refine ⟨2165908127404161433263859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887877503205548577685145 2165908127404161433263859)
                      ·
                        rfl

theorem cell23_4218091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 2, 2].length) (baseStart_4218091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218091 prefixEnd_4218091 := by exact prefixLift 4218091
  have htrace : WordTrace (prefixWord ++ tailWord_4218091) baseStart_4218091 baseEnd_4218091 := by
    simpa [prefixWord, tailWord_4218091, baseEnd_4218091] using wordTrace_append hprefix tailTrace_4218091
  have hstable : (prefixWord ++ tailWord_4218091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218091).length < 2 ^ (prefixWord ++ tailWord_4218091).sum := by decide
  have hdescent : baseEnd_4218091 < baseStart_4218091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218108 : List Nat := [2, 2, 2, 1, 5, 1, 3, 1, 2, 2, 2]
def baseStart_4218108 : Nat := 118140960795 + 4218108 * 2 ^ 59
def prefixEnd_4218108 : Nat := 4983230072969 + 3 ^ 40 * 4218108 * 2
def baseEnd_4218108 : Nat := 2165916856575287866751281

theorem tailTrace_4218108 : CollatzResearch.WordTrace tailWord_4218108 prefixEnd_4218108 2165916856575287866751281 := by
  unfold tailWord_4218108
  simp only [CollatzResearch.WordTrace]
  refine ⟨76923518901261293168947489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102564691868348390891929985 76923518901261293168947489)
  ·
    refine ⟨57692639175945969876710617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76923518901261293168947489 57692639175945969876710617)
    ·
      refine ⟨43269479381959477407532963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57692639175945969876710617 43269479381959477407532963)
      ·
        refine ⟨64904219072939216111299445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43269479381959477407532963 64904219072939216111299445)
        ·
          refine ⟨6084770538088051510434323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64904219072939216111299445 6084770538088051510434323)
          ·
            refine ⟨9127155807132077265651485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6084770538088051510434323 9127155807132077265651485)
            ·
              refine ⟨3422683427674528974619307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9127155807132077265651485 3422683427674528974619307)
              ·
                refine ⟨5134025141511793461928961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3422683427674528974619307 5134025141511793461928961)
                ·
                  refine ⟨3850518856133845096446721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5134025141511793461928961 3850518856133845096446721)
                  ·
                    refine ⟨2887889142100383822335041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3850518856133845096446721 2887889142100383822335041)
                    ·
                      refine ⟨2165916856575287866751281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887889142100383822335041 2165916856575287866751281)
                      ·
                        rfl

theorem cell23_4218108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_4218108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218108 prefixEnd_4218108 := by exact prefixLift 4218108
  have htrace : WordTrace (prefixWord ++ tailWord_4218108) baseStart_4218108 baseEnd_4218108 := by
    simpa [prefixWord, tailWord_4218108, baseEnd_4218108] using wordTrace_append hprefix tailTrace_4218108
  have hstable : (prefixWord ++ tailWord_4218108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218108).length < 2 ^ (prefixWord ++ tailWord_4218108).sum := by decide
  have hdescent : baseEnd_4218108 < baseStart_4218108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218147 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 4]
def baseStart_4218147 : Nat := 118140960795 + 4218147 * 2 ^ 59
def prefixEnd_4218147 : Nat := 4983230072969 + 3 ^ 40 * 4218147 * 2
def baseEnd_4218147 : Nat := 2165936882320813214163601

theorem tailTrace_4218147 : CollatzResearch.WordTrace tailWord_4218147 prefixEnd_4218147 2165936882320813214163601 := by
  unfold tailWord_4218147
  simp only [CollatzResearch.WordTrace]
  refine ⟨153848460249381295998564695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102565640166254197332376463 153848460249381295998564695)
  ·
    refine ⟨230772690374071943997847043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153848460249381295998564695 230772690374071943997847043)
    ·
      refine ⟨346159035561107915996770565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230772690374071943997847043 346159035561107915996770565)
      ·
        refine ⟨64904819167707734249394481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 346159035561107915996770565 64904819167707734249394481)
        ·
          refine ⟨48678614375780800687045861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64904819167707734249394481 48678614375780800687045861)
          ·
            refine ⟨9127240195458900128821099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48678614375780800687045861 9127240195458900128821099)
            ·
              refine ⟨13690860293188350193231649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9127240195458900128821099 13690860293188350193231649)
              ·
                refine ⟨10268145219891262644923737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13690860293188350193231649 10268145219891262644923737)
                ·
                  refine ⟨7701108914918446983692803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10268145219891262644923737 7701108914918446983692803)
                  ·
                    refine ⟨11551663372377670475539205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7701108914918446983692803 11551663372377670475539205)
                    ·
                      refine ⟨2165936882320813214163601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11551663372377670475539205 2165936882320813214163601)
                      ·
                        rfl

theorem cell23_4218147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_4218147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218147 prefixEnd_4218147 := by exact prefixLift 4218147
  have htrace : WordTrace (prefixWord ++ tailWord_4218147) baseStart_4218147 baseEnd_4218147 := by
    simpa [prefixWord, tailWord_4218147, baseEnd_4218147] using wordTrace_append hprefix tailTrace_4218147
  have hstable : (prefixWord ++ tailWord_4218147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218147).length < 2 ^ (prefixWord ++ tailWord_4218147).sum := by decide
  have hdescent : baseEnd_4218147 < baseStart_4218147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218164 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_4218164 : Nat := 118140960795 + 4218164 * 2 ^ 59
def prefixEnd_4218164 : Nat := 4983230072969 + 3 ^ 40 * 4218164 * 2
def baseEnd_4218164 : Nat := 2165945611491939647651023

theorem tailTrace_4218164 : CollatzResearch.WordTrace tailWord_4218164 prefixEnd_4218164 2165945611491939647651023 := by
  unfold tailWord_4218164
  simp only [CollatzResearch.WordTrace]
  refine ⟨76924540145159853950966773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102566053526879805267955697 76924540145159853950966773)
  ·
    refine ⟨7211675638608736307903135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76924540145159853950966773 7211675638608736307903135)
    ·
      refine ⟨10817513457913104461854703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7211675638608736307903135 10817513457913104461854703)
      ·
        refine ⟨16226270186869656692782055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10817513457913104461854703 16226270186869656692782055)
        ·
          refine ⟨24339405280304485039173083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16226270186869656692782055 24339405280304485039173083)
          ·
            refine ⟨36509107920456727558759625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24339405280304485039173083 36509107920456727558759625)
            ·
              refine ⟨27381830940342545669069719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36509107920456727558759625 27381830940342545669069719)
              ·
                refine ⟨41072746410513818503604579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27381830940342545669069719 41072746410513818503604579)
                ·
                  refine ⟨61609119615770727755406869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41072746410513818503604579 61609119615770727755406869)
                  ·
                    refine ⟨2887927481989252863534697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61609119615770727755406869 2887927481989252863534697)
                    ·
                      refine ⟨2165945611491939647651023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887927481989252863534697 2165945611491939647651023)
                      ·
                        rfl

theorem cell23_4218164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_4218164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218164 prefixEnd_4218164 := by exact prefixLift 4218164
  have htrace : WordTrace (prefixWord ++ tailWord_4218164) baseStart_4218164 baseEnd_4218164 := by
    simpa [prefixWord, tailWord_4218164, baseEnd_4218164] using wordTrace_append hprefix tailTrace_4218164
  have hstable : (prefixWord ++ tailWord_4218164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218164).length < 2 ^ (prefixWord ++ tailWord_4218164).sum := by decide
  have hdescent : baseEnd_4218164 < baseStart_4218164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218207 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 3, 5, 2]
def baseStart_4218207 : Nat := 118140960795 + 4218207 * 2 ^ 59
def prefixEnd_4218207 : Nat := 4983230072969 + 3 ^ 40 * 4218207 * 2
def baseEnd_4218207 : Nat := 2165967691160082979413325

theorem tailTrace_4218207 : CollatzResearch.WordTrace tailWord_4218207 prefixEnd_4218207 2165967691160082979413325 := by
  unfold tailWord_4218207
  simp only [CollatzResearch.WordTrace]
  refine ⟨153850648629163926245748875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102567099086109284163832583 153850648629163926245748875)
  ·
    refine ⟨230775972943745889368623313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153850648629163926245748875 230775972943745889368623313)
    ·
      refine ⟨173081979707809417026467485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230775972943745889368623313 173081979707809417026467485)
      ·
        refine ⟨64905742390428531384925307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173081979707809417026467485 64905742390428531384925307)
        ·
          refine ⟨97358613585642797077387961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64905742390428531384925307 97358613585642797077387961)
          ·
            refine ⟨73018960189232097808040971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97358613585642797077387961 73018960189232097808040971)
            ·
              refine ⟨109528440283848146712061457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73018960189232097808040971 109528440283848146712061457)
              ·
                refine ⟨82146330212886110034046093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109528440283848146712061457 82146330212886110034046093)
                ·
                  refine ⟨30804873829832291262767285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82146330212886110034046093 30804873829832291262767285)
                  ·
                    refine ⟨2887956921546777305884433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30804873829832291262767285 2887956921546777305884433)
                    ·
                      refine ⟨2165967691160082979413325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887956921546777305884433 2165967691160082979413325)
                      ·
                        rfl

theorem cell23_4218207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_4218207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218207 prefixEnd_4218207 := by exact prefixLift 4218207
  have htrace : WordTrace (prefixWord ++ tailWord_4218207) baseStart_4218207 baseEnd_4218207 := by
    simpa [prefixWord, tailWord_4218207, baseEnd_4218207] using wordTrace_append hprefix tailTrace_4218207
  have hstable : (prefixWord ++ tailWord_4218207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218207).length < 2 ^ (prefixWord ++ tailWord_4218207).sum := by decide
  have hdescent : baseEnd_4218207 < baseStart_4218207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218208 : List Nat := [2, 1, 1, 3, 4, 3, 2, 2, 1, 4]
def baseStart_4218208 : Nat := 118140960795 + 4218208 * 2 ^ 59
def prefixEnd_4218208 : Nat := 4983230072969 + 3 ^ 40 * 4218208 * 2
def baseEnd_4218208 : Nat := 721989401546912491833607

theorem tailTrace_4218208 : CollatzResearch.WordTrace tailWord_4218208 prefixEnd_4218208 721989401546912491833607 := by
  unfold tailWord_4218208
  simp only [CollatzResearch.WordTrace]
  refine ⟨76925342551080151708267639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102567123401440202277690185 76925342551080151708267639)
  ·
    refine ⟨115388013826620227562401459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76925342551080151708267639 115388013826620227562401459)
    ·
      refine ⟨173082020739930341343602189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115388013826620227562401459 173082020739930341343602189)
      ·
        refine ⟨64905757777473878003850821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173082020739930341343602189 64905757777473878003850821)
        ·
          refine ⟨12169829583276352125722029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64905757777473878003850821 12169829583276352125722029)
          ·
            refine ⟨4563686093728632047145761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12169829583276352125722029 4563686093728632047145761)
            ·
              refine ⟨3422764570296474035359321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4563686093728632047145761 3422764570296474035359321)
              ·
                refine ⟨2567073427722355526519491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3422764570296474035359321 2567073427722355526519491)
                ·
                  refine ⟨3850610141583533289779237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2567073427722355526519491 3850610141583533289779237)
                  ·
                    refine ⟨721989401546912491833607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3850610141583533289779237 721989401546912491833607)
                    ·
                      rfl

theorem cell23_4218208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 1, 4].length) (baseStart_4218208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218208 prefixEnd_4218208 := by exact prefixLift 4218208
  have htrace : WordTrace (prefixWord ++ tailWord_4218208) baseStart_4218208 baseEnd_4218208 := by
    simpa [prefixWord, tailWord_4218208, baseEnd_4218208] using wordTrace_append hprefix tailTrace_4218208
  have hstable : (prefixWord ++ tailWord_4218208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218208).length < 2 ^ (prefixWord ++ tailWord_4218208).sum := by decide
  have hdescent : baseEnd_4218208 < baseStart_4218208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218237 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_4218237 : Nat := 118140960795 + 4218237 * 2 ^ 59
def prefixEnd_4218237 : Nat := 4983230072969 + 3 ^ 40 * 4218237 * 2
def baseEnd_4218237 : Nat := 2165983095579717862038187

theorem tailTrace_4218237 : CollatzResearch.WordTrace tailWord_4218237 prefixEnd_4218237 2165983095579717862038187 := by
  unfold tailWord_4218237
  simp only [CollatzResearch.WordTrace]
  refine ⟨153851742819055241369340965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102567828546036827579560643 153851742819055241369340965)
  ·
    refine ⟨28847201778572857756751431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153851742819055241369340965 28847201778572857756751431)
    ·
      refine ⟨43270802667859286635127147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28847201778572857756751431 43270802667859286635127147)
      ·
        refine ⟨64906204001788929952690721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43270802667859286635127147 64906204001788929952690721)
        ·
          refine ⟨48679653001341697464518041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64906204001788929952690721 48679653001341697464518041)
          ·
            refine ⟨36509739751006273098388531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48679653001341697464518041 36509739751006273098388531)
            ·
              refine ⟨54764609626509409647582797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36509739751006273098388531 54764609626509409647582797)
              ·
                refine ⟨20536728609941028617843549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54764609626509409647582797 20536728609941028617843549)
                ·
                  refine ⟨7701273228727885731691331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20536728609941028617843549 7701273228727885731691331)
                  ·
                    refine ⟨11551909843091828597536997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7701273228727885731691331 11551909843091828597536997)
                    ·
                      refine ⟨2165983095579717862038187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11551909843091828597536997 2165983095579717862038187)
                      ·
                        rfl

theorem cell23_4218237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_4218237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218237 prefixEnd_4218237 := by exact prefixLift 4218237
  have htrace : WordTrace (prefixWord ++ tailWord_4218237) baseStart_4218237 baseEnd_4218237 := by
    simpa [prefixWord, tailWord_4218237, baseEnd_4218237] using wordTrace_append hprefix tailTrace_4218237
  have hstable : (prefixWord ++ tailWord_4218237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218237).length < 2 ^ (prefixWord ++ tailWord_4218237).sum := by decide
  have hdescent : baseEnd_4218237 < baseStart_4218237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218241 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_4218241 : Nat := 118140960795 + 4218241 * 2 ^ 59
def prefixEnd_4218241 : Nat := 4983230072969 + 3 ^ 40 * 4218241 * 2
def baseEnd_4218241 : Nat := 2165985149502335846388169

theorem tailTrace_4218241 : CollatzResearch.WordTrace tailWord_4218241 prefixEnd_4218241 2165985149502335846388169 := by
  unfold tailWord_4218241
  simp only [CollatzResearch.WordTrace]
  refine ⟨153851888711040750052486577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102567925807360500034991051 153851888711040750052486577)
  ·
    refine ⟨115388916533280562539364933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153851888711040750052486577 115388916533280562539364933)
    ·
      refine ⟨21635421849990105476130925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115388916533280562539364933 21635421849990105476130925)
      ·
        refine ⟨8113283193746289553549097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21635421849990105476130925 8113283193746289553549097)
        ·
          refine ⟨6084962395309717165161823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8113283193746289553549097 6084962395309717165161823)
          ·
            refine ⟨9127443592964575747742735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6084962395309717165161823 9127443592964575747742735)
            ·
              refine ⟨13691165389446863621614103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9127443592964575747742735 13691165389446863621614103)
              ·
                refine ⟨20536748084170295432421155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13691165389446863621614103 20536748084170295432421155)
                ·
                  refine ⟨30805122126255443148631733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20536748084170295432421155 30805122126255443148631733)
                  ·
                    refine ⟨2887980199336447795184225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30805122126255443148631733 2887980199336447795184225)
                    ·
                      refine ⟨2165985149502335846388169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2887980199336447795184225 2165985149502335846388169)
                      ·
                        rfl

theorem cell23_4218241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_4218241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218241 prefixEnd_4218241 := by exact prefixLift 4218241
  have htrace : WordTrace (prefixWord ++ tailWord_4218241) baseStart_4218241 baseEnd_4218241 := by
    simpa [prefixWord, tailWord_4218241, baseEnd_4218241] using wordTrace_append hprefix tailTrace_4218241
  have hstable : (prefixWord ++ tailWord_4218241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218241).length < 2 ^ (prefixWord ++ tailWord_4218241).sum := by decide
  have hdescent : baseEnd_4218241 < baseStart_4218241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218247 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 1, 6]
def baseStart_4218247 : Nat := 118140960795 + 4218247 * 2 ^ 59
def prefixEnd_4218247 : Nat := 4983230072969 + 3 ^ 40 * 4218247 * 2
def baseEnd_4218247 : Nat := 721996076795420940971047

theorem tailTrace_4218247 : CollatzResearch.WordTrace tailWord_4218247 prefixEnd_4218247 721996076795420940971047 := by
  unfold tailWord_4218247
  simp only [CollatzResearch.WordTrace]
  refine ⟨153852107549019013077204995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102568071699346008718136663 153852107549019013077204995)
  ·
    refine ⟨230778161323528519615807493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153852107549019013077204995 230778161323528519615807493)
    ·
      refine ⟨43270905248161597427963905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230778161323528519615807493 43270905248161597427963905)
      ·
        refine ⟨32453178936121198070972929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43270905248161597427963905 32453178936121198070972929)
        ·
          refine ⟨24339884202090898553229697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32453178936121198070972929 24339884202090898553229697)
          ·
            refine ⟨18254913151568173914922273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24339884202090898553229697 18254913151568173914922273)
            ·
              refine ⟨13691184863676130436191705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18254913151568173914922273 13691184863676130436191705)
              ·
                refine ⟨10268388647757097827143779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13691184863676130436191705 10268388647757097827143779)
                ·
                  refine ⟨15402582971635646740715669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10268388647757097827143779 15402582971635646740715669)
                  ·
                    refine ⟨721996076795420940971047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15402582971635646740715669 721996076795420940971047)
                    ·
                      rfl

theorem cell23_4218247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_4218247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218247 prefixEnd_4218247 := by exact prefixLift 4218247
  have htrace : WordTrace (prefixWord ++ tailWord_4218247) baseStart_4218247 baseEnd_4218247 := by
    simpa [prefixWord, tailWord_4218247, baseEnd_4218247] using wordTrace_append hprefix tailTrace_4218247
  have hstable : (prefixWord ++ tailWord_4218247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218247).length < 2 ^ (prefixWord ++ tailWord_4218247).sum := by decide
  have hdescent : baseEnd_4218247 < baseStart_4218247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218248 : List Nat := [2, 1, 3, 3, 1, 3, 2, 3, 1, 1, 3]
def baseStart_4218248 : Nat := 118140960795 + 4218248 * 2 ^ 59
def prefixEnd_4218248 : Nat := 4983230072969 + 3 ^ 40 * 4218248 * 2
def baseEnd_4218248 : Nat := 2165988743866917319000637

theorem tailTrace_4218248 : CollatzResearch.WordTrace tailWord_4218248 prefixEnd_4218248 2165988743866917319000637 := by
  unfold tailWord_4218248
  simp only [CollatzResearch.WordTrace]
  refine ⟨76926072011007695123995699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102568096014676926831994265 76926072011007695123995699)
  ·
    refine ⟨115389108016511542685993549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76926072011007695123995699 115389108016511542685993549)
    ·
      refine ⟨43270915506191828507247581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115389108016511542685993549 43270915506191828507247581)
      ·
        refine ⟨16226593314821935690217843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43270915506191828507247581 16226593314821935690217843)
        ·
          refine ⟨24339889972232903535326765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16226593314821935690217843 24339889972232903535326765)
          ·
            refine ⟨9127458739587338825747537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24339889972232903535326765 9127458739587338825747537)
            ·
              refine ⟨6845594054690504119310653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9127458739587338825747537 6845594054690504119310653)
              ·
                refine ⟨2567097770508939044741495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6845594054690504119310653 2567097770508939044741495)
                ·
                  refine ⟨3850646655763408567112243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2567097770508939044741495 3850646655763408567112243)
                  ·
                    refine ⟨5775969983645112850668365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3850646655763408567112243 5775969983645112850668365)
                    ·
                      refine ⟨2165988743866917319000637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5775969983645112850668365 2165988743866917319000637)
                      ·
                        rfl

theorem cell23_4218248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_4218248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218248 prefixEnd_4218248 := by exact prefixLift 4218248
  have htrace : WordTrace (prefixWord ++ tailWord_4218248) baseStart_4218248 baseEnd_4218248 := by
    simpa [prefixWord, tailWord_4218248, baseEnd_4218248] using wordTrace_append hprefix tailTrace_4218248
  have hstable : (prefixWord ++ tailWord_4218248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218248).length < 2 ^ (prefixWord ++ tailWord_4218248).sum := by decide
  have hdescent : baseEnd_4218248 < baseStart_4218248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218271 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 3, 2, 2]
def baseStart_4218271 : Nat := 118140960795 + 4218271 * 2 ^ 59
def prefixEnd_4218271 : Nat := 4983230072969 + 3 ^ 40 * 4218271 * 2
def baseEnd_4218271 : Nat := 2166000553921970729013031

theorem tailTrace_4218271 : CollatzResearch.WordTrace tailWord_4218271 prefixEnd_4218271 2166000553921970729013031 := by
  unfold tailWord_4218271
  simp only [CollatzResearch.WordTrace]
  refine ⟨153852982900932065176078667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102568655267288043450719111 153852982900932065176078667)
  ·
    refine ⟨230779474351398097764118001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153852982900932065176078667 230779474351398097764118001)
    ·
      refine ⟨173084605763548573323088501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230779474351398097764118001 173084605763548573323088501)
      ·
        refine ⟨16226681790332678749039547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 173084605763548573323088501 16226681790332678749039547)
        ·
          refine ⟨24340022685499018123559321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16226681790332678749039547 24340022685499018123559321)
          ·
            refine ⟨18255017014124263592669491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24340022685499018123559321 18255017014124263592669491)
            ·
              refine ⟨27382525521186395389004237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18255017014124263592669491 27382525521186395389004237)
              ·
                refine ⟨10268447070444898270876589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27382525521186395389004237 10268447070444898270876589)
                ·
                  refine ⟨3850667651416836851578721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10268447070444898270876589 3850667651416836851578721)
                  ·
                    refine ⟨2888000738562627638684041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3850667651416836851578721 2888000738562627638684041)
                    ·
                      refine ⟨2166000553921970729013031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2888000738562627638684041 2166000553921970729013031)
                      ·
                        rfl

theorem cell23_4218271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_4218271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218271 prefixEnd_4218271 := by exact prefixLift 4218271
  have htrace : WordTrace (prefixWord ++ tailWord_4218271) baseStart_4218271 baseEnd_4218271 := by
    simpa [prefixWord, tailWord_4218271, baseEnd_4218271] using wordTrace_append hprefix tailTrace_4218271
  have hstable : (prefixWord ++ tailWord_4218271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218271).length < 2 ^ (prefixWord ++ tailWord_4218271).sum := by decide
  have hdescent : baseEnd_4218271 < baseStart_4218271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218274 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_4218274 : Nat := 118140960795 + 4218274 * 2 ^ 59
def prefixEnd_4218274 : Nat := 4983230072969 + 3 ^ 40 * 4218274 * 2
def baseEnd_4218274 : Nat := 2166002094363934217275517

theorem tailTrace_4218274 : CollatzResearch.WordTrace tailWord_4218274 prefixEnd_4218274 2166002094363934217275517 := by
  unfold tailWord_4218274
  simp only [CollatzResearch.WordTrace]
  refine ⟨38463273079980299172109469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102568728213280797792291917 38463273079980299172109469)
  ·
    refine ⟨14423727404992612189541051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38463273079980299172109469 14423727404992612189541051)
    ·
      refine ⟨21635591107488918284311577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14423727404992612189541051 21635591107488918284311577)
      ·
        refine ⟨16226693330616688713233683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21635591107488918284311577 16226693330616688713233683)
        ·
          refine ⟨24340039995925033069850525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16226693330616688713233683 24340039995925033069850525)
          ·
            refine ⟨9127514998471887401193947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24340039995925033069850525 9127514998471887401193947)
            ·
              refine ⟨13691272497707831101790921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9127514998471887401193947 13691272497707831101790921)
              ·
                refine ⟨10268454373280873326343191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13691272497707831101790921 10268454373280873326343191)
                ·
                  refine ⟨15402681559921309989514787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10268454373280873326343191 15402681559921309989514787)
                  ·
                    refine ⟨23104022339881964984272181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15402681559921309989514787 23104022339881964984272181)
                    ·
                      refine ⟨2166002094363934217275517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23104022339881964984272181 2166002094363934217275517)
                      ·
                        rfl

theorem cell23_4218274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_4218274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218274 prefixEnd_4218274 := by exact prefixLift 4218274
  have htrace : WordTrace (prefixWord ++ tailWord_4218274) baseStart_4218274 baseEnd_4218274 := by
    simpa [prefixWord, tailWord_4218274, baseEnd_4218274] using wordTrace_append hprefix tailTrace_4218274
  have hstable : (prefixWord ++ tailWord_4218274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218274).length < 2 ^ (prefixWord ++ tailWord_4218274).sum := by decide
  have hdescent : baseEnd_4218274 < baseStart_4218274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218304 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 4, 1, 3]
def baseStart_4218304 : Nat := 118140960795 + 4218304 * 2 ^ 59
def prefixEnd_4218304 : Nat := 4983230072969 + 3 ^ 40 * 4218304 * 2
def baseEnd_4218304 : Nat := 2166017498783569099900379

theorem tailTrace_4218304 : CollatzResearch.WordTrace tailWord_4218304 prefixEnd_4218304 2166017498783569099900379 := by
  unfold tailWord_4218304
  simp only [CollatzResearch.WordTrace]
  refine ⟨76927093254906255906014983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102569457673208341208019977 76927093254906255906014983)
  ·
    refine ⟨115390639882359383859022475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76927093254906255906014983 115390639882359383859022475)
    ·
      refine ⟨173085959823539075788533713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115390639882359383859022475 173085959823539075788533713)
      ·
        refine ⟨129814469867654306841400285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173085959823539075788533713 129814469867654306841400285)
        ·
          refine ⟨48680426200370365065525107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129814469867654306841400285 48680426200370365065525107)
          ·
            refine ⟨73020639300555547598287661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48680426200370365065525107 73020639300555547598287661)
            ·
              refine ⟨27382739737708330349357873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73020639300555547598287661 27382739737708330349357873)
              ·
                refine ⟨20537054803281247762018405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27382739737708330349357873 20537054803281247762018405)
                ·
                  refine ⟨3850697775615233955378451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20537054803281247762018405 3850697775615233955378451)
                  ·
                    refine ⟨5776046663422850933067677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3850697775615233955378451 5776046663422850933067677)
                    ·
                      refine ⟨2166017498783569099900379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5776046663422850933067677 2166017498783569099900379)
                      ·
                        rfl

theorem cell23_4218304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_4218304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218304 prefixEnd_4218304 := by exact prefixLift 4218304
  have htrace : WordTrace (prefixWord ++ tailWord_4218304) baseStart_4218304 baseEnd_4218304 := by
    simpa [prefixWord, tailWord_4218304, baseEnd_4218304] using wordTrace_append hprefix tailTrace_4218304
  have hstable : (prefixWord ++ tailWord_4218304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218304).length < 2 ^ (prefixWord ++ tailWord_4218304).sum := by decide
  have hdescent : baseEnd_4218304 < baseStart_4218304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218347 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 3]
def baseStart_4218347 : Nat := 118140960795 + 4218347 * 2 ^ 59
def prefixEnd_4218347 : Nat := 4983230072969 + 3 ^ 40 * 4218347 * 2
def baseEnd_4218347 : Nat := 2166039578451712431662681

theorem tailTrace_4218347 : CollatzResearch.WordTrace tailWord_4218347 prefixEnd_4218347 2166039578451712431662681 := by
  unfold tailWord_4218347
  simp only [CollatzResearch.WordTrace]
  refine ⟨153855754848656730155845295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102570503232437820103896863 153855754848656730155845295)
  ·
    refine ⟨230783632272985095233767943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153855754848656730155845295 230783632272985095233767943)
    ·
      refine ⟨346175448409477642850651915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230783632272985095233767943 346175448409477642850651915)
      ·
        refine ⟨519263172614216464275977873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346175448409477642850651915 519263172614216464275977873)
        ·
          refine ⟨389447379460662348206983405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 519263172614216464275977873 389447379460662348206983405)
          ·
            refine ⟨146042767297748380577618777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 389447379460662348206983405 146042767297748380577618777)
            ·
              refine ⟨109532075473311285433214083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146042767297748380577618777 109532075473311285433214083)
              ·
                refine ⟨164298113209966928149821125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109532075473311285433214083 164298113209966928149821125)
                ·
                  refine ⟨30805896226868799028091461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164298113209966928149821125 30805896226868799028091461)
                  ·
                    refine ⟨5776105542537899817767149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30805896226868799028091461 5776105542537899817767149)
                    ·
                      refine ⟨2166039578451712431662681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5776105542537899817767149 2166039578451712431662681)
                      ·
                        rfl

theorem cell23_4218347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 3].length) (baseStart_4218347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218347 prefixEnd_4218347 := by exact prefixLift 4218347
  have htrace : WordTrace (prefixWord ++ tailWord_4218347) baseStart_4218347 baseEnd_4218347 := by
    simpa [prefixWord, tailWord_4218347, baseEnd_4218347] using wordTrace_append hprefix tailTrace_4218347
  have hstable : (prefixWord ++ tailWord_4218347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218347).length < 2 ^ (prefixWord ++ tailWord_4218347).sum := by decide
  have hdescent : baseEnd_4218347 < baseStart_4218347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218378 : List Nat := [3, 1, 2, 2, 2, 2, 1, 4, 2, 2, 2]
def baseStart_4218378 : Nat := 118140960795 + 4218378 * 2 ^ 59
def prefixEnd_4218378 : Nat := 4983230072969 + 3 ^ 40 * 4218378 * 2
def baseEnd_4218378 : Nat := 2166055496352001810375039

theorem tailTrace_4218378 : CollatzResearch.WordTrace tailWord_4218378 prefixEnd_4218378 2166055496352001810375039 := by
  unfold tailWord_4218378
  simp only [CollatzResearch.WordTrace]
  refine ⟨38464221377886105612555947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102571257007696281633482525 38464221377886105612555947)
  ·
    refine ⟨57696332066829158418833921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38464221377886105612555947 57696332066829158418833921)
    ·
      refine ⟨43272249050121868814125441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57696332066829158418833921 43272249050121868814125441)
      ·
        refine ⟨32454186787591401610594081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43272249050121868814125441 32454186787591401610594081)
        ·
          refine ⟨24340640090693551207945561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32454186787591401610594081 24340640090693551207945561)
          ·
            refine ⟨18255480068020163405959171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24340640090693551207945561 18255480068020163405959171)
            ·
              refine ⟨27383220102030245108938757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18255480068020163405959171 27383220102030245108938757)
              ·
                refine ⟨5134353769130670957926017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27383220102030245108938757 5134353769130670957926017)
                ·
                  refine ⟨3850765326848003218444513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5134353769130670957926017 3850765326848003218444513)
                  ·
                    refine ⟨2888073995136002413833385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3850765326848003218444513 2888073995136002413833385)
                    ·
                      refine ⟨2166055496352001810375039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2888073995136002413833385 2166055496352001810375039)
                      ·
                        rfl

theorem cell23_4218378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_4218378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218378 prefixEnd_4218378 := by exact prefixLift 4218378
  have htrace : WordTrace (prefixWord ++ tailWord_4218378) baseStart_4218378 baseEnd_4218378 := by
    simpa [prefixWord, tailWord_4218378, baseEnd_4218378] using wordTrace_append hprefix tailTrace_4218378
  have hstable : (prefixWord ++ tailWord_4218378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218378).length < 2 ^ (prefixWord ++ tailWord_4218378).sum := by decide
  have hdescent : baseEnd_4218378 < baseStart_4218378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218447 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 6]
def baseStart_4218447 : Nat := 118140960795 + 4218447 * 2 ^ 59
def prefixEnd_4218447 : Nat := 4983230072969 + 3 ^ 40 * 4218447 * 2
def baseEnd_4218447 : Nat := 2166090926517162040412221

theorem tailTrace_4218447 : CollatzResearch.WordTrace tailWord_4218447 prefixEnd_4218447 2166090926517162040412221 := by
  unfold tailWord_4218447
  simp only [CollatzResearch.WordTrace]
  refine ⟨153859402148294447234485595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102572934765529631489657063 153859402148294447234485595)
  ·
    refine ⟨230789103222441670851728393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153859402148294447234485595 230789103222441670851728393)
    ·
      refine ⟨173091827416831253138796295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230789103222441670851728393 173091827416831253138796295)
      ·
        refine ⟨259637741125246879708194443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173091827416831253138796295 259637741125246879708194443)
        ·
          refine ⟨389456611687870319562291665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259637741125246879708194443 389456611687870319562291665)
          ·
            refine ⟨292092458765902739671718749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389456611687870319562291665 292092458765902739671718749)
            ·
              refine ⟨109534672037213527376894531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 292092458765902739671718749 109534672037213527376894531)
              ·
                refine ⟨164302008055820291065341797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109534672037213527376894531 164302008055820291065341797)
                ·
                  refine ⟨30806626510466304574751587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164302008055820291065341797 30806626510466304574751587)
                  ·
                    refine ⟨46209939765699456862127381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30806626510466304574751587 46209939765699456862127381)
                    ·
                      refine ⟨2166090926517162040412221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46209939765699456862127381 2166090926517162040412221)
                      ·
                        rfl

theorem cell23_4218447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_4218447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218447 prefixEnd_4218447 := by exact prefixLift 4218447
  have htrace : WordTrace (prefixWord ++ tailWord_4218447) baseStart_4218447 baseEnd_4218447 := by
    simpa [prefixWord, tailWord_4218447, baseEnd_4218447] using wordTrace_append hprefix tailTrace_4218447
  have hstable : (prefixWord ++ tailWord_4218447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218447).length < 2 ^ (prefixWord ++ tailWord_4218447).sum := by decide
  have hdescent : baseEnd_4218447 < baseStart_4218447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218474 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 8]
def baseStart_4218474 : Nat := 118140960795 + 4218474 * 2 ^ 59
def prefixEnd_4218474 : Nat := 4983230072969 + 3 ^ 40 * 4218474 * 2
def baseEnd_4218474 : Nat := 240678310054981492752733

theorem tailTrace_4218474 : CollatzResearch.WordTrace tailWord_4218474 prefixEnd_4218474 240678310054981492752733 := by
  unfold tailWord_4218474
  simp only [CollatzResearch.WordTrace]
  refine ⟨38465096729799157711429619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102573591279464420563812317 38465096729799157711429619)
  ·
    refine ⟨57697645094698736567144429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38465096729799157711429619 57697645094698736567144429)
    ·
      refine ⟨21636616910512026212679161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57697645094698736567144429 21636616910512026212679161)
      ·
        refine ⟨16227462682884019659509371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21636616910512026212679161 16227462682884019659509371)
        ·
          refine ⟨24341194024326029489264057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16227462682884019659509371 24341194024326029489264057)
          ·
            refine ⟨18255895518244522116948043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24341194024326029489264057 18255895518244522116948043)
            ·
              refine ⟨27383843277366783175422065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18255895518244522116948043 27383843277366783175422065)
              ·
                refine ⟨20537882458025087381566549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27383843277366783175422065 20537882458025087381566549)
                ·
                  refine ⟨240678310054981492752733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20537882458025087381566549 240678310054981492752733)
                  ·
                    rfl

theorem cell23_4218474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_4218474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218474 prefixEnd_4218474 := by exact prefixLift 4218474
  have htrace : WordTrace (prefixWord ++ tailWord_4218474) baseStart_4218474 baseEnd_4218474 := by
    simpa [prefixWord, tailWord_4218474, baseEnd_4218474] using wordTrace_append hprefix tailTrace_4218474
  have hstable : (prefixWord ++ tailWord_4218474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218474).length < 2 ^ (prefixWord ++ tailWord_4218474).sum := by decide
  have hdescent : baseEnd_4218474 < baseStart_4218474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218528 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 2, 3, 2]
def baseStart_4218528 : Nat := 118140960795 + 4218528 * 2 ^ 59
def prefixEnd_4218528 : Nat := 4983230072969 + 3 ^ 40 * 4218528 * 2
def baseEnd_4218528 : Nat := 2166132518450176223499349

theorem tailTrace_4218528 : CollatzResearch.WordTrace tailWord_4218528 prefixEnd_4218528 2166132518450176223499349 := by
  unfold tailWord_4218528
  simp only [CollatzResearch.WordTrace]
  refine ⟨76931178230500499034092119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102574904307333998712122825 76931178230500499034092119)
  ·
    refine ⟨115396767345750748551138179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76931178230500499034092119 115396767345750748551138179)
    ·
      refine ⟨173095151018626122826707269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115396767345750748551138179 173095151018626122826707269)
      ·
        refine ⟨32455340815992398030007613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173095151018626122826707269 32455340815992398030007613)
        ·
          refine ⟨12170752805997149261252855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32455340815992398030007613 12170752805997149261252855)
          ·
            refine ⟨18256129208995723891879283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12170752805997149261252855 18256129208995723891879283)
            ·
              refine ⟨27384193813493585837818925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18256129208995723891879283 27384193813493585837818925)
              ·
                refine ⟨10269072680060094689182097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27384193813493585837818925 10269072680060094689182097)
                ·
                  refine ⟨7701804510045071016886573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10269072680060094689182097 7701804510045071016886573)
                  ·
                    refine ⟨2888176691266901631332465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7701804510045071016886573 2888176691266901631332465)
                    ·
                      refine ⟨2166132518450176223499349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2888176691266901631332465 2166132518450176223499349)
                      ·
                        rfl

theorem cell23_4218528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_4218528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218528 prefixEnd_4218528 := by exact prefixLift 4218528
  have htrace : WordTrace (prefixWord ++ tailWord_4218528) baseStart_4218528 baseEnd_4218528 := by
    simpa [prefixWord, tailWord_4218528, baseEnd_4218528] using wordTrace_append hprefix tailTrace_4218528
  have hstable : (prefixWord ++ tailWord_4218528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218528).length < 2 ^ (prefixWord ++ tailWord_4218528).sum := by decide
  have hdescent : baseEnd_4218528 < baseStart_4218528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218578 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_4218578 : Nat := 118140960795 + 4218578 * 2 ^ 59
def prefixEnd_4218578 : Nat := 4983230072969 + 3 ^ 40 * 4218578 * 2
def baseEnd_4218578 : Nat := 2166158192482901027874119

theorem tailTrace_4218578 : CollatzResearch.WordTrace tailWord_4218578 prefixEnd_4218578 2166158192482901027874119 := by
  unfold tailWord_4218578
  simp only [CollatzResearch.WordTrace]
  refine ⟨38466045027704964151876097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102576120073879904405002925 38466045027704964151876097)
  ·
    refine ⟨28849533770778723113907073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38466045027704964151876097 28849533770778723113907073)
    ·
      refine ⟨21637150328084042335430305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28849533770778723113907073 21637150328084042335430305)
      ·
        refine ⟨16227862746063031751572729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21637150328084042335430305 16227862746063031751572729)
        ·
          refine ⟨12170897059547273813679547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16227862746063031751572729 12170897059547273813679547)
          ·
            refine ⟨18256345589320910720519321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12170897059547273813679547 18256345589320910720519321)
            ·
              refine ⟨13692259191990683040389491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18256345589320910720519321 13692259191990683040389491)
              ·
                refine ⟨20538388787986024560584237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13692259191990683040389491 20538388787986024560584237)
                ·
                  refine ⟨7701895795494759210219089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20538388787986024560584237 7701895795494759210219089)
                  ·
                    refine ⟨5776421846621069407664317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7701895795494759210219089 5776421846621069407664317)
                    ·
                      refine ⟨2166158192482901027874119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5776421846621069407664317 2166158192482901027874119)
                      ·
                        rfl

theorem cell23_4218578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_4218578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218578 prefixEnd_4218578 := by exact prefixLift 4218578
  have htrace : WordTrace (prefixWord ++ tailWord_4218578) baseStart_4218578 baseEnd_4218578 := by
    simpa [prefixWord, tailWord_4218578, baseEnd_4218578] using wordTrace_append hprefix tailTrace_4218578
  have hstable : (prefixWord ++ tailWord_4218578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218578).length < 2 ^ (prefixWord ++ tailWord_4218578).sum := by decide
  have hdescent : baseEnd_4218578 < baseStart_4218578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218589 : List Nat := [1, 4, 3, 3, 2, 1, 2, 1, 1, 5]
def baseStart_4218589 : Nat := 118140960795 + 4218589 * 2 ^ 59
def prefixEnd_4218589 : Nat := 4983230072969 + 3 ^ 40 * 4218589 * 2
def baseEnd_4218589 : Nat := 722054613590033494945523

theorem tailTrace_4218589 : CollatzResearch.WordTrace tailWord_4218589 prefixEnd_4218589 722054613590033494945523 := by
  unfold tailWord_4218589
  simp only [CollatzResearch.WordTrace]
  refine ⟨153864581313780005486154821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102576387542520003657436547 153864581313780005486154821)
  ·
    refine ⟨28849608996333751028654029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153864581313780005486154821 28849608996333751028654029)
    ·
      refine ⟨10818603373625156635745261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28849608996333751028654029 10818603373625156635745261)
      ·
        refine ⟨4056976265109433738404473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10818603373625156635745261 4056976265109433738404473)
        ·
          refine ⟨3042732198832075303803355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4056976265109433738404473 3042732198832075303803355)
          ·
            refine ⟨4564098298248112955705033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3042732198832075303803355 4564098298248112955705033)
            ·
              refine ⟨3423073723686084716778775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4564098298248112955705033 3423073723686084716778775)
              ·
                refine ⟨5134610585529127075168163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3423073723686084716778775 5134610585529127075168163)
                ·
                  refine ⟨7701915878293690612752245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5134610585529127075168163 7701915878293690612752245)
                  ·
                    refine ⟨722054613590033494945523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7701915878293690612752245 722054613590033494945523)
                    ·
                      rfl

theorem cell23_4218589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_4218589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218589 prefixEnd_4218589 := by exact prefixLift 4218589
  have htrace : WordTrace (prefixWord ++ tailWord_4218589) baseStart_4218589 baseEnd_4218589 := by
    simpa [prefixWord, tailWord_4218589, baseEnd_4218589] using wordTrace_append hprefix tailTrace_4218589
  have hstable : (prefixWord ++ tailWord_4218589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218589).length < 2 ^ (prefixWord ++ tailWord_4218589).sum := by decide
  have hdescent : baseEnd_4218589 < baseStart_4218589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218591 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 3]
def baseStart_4218591 : Nat := 118140960795 + 4218591 * 2 ^ 59
def prefixEnd_4218591 : Nat := 4983230072969 + 3 ^ 40 * 4218591 * 2
def baseEnd_4218591 : Nat := 2166164867731409477011559

theorem tailTrace_4218591 : CollatzResearch.WordTrace tailWord_4218591 prefixEnd_4218591 2166164867731409477011559 := by
  unfold tailWord_4218591
  simp only [CollatzResearch.WordTrace]
  refine ⟨153864654259772759827727627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102576436173181839885151751 153864654259772759827727627)
  ·
    refine ⟨230796981389659139741591441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153864654259772759827727627 230796981389659139741591441)
    ·
      refine ⟨173097736042244354806193581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230796981389659139741591441 173097736042244354806193581)
      ·
        refine ⟨64911651015841633052322593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173097736042244354806193581 64911651015841633052322593)
        ·
          refine ⟨48683738261881224789241945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64911651015841633052322593 48683738261881224789241945)
          ·
            refine ⟨36512803696410918591931459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48683738261881224789241945 36512803696410918591931459)
            ·
              refine ⟨54769205544616377887897189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36512803696410918591931459 54769205544616377887897189)
              ·
                refine ⟨10269226039615570853980723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54769205544616377887897189 10269226039615570853980723)
                ·
                  refine ⟨15403839059423356280971085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10269226039615570853980723 15403839059423356280971085)
                  ·
                    refine ⟨5776439647283758605364157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15403839059423356280971085 5776439647283758605364157)
                    ·
                      refine ⟨2166164867731409477011559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5776439647283758605364157 2166164867731409477011559)
                      ·
                        rfl

theorem cell23_4218591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_4218591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218591 prefixEnd_4218591 := by exact prefixLift 4218591
  have htrace : WordTrace (prefixWord ++ tailWord_4218591) baseStart_4218591 baseEnd_4218591 := by
    simpa [prefixWord, tailWord_4218591, baseEnd_4218591] using wordTrace_append hprefix tailTrace_4218591
  have hstable : (prefixWord ++ tailWord_4218591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218591).length < 2 ^ (prefixWord ++ tailWord_4218591).sum := by decide
  have hdescent : baseEnd_4218591 < baseStart_4218591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218595 : List Nat := [1, 1, 1, 7, 2, 1, 1, 3, 1, 2, 3]
def baseStart_4218595 : Nat := 118140960795 + 4218595 * 2 ^ 59
def prefixEnd_4218595 : Nat := 4983230072969 + 3 ^ 40 * 4218595 * 2
def baseEnd_4218595 : Nat := 2166166921654027461361541

theorem tailTrace_4218595 : CollatzResearch.WordTrace tailWord_4218595 prefixEnd_4218595 2166166921654027461361541 := by
  unfold tailWord_4218595
  simp only [CollatzResearch.WordTrace]
  refine ⟨153864800151758268510873239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102576533434505512340582159 153864800151758268510873239)
  ·
    refine ⟨230797200227637402766309859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153864800151758268510873239 230797200227637402766309859)
    ·
      refine ⟨346195800341456104149464789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230797200227637402766309859 346195800341456104149464789)
      ·
        refine ⟨8113964070502877441003081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 346195800341456104149464789 8113964070502877441003081)
        ·
          refine ⟨6085473052877158080752311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8113964070502877441003081 6085473052877158080752311)
          ·
            refine ⟨9128209579315737121128467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6085473052877158080752311 9128209579315737121128467)
            ·
              refine ⟨13692314368973605681692701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9128209579315737121128467 13692314368973605681692701)
              ·
                refine ⟨5134617888365102130634763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13692314368973605681692701 5134617888365102130634763)
                ·
                  refine ⟨7701926832547653195952145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5134617888365102130634763 7701926832547653195952145)
                  ·
                    refine ⟨5776445124410739896964109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7701926832547653195952145 5776445124410739896964109)
                    ·
                      refine ⟨2166166921654027461361541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5776445124410739896964109 2166166921654027461361541)
                      ·
                        rfl

theorem cell23_4218595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_4218595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218595 prefixEnd_4218595 := by exact prefixLift 4218595
  have htrace : WordTrace (prefixWord ++ tailWord_4218595) baseStart_4218595 baseEnd_4218595 := by
    simpa [prefixWord, tailWord_4218595, baseEnd_4218595] using wordTrace_append hprefix tailTrace_4218595
  have hstable : (prefixWord ++ tailWord_4218595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218595).length < 2 ^ (prefixWord ++ tailWord_4218595).sum := by decide
  have hdescent : baseEnd_4218595 < baseStart_4218595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218608 : List Nat := [2, 1, 1, 1, 3, 1, 2, 6, 2, 1, 3]
def baseStart_4218608 : Nat := 118140960795 + 4218608 * 2 ^ 59
def prefixEnd_4218608 : Nat := 4983230072969 + 3 ^ 40 * 4218608 * 2
def baseEnd_4218608 : Nat := 2166173596902535910498981

theorem tailTrace_4218608 : CollatzResearch.WordTrace tailWord_4218608 prefixEnd_4218608 2166173596902535910498981 := by
  unfold tailWord_4218608
  simp only [CollatzResearch.WordTrace]
  refine ⟨76932637150355585865548239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102576849533807447820730985 76932637150355585865548239)
  ·
    refine ⟨115398955725533378798322359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76932637150355585865548239 115398955725533378798322359)
    ·
      refine ⟨173098433588300068197483539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115398955725533378798322359 173098433588300068197483539)
      ·
        refine ⟨259647650382450102296225309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173098433588300068197483539 259647650382450102296225309)
        ·
          refine ⟨97367868893418788361084491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259647650382450102296225309 97367868893418788361084491)
          ·
            refine ⟨146051803340128182541626737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97367868893418788361084491 146051803340128182541626737)
            ·
              refine ⟨109538852505096136906220053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146051803340128182541626737 109538852505096136906220053)
              ·
                refine ⟨5134633711176381417479065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 109538852505096136906220053 5134633711176381417479065)
                ·
                  refine ⟨3850975283382286063109299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5134633711176381417479065 3850975283382286063109299)
                  ·
                    refine ⟨5776462925073429094663949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3850975283382286063109299 5776462925073429094663949)
                    ·
                      refine ⟨2166173596902535910498981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5776462925073429094663949 2166173596902535910498981)
                      ·
                        rfl

theorem cell23_4218608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 2, 1, 3].length) (baseStart_4218608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218608 prefixEnd_4218608 := by exact prefixLift 4218608
  have htrace : WordTrace (prefixWord ++ tailWord_4218608) baseStart_4218608 baseEnd_4218608 := by
    simpa [prefixWord, tailWord_4218608, baseEnd_4218608] using wordTrace_append hprefix tailTrace_4218608
  have hstable : (prefixWord ++ tailWord_4218608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218608).length < 2 ^ (prefixWord ++ tailWord_4218608).sum := by decide
  have hdescent : baseEnd_4218608 < baseStart_4218608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218622 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_4218622 : Nat := 118140960795 + 4218622 * 2 ^ 59
def prefixEnd_4218622 : Nat := 4983230072969 + 3 ^ 40 * 4218622 * 2
def baseEnd_4218622 : Nat := 2166180785631698855723917

theorem tailTrace_4218622 : CollatzResearch.WordTrace tailWord_4218622 prefixEnd_4218622 2166180785631698855723917 := by
  unfold tailWord_4218622
  simp only [CollatzResearch.WordTrace]
  refine ⟨19233223115332556515263265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102577189948440301414737413 19233223115332556515263265)
  ·
    refine ⟨14424917336499417386447449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19233223115332556515263265 14424917336499417386447449)
    ·
      refine ⟨10818688002374563039835587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14424917336499417386447449 10818688002374563039835587)
      ·
        refine ⟨16228032003561844559753381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10818688002374563039835587 16228032003561844559753381)
        ·
          refine ⟨3042756000667845854953759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16228032003561844559753381 3042756000667845854953759)
          ·
            refine ⟨4564134001001768782430639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3042756000667845854953759 4564134001001768782430639)
            ·
              refine ⟨6846201001502653173645959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4564134001001768782430639 6846201001502653173645959)
              ·
                refine ⟨10269301502253979760468939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6846201001502653173645959 10269301502253979760468939)
                ·
                  refine ⟨15403952253380969640703409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10269301502253979760468939 15403952253380969640703409)
                  ·
                    refine ⟨11552964190035727230527557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15403952253380969640703409 11552964190035727230527557)
                    ·
                      refine ⟨2166180785631698855723917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11552964190035727230527557 2166180785631698855723917)
                      ·
                        rfl

theorem cell23_4218622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_4218622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218622 prefixEnd_4218622 := by exact prefixLift 4218622
  have htrace : WordTrace (prefixWord ++ tailWord_4218622) baseStart_4218622 baseEnd_4218622 := by
    simpa [prefixWord, tailWord_4218622, baseEnd_4218622] using wordTrace_append hprefix tailTrace_4218622
  have hstable : (prefixWord ++ tailWord_4218622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218622).length < 2 ^ (prefixWord ++ tailWord_4218622).sum := by decide
  have hdescent : baseEnd_4218622 < baseStart_4218622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218648 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 1, 4, 2]
def baseStart_4218648 : Nat := 118140960795 + 4218648 * 2 ^ 59
def prefixEnd_4218648 : Nat := 4983230072969 + 3 ^ 40 * 4218648 * 2
def baseEnd_4218648 : Nat := 2166194136128715753998797

theorem tailTrace_4218648 : CollatzResearch.WordTrace tailWord_4218648 prefixEnd_4218648 2166194136128715753998797 := by
  unfold tailWord_4218648
  simp only [CollatzResearch.WordTrace]
  refine ⟨76933366610283129281276299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102577822147044172375035065 76933366610283129281276299)
  ·
    refine ⟨115400049915424693921914449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76933366610283129281276299 115400049915424693921914449)
    ·
      refine ⟨86550037436568520441435837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115400049915424693921914449 86550037436568520441435837)
      ·
        refine ⟨32456264038713195165538439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86550037436568520441435837 32456264038713195165538439)
        ·
          refine ⟨48684396058069792748307659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32456264038713195165538439 48684396058069792748307659)
          ·
            refine ⟨73026594087104689122461489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48684396058069792748307659 73026594087104689122461489)
            ·
              refine ⟨54769945565328516841846117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73026594087104689122461489 54769945565328516841846117)
              ·
                refine ⟨10269364793499096907846147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54769945565328516841846117 10269364793499096907846147)
                ·
                  refine ⟨15404047190248645361769221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10269364793499096907846147 15404047190248645361769221)
                  ·
                    refine ⟨2888258848171621005331729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15404047190248645361769221 2888258848171621005331729)
                    ·
                      refine ⟨2166194136128715753998797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2888258848171621005331729 2166194136128715753998797)
                      ·
                        rfl

theorem cell23_4218648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_4218648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218648 prefixEnd_4218648 := by exact prefixLift 4218648
  have htrace : WordTrace (prefixWord ++ tailWord_4218648) baseStart_4218648 baseEnd_4218648 := by
    simpa [prefixWord, tailWord_4218648, baseEnd_4218648] using wordTrace_append hprefix tailTrace_4218648
  have hstable : (prefixWord ++ tailWord_4218648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218648).length < 2 ^ (prefixWord ++ tailWord_4218648).sum := by decide
  have hdescent : baseEnd_4218648 < baseStart_4218648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218682 : List Nat := [3, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2]
def baseStart_4218682 : Nat := 118140960795 + 4218682 * 2 ^ 59
def prefixEnd_4218682 : Nat := 4983230072969 + 3 ^ 40 * 4218682 * 2
def baseEnd_4218682 : Nat := 2166211594470968620973641

theorem tailTrace_4218682 : CollatzResearch.WordTrace tailWord_4218682 prefixEnd_4218682 2166211594470968620973641 := by
  unfold tailWord_4218682
  simp only [CollatzResearch.WordTrace]
  refine ⟨38466993325610770592322575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102578648868295388246193533 38466993325610770592322575)
  ·
    refine ⟨57700489988416155888483863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38466993325610770592322575 57700489988416155888483863)
    ·
      refine ⟨86550734982624233832725795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57700489988416155888483863 86550734982624233832725795)
      ·
        refine ⟨129826102473936350749088693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86550734982624233832725795 129826102473936350749088693)
        ·
          refine ⟨12171197106931532882727065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129826102473936350749088693 12171197106931532882727065)
          ·
            refine ⟨9128397830198649662045299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12171197106931532882727065 9128397830198649662045299)
            ·
              refine ⟨13692596745297974493067949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9128397830198649662045299 13692596745297974493067949)
              ·
                refine ⟨5134723779486740434900481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13692596745297974493067949 5134723779486740434900481)
                ·
                  refine ⟨3851042834615055326175361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5134723779486740434900481 3851042834615055326175361)
                  ·
                    refine ⟨2888282125961291494631521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3851042834615055326175361 2888282125961291494631521)
                    ·
                      refine ⟨2166211594470968620973641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2888282125961291494631521 2166211594470968620973641)
                      ·
                        rfl

theorem cell23_4218682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2].length) (baseStart_4218682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218682 prefixEnd_4218682 := by exact prefixLift 4218682
  have htrace : WordTrace (prefixWord ++ tailWord_4218682) baseStart_4218682 baseEnd_4218682 := by
    simpa [prefixWord, tailWord_4218682, baseEnd_4218682] using wordTrace_append hprefix tailTrace_4218682
  have hstable : (prefixWord ++ tailWord_4218682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218682).length < 2 ^ (prefixWord ++ tailWord_4218682).sum := by decide
  have hdescent : baseEnd_4218682 < baseStart_4218682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218722 : List Nat := [3, 3, 2, 1, 2, 1, 4, 2, 5]
def baseStart_4218722 : Nat := 118140960795 + 4218722 * 2 ^ 59
def prefixEnd_4218722 : Nat := 4983230072969 + 3 ^ 40 * 4218722 * 2
def baseEnd_4218722 : Nat := 240692459299683162719273

theorem tailTrace_4218722 : CollatzResearch.WordTrace tailWord_4218722 prefixEnd_4218722 240692459299683162719273 := by
  unfold tailWord_4218722
  simp only [CollatzResearch.WordTrace]
  refine ⟨38467358055574542300186605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102579621481532112800497613 38467358055574542300186605)
  ·
    refine ⟨14425259270840453362569977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38467358055574542300186605 14425259270840453362569977)
    ·
      refine ⟨10818944453130340021927483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14425259270840453362569977 10818944453130340021927483)
      ·
        refine ⟨16228416679695510032891225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10818944453130340021927483 16228416679695510032891225)
        ·
          refine ⟨12171312509771632524668419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16228416679695510032891225 12171312509771632524668419)
          ·
            refine ⟨18256968764657448787002629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12171312509771632524668419 18256968764657448787002629)
            ·
              refine ⟨3423181643373271647562993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18256968764657448787002629 3423181643373271647562993)
              ·
                refine ⟨2567386232529953735672245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3423181643373271647562993 2567386232529953735672245)
                ·
                  refine ⟨240692459299683162719273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2567386232529953735672245 240692459299683162719273)
                  ·
                    rfl

theorem cell23_4218722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_4218722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218722 prefixEnd_4218722 := by exact prefixLift 4218722
  have htrace : WordTrace (prefixWord ++ tailWord_4218722) baseStart_4218722 baseEnd_4218722 := by
    simpa [prefixWord, tailWord_4218722, baseEnd_4218722] using wordTrace_append hprefix tailTrace_4218722
  have hstable : (prefixWord ++ tailWord_4218722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218722).length < 2 ^ (prefixWord ++ tailWord_4218722).sum := by decide
  have hdescent : baseEnd_4218722 < baseStart_4218722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218755 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 2, 1, 4]
def baseStart_4218755 : Nat := 118140960795 + 4218755 * 2 ^ 59
def prefixEnd_4218755 : Nat := 4983230072969 + 3 ^ 40 * 4218755 * 2
def baseEnd_4218755 : Nat := 2166249078558746835360805

theorem tailTrace_4218755 : CollatzResearch.WordTrace tailWord_4218755 prefixEnd_4218755 2166249078558746835360805 := by
  unfold tailWord_4218755
  simp only [CollatzResearch.WordTrace]
  refine ⟨153870635831178615836697719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102580423887452410557798479 153870635831178615836697719)
  ·
    refine ⟨230805953746767923755046579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153870635831178615836697719 230805953746767923755046579)
    ·
      refine ⟨346208930620151885632569869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230805953746767923755046579 346208930620151885632569869)
      ·
        refine ⟨129828348982556957112213701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346208930620151885632569869 129828348982556957112213701)
        ·
          refine ⟨24342815434229429458540069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129828348982556957112213701 24342815434229429458540069)
          ·
            refine ⟨4564277893918018023476263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24342815434229429458540069 4564277893918018023476263)
            ·
              refine ⟨6846416840877027035214395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4564277893918018023476263 6846416840877027035214395)
              ·
                refine ⟨10269625261315540552821593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6846416840877027035214395 10269625261315540552821593)
                ·
                  refine ⟨7702218945986655414616195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10269625261315540552821593 7702218945986655414616195)
                  ·
                    refine ⟨11553328418979983121924293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7702218945986655414616195 11553328418979983121924293)
                    ·
                      refine ⟨2166249078558746835360805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11553328418979983121924293 2166249078558746835360805)
                      ·
                        rfl

theorem cell23_4218755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_4218755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218755 prefixEnd_4218755 := by exact prefixLift 4218755
  have htrace : WordTrace (prefixWord ++ tailWord_4218755) baseStart_4218755 baseEnd_4218755 := by
    simpa [prefixWord, tailWord_4218755, baseEnd_4218755] using wordTrace_append hprefix tailTrace_4218755
  have hstable : (prefixWord ++ tailWord_4218755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218755).length < 2 ^ (prefixWord ++ tailWord_4218755).sum := by decide
  have hdescent : baseEnd_4218755 < baseStart_4218755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218761 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 8]
def baseStart_4218761 : Nat := 118140960795 + 4218761 * 2 ^ 59
def prefixEnd_4218761 : Nat := 4983230072969 + 3 ^ 40 * 4218761 * 2
def baseEnd_4218761 : Nat := 240694684382519312431753

theorem tailTrace_4218761 : CollatzResearch.WordTrace tailWord_4218761 prefixEnd_4218761 240694684382519312431753 := by
  unfold tailWord_4218761
  simp only [CollatzResearch.WordTrace]
  refine ⟨153870854669156878861416137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102580569779437919240944091 153870854669156878861416137)
  ·
    refine ⟨115403141001867659146062103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153870854669156878861416137 115403141001867659146062103)
    ·
      refine ⟨173104711502801488719093155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115403141001867659146062103 173104711502801488719093155)
      ·
        refine ⟨259657067254202233078639733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173104711502801488719093155 259657067254202233078639733)
        ·
          refine ⟨24342850055081459351122475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 259657067254202233078639733 24342850055081459351122475)
          ·
            refine ⟨36514275082622189026683713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24342850055081459351122475 36514275082622189026683713)
            ·
              refine ⟨27385706311966641770012785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36514275082622189026683713 27385706311966641770012785)
              ·
                refine ⟨20539279733974981327509589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27385706311966641770012785 20539279733974981327509589)
                ·
                  refine ⟨240694684382519312431753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20539279733974981327509589 240694684382519312431753)
                  ·
                    rfl

theorem cell23_4218761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 8].length) (baseStart_4218761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218761 prefixEnd_4218761 := by exact prefixLift 4218761
  have htrace : WordTrace (prefixWord ++ tailWord_4218761) baseStart_4218761 baseEnd_4218761 := by
    simpa [prefixWord, tailWord_4218761, baseEnd_4218761] using wordTrace_append hprefix tailTrace_4218761
  have hstable : (prefixWord ++ tailWord_4218761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218761).length < 2 ^ (prefixWord ++ tailWord_4218761).sum := by decide
  have hdescent : baseEnd_4218761 < baseStart_4218761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218778 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 8]
def baseStart_4218778 : Nat := 118140960795 + 4218778 * 2 ^ 59
def prefixEnd_4218778 : Nat := 4983230072969 + 3 ^ 40 * 4218778 * 2
def baseEnd_4218778 : Nat := 240695654290422249485911

theorem tailTrace_4218778 : CollatzResearch.WordTrace tailWord_4218778 prefixEnd_4218778 240695654290422249485911 := by
  unfold tailWord_4218778
  simp only [CollatzResearch.WordTrace]
  refine ⟨38467868677523822691196247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102580983140063527176523325 38467868677523822691196247)
  ·
    refine ⟨57701803016285734036794371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38467868677523822691196247 57701803016285734036794371)
    ·
      refine ⟨86552704524428601055191557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57701803016285734036794371 86552704524428601055191557)
      ·
        refine ⟨16228632098330362697848417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86552704524428601055191557 16228632098330362697848417)
        ·
          refine ⟨12171474073747772023386313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16228632098330362697848417 12171474073747772023386313)
          ·
            refine ⟨9128605555310829017539735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12171474073747772023386313 9128605555310829017539735)
            ·
              refine ⟨13692908332966243526309603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9128605555310829017539735 13692908332966243526309603)
              ·
                refine ⟨20539362499449365289464405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13692908332966243526309603 20539362499449365289464405)
                ·
                  refine ⟨240695654290422249485911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20539362499449365289464405 240695654290422249485911)
                  ·
                    rfl

theorem cell23_4218778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_4218778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218778 prefixEnd_4218778 := by exact prefixLift 4218778
  have htrace : WordTrace (prefixWord ++ tailWord_4218778) baseStart_4218778 baseEnd_4218778 := by
    simpa [prefixWord, tailWord_4218778, baseEnd_4218778] using wordTrace_append hprefix tailTrace_4218778
  have hstable : (prefixWord ++ tailWord_4218778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218778).length < 2 ^ (prefixWord ++ tailWord_4218778).sum := by decide
  have hdescent : baseEnd_4218778 < baseStart_4218778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218815 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 2, 3, 2]
def baseStart_4218815 : Nat := 118140960795 + 4218815 * 2 ^ 59
def prefixEnd_4218815 : Nat := 4983230072969 + 3 ^ 40 * 4218815 * 2
def baseEnd_4218815 : Nat := 2166279887398016600610529

theorem tailTrace_4218815 : CollatzResearch.WordTrace tailWord_4218815 prefixEnd_4218815 2166279887398016600610529 := by
  unfold tailWord_4218815
  simp only [CollatzResearch.WordTrace]
  refine ⟨153872824210961246083881899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102581882807307497389254599 153872824210961246083881899)
  ·
    refine ⟨230809236316441869125822849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153872824210961246083881899 230809236316441869125822849)
    ·
      refine ⟨173106927237331401844367137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230809236316441869125822849 173106927237331401844367137)
      ·
        refine ⟨129830195427998551383275353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173106927237331401844367137 129830195427998551383275353)
        ·
          refine ⟨97372646570998913537456515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129830195427998551383275353 97372646570998913537456515)
          ·
            refine ⟨146058969856498370306184773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97372646570998913537456515 146058969856498370306184773)
            ·
              refine ⟨27386056848093444432409645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146058969856498370306184773 27386056848093444432409645)
              ·
                refine ⟨10269771318035041662153617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27386056848093444432409645 10269771318035041662153617)
                ·
                  refine ⟨7702328488526281246615213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10269771318035041662153617 7702328488526281246615213)
                  ·
                    refine ⟨2888373183197355467480705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7702328488526281246615213 2888373183197355467480705)
                    ·
                      refine ⟨2166279887398016600610529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2888373183197355467480705 2166279887398016600610529)
                      ·
                        rfl

theorem cell23_4218815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 3, 2].length) (baseStart_4218815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218815 prefixEnd_4218815 := by exact prefixLift 4218815
  have htrace : WordTrace (prefixWord ++ tailWord_4218815) baseStart_4218815 baseEnd_4218815 := by
    simpa [prefixWord, tailWord_4218815, baseEnd_4218815] using wordTrace_append hprefix tailTrace_4218815
  have hstable : (prefixWord ++ tailWord_4218815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218815).length < 2 ^ (prefixWord ++ tailWord_4218815).sum := by decide
  have hdescent : baseEnd_4218815 < baseStart_4218815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218839 : List Nat := [1, 1, 3, 2, 1, 1, 7, 2, 1, 1, 3]
def baseStart_4218839 : Nat := 118140960795 + 4218839 * 2 ^ 59
def prefixEnd_4218839 : Nat := 4983230072969 + 3 ^ 40 * 4218839 * 2
def baseEnd_4218839 : Nat := 2166292210933724506710419

theorem tailTrace_4218839 : CollatzResearch.WordTrace tailWord_4218839 prefixEnd_4218839 2166292210933724506710419 := by
  unfold tailWord_4218839
  simp only [CollatzResearch.WordTrace]
  refine ⟨153873699562874298182755571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102582466375249532121837047 153873699562874298182755571)
  ·
    refine ⟨230810549344311447274133357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153873699562874298182755571 230810549344311447274133357)
    ·
      refine ⟨86553956004116792727800009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230810549344311447274133357 86553956004116792727800009)
      ·
        refine ⟨64915467003087594545850007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86553956004116792727800009 64915467003087594545850007)
        ·
          refine ⟨97373200504631391818775011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64915467003087594545850007 97373200504631391818775011)
          ·
            refine ⟨146059800756947087728162517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97373200504631391818775011 146059800756947087728162517)
            ·
              refine ⟨3423276580240947368628809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 146059800756947087728162517 3423276580240947368628809)
              ·
                refine ⟨2567457435180710526471607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3423276580240947368628809 2567457435180710526471607)
                ·
                  refine ⟨3851186152771065789707411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2567457435180710526471607 3851186152771065789707411)
                  ·
                    refine ⟨5776779229156598684561117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3851186152771065789707411 5776779229156598684561117)
                    ·
                      refine ⟨2166292210933724506710419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5776779229156598684561117 2166292210933724506710419)
                      ·
                        rfl

theorem cell23_4218839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_4218839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218839 prefixEnd_4218839 := by exact prefixLift 4218839
  have htrace : WordTrace (prefixWord ++ tailWord_4218839) baseStart_4218839 baseEnd_4218839 := by
    simpa [prefixWord, tailWord_4218839, baseEnd_4218839] using wordTrace_append hprefix tailTrace_4218839
  have hstable : (prefixWord ++ tailWord_4218839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218839).length < 2 ^ (prefixWord ++ tailWord_4218839).sum := by decide
  have hdescent : baseEnd_4218839 < baseStart_4218839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218858 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_4218858 : Nat := 118140960795 + 4218858 * 2 ^ 59
def prefixEnd_4218858 : Nat := 4983230072969 + 3 ^ 40 * 4218858 * 2
def baseEnd_4218858 : Nat := 2166301967066159932372831

theorem tailTrace_4218858 : CollatzResearch.WordTrace tailWord_4218858 prefixEnd_4218858 2166301967066159932372831 := by
  unfold tailWord_4218858
  simp only [CollatzResearch.WordTrace]
  refine ⟨38468598137451366106924307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102582928366536976285131485 38468598137451366106924307)
  ·
    refine ⟨57702897206177049160386461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38468598137451366106924307 57702897206177049160386461)
    ·
      refine ⟨21638586452316393435144923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57702897206177049160386461 21638586452316393435144923)
      ·
        refine ⟨32457879678474590152717385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21638586452316393435144923 32457879678474590152717385)
        ·
          refine ⟨24343409758855942614538039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32457879678474590152717385 24343409758855942614538039)
          ·
            refine ⟨36515114638283913921807059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24343409758855942614538039 36515114638283913921807059)
            ·
              refine ⟨54772671957425870882710589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36515114638283913921807059 54772671957425870882710589)
              ·
                refine ⟨20539751984034701581016471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54772671957425870882710589 20539751984034701581016471)
                ·
                  refine ⟨30809627976052052371524707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20539751984034701581016471 30809627976052052371524707)
                  ·
                    refine ⟨46214441964078078557287061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30809627976052052371524707 46214441964078078557287061)
                    ·
                      refine ⟨2166301967066159932372831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46214441964078078557287061 2166301967066159932372831)
                      ·
                        rfl

theorem cell23_4218858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_4218858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218858 prefixEnd_4218858 := by exact prefixLift 4218858
  have htrace : WordTrace (prefixWord ++ tailWord_4218858) baseStart_4218858 baseEnd_4218858 := by
    simpa [prefixWord, tailWord_4218858, baseEnd_4218858] using wordTrace_append hprefix tailTrace_4218858
  have hstable : (prefixWord ++ tailWord_4218858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218858).length < 2 ^ (prefixWord ++ tailWord_4218858).sum := by decide
  have hdescent : baseEnd_4218858 < baseStart_4218858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218862 : List Nat := [4, 1, 2, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_4218862 : Nat := 118140960795 + 4218862 * 2 ^ 59
def prefixEnd_4218862 : Nat := 4983230072969 + 3 ^ 40 * 4218862 * 2
def baseEnd_4218862 : Nat := 2166304020988777916722813

theorem tailTrace_4218862 : CollatzResearch.WordTrace tailWord_4218862 prefixEnd_4218862 2166304020988777916722813 := by
  unfold tailWord_4218862
  simp only [CollatzResearch.WordTrace]
  refine ⟨19234317305223871638855355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102583025627860648740561893 19234317305223871638855355)
  ·
    refine ⟨28851475957835807458283033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19234317305223871638855355 28851475957835807458283033)
    ·
      refine ⟨21638606968376855593712275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28851475957835807458283033 21638606968376855593712275)
      ·
        refine ⟨32457910452565283390568413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21638606968376855593712275 32457910452565283390568413)
        ·
          refine ⟨12171716419711981271463155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32457910452565283390568413 12171716419711981271463155)
          ·
            refine ⟨18257574629567971907194733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12171716419711981271463155 18257574629567971907194733)
            ·
              refine ⟨6846590486087989465198025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18257574629567971907194733 6846590486087989465198025)
              ·
                refine ⟨5134942864565992098898519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6846590486087989465198025 5134942864565992098898519)
                ·
                  refine ⟨7702414296848988148347779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5134942864565992098898519 7702414296848988148347779)
                  ·
                    refine ⟨11553621445273482222521669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7702414296848988148347779 11553621445273482222521669)
                    ·
                      refine ⟨2166304020988777916722813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11553621445273482222521669 2166304020988777916722813)
                      ·
                        rfl

theorem cell23_4218862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_4218862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218862 prefixEnd_4218862 := by exact prefixLift 4218862
  have htrace : WordTrace (prefixWord ++ tailWord_4218862) baseStart_4218862 baseEnd_4218862 := by
    simpa [prefixWord, tailWord_4218862, baseEnd_4218862] using wordTrace_append hprefix tailTrace_4218862
  have hstable : (prefixWord ++ tailWord_4218862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218862).length < 2 ^ (prefixWord ++ tailWord_4218862).sum := by decide
  have hdescent : baseEnd_4218862 < baseStart_4218862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218938 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_4218938 : Nat := 118140960795 + 4218938 * 2 ^ 59
def prefixEnd_4218938 : Nat := 4983230072969 + 3 ^ 40 * 4218938 * 2
def baseEnd_4218938 : Nat := 2166343045518519619372463

theorem tailTrace_4218938 : CollatzResearch.WordTrace tailWord_4218938 prefixEnd_4218938 2166343045518519619372463 := by
  unfold tailWord_4218938
  simp only [CollatzResearch.WordTrace]
  refine ⟨38469327597378909522652367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102584873593010425393739645 38469327597378909522652367)
  ·
    refine ⟨57703991396068364283978551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38469327597378909522652367 57703991396068364283978551)
    ·
      refine ⟨86555987094102546425967827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57703991396068364283978551 86555987094102546425967827)
      ·
        refine ⟨129833980641153819638951741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86555987094102546425967827 129833980641153819638951741)
        ·
          refine ⟨48687742740432682364606903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129833980641153819638951741 48687742740432682364606903)
          ·
            refine ⟨73031614110649023546910355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48687742740432682364606903 73031614110649023546910355)
            ·
              refine ⟨109547421165973535320365533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73031614110649023546910355 109547421165973535320365533)
              ·
                refine ⟨41080282937240075745137075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109547421165973535320365533 41080282937240075745137075)
                ·
                  refine ⟨61620424405860113617705613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41080282937240075745137075 61620424405860113617705613)
                  ·
                    refine ⟨23107659152197542606639605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61620424405860113617705613 23107659152197542606639605)
                    ·
                      refine ⟨2166343045518519619372463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23107659152197542606639605 2166343045518519619372463)
                      ·
                        rfl

theorem cell23_4218938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_4218938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218938 prefixEnd_4218938 := by exact prefixLift 4218938
  have htrace : WordTrace (prefixWord ++ tailWord_4218938) baseStart_4218938 baseEnd_4218938 := by
    simpa [prefixWord, tailWord_4218938, baseEnd_4218938] using wordTrace_append hprefix tailTrace_4218938
  have hstable : (prefixWord ++ tailWord_4218938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218938).length < 2 ^ (prefixWord ++ tailWord_4218938).sum := by decide
  have hdescent : baseEnd_4218938 < baseStart_4218938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218945 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 2, 6]
def baseStart_4218945 : Nat := 118140960795 + 4218945 * 2 ^ 59
def prefixEnd_4218945 : Nat := 4983230072969 + 3 ^ 40 * 4218945 * 2
def baseEnd_4218945 : Nat := 722115546627700363994977

theorem tailTrace_4218945 : CollatzResearch.WordTrace tailWord_4218945 prefixEnd_4218945 722115546627700363994977 := by
  unfold tailWord_4218945
  simp only [CollatzResearch.WordTrace]
  refine ⟨153877565700490278286114289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102585043800326852190742859 153877565700490278286114289)
  ·
    refine ⟨115408174275367708714585717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153877565700490278286114289 115408174275367708714585717)
    ·
      refine ⟨10819516338315722691992411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115408174275367708714585717 10819516338315722691992411)
      ·
        refine ⟨16229274507473584037988617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10819516338315722691992411 16229274507473584037988617)
        ·
          refine ⟨12171955880605188028491463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16229274507473584037988617 12171955880605188028491463)
          ·
            refine ⟨18257933820907782042737195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12171955880605188028491463 18257933820907782042737195)
            ·
              refine ⟨27386900731361673064105793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18257933820907782042737195 27386900731361673064105793)
              ·
                refine ⟨20540175548521254798079345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27386900731361673064105793 20540175548521254798079345)
                ·
                  refine ⟨15405131661390941098559509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20540175548521254798079345 15405131661390941098559509)
                  ·
                    refine ⟨722115546627700363994977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15405131661390941098559509 722115546627700363994977)
                    ·
                      rfl

theorem cell23_4218945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_4218945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218945 prefixEnd_4218945 := by exact prefixLift 4218945
  have htrace : WordTrace (prefixWord ++ tailWord_4218945) baseStart_4218945 baseEnd_4218945 := by
    simpa [prefixWord, tailWord_4218945, baseEnd_4218945] using wordTrace_append hprefix tailTrace_4218945
  have hstable : (prefixWord ++ tailWord_4218945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218945).length < 2 ^ (prefixWord ++ tailWord_4218945).sum := by decide
  have hdescent : baseEnd_4218945 < baseStart_4218945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218965 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_4218965 : Nat := 118140960795 + 4218965 * 2 ^ 59
def prefixEnd_4218965 : Nat := 4983230072969 + 3 ^ 40 * 4218965 * 2
def baseEnd_4218965 : Nat := 2166356909496191013734839

theorem tailTrace_4218965 : CollatzResearch.WordTrace tailWord_4218965 prefixEnd_4218965 2166356909496191013734839 := by
  unfold tailWord_4218965
  simp only [CollatzResearch.WordTrace]
  refine ⟨153878295160417821701842349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102585530106945214467894899 153878295160417821701842349)
  ·
    refine ⟨57704360685156683138190881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153878295160417821701842349 57704360685156683138190881)
    ·
      refine ⟨43278270513867512353643161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57704360685156683138190881 43278270513867512353643161)
      ·
        refine ⟨32458702885400634265232371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43278270513867512353643161 32458702885400634265232371)
        ·
          refine ⟨48688054328100951397848557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32458702885400634265232371 48688054328100951397848557)
          ·
            refine ⟨18258020373037856774193209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48688054328100951397848557 18258020373037856774193209)
            ·
              refine ⟨13693515279778392580644907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18258020373037856774193209 13693515279778392580644907)
              ·
                refine ⟨20540272919667588870967361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13693515279778392580644907 20540272919667588870967361)
                ·
                  refine ⟨15405204689750691653225521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20540272919667588870967361 15405204689750691653225521)
                  ·
                    refine ⟨11553903517313018739919141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15405204689750691653225521 11553903517313018739919141)
                    ·
                      refine ⟨2166356909496191013734839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11553903517313018739919141 2166356909496191013734839)
                      ·
                        rfl

theorem cell23_4218965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_4218965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218965 prefixEnd_4218965 := by exact prefixLift 4218965
  have htrace : WordTrace (prefixWord ++ tailWord_4218965) baseStart_4218965 baseEnd_4218965 := by
    simpa [prefixWord, tailWord_4218965, baseEnd_4218965] using wordTrace_append hprefix tailTrace_4218965
  have hstable : (prefixWord ++ tailWord_4218965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218965).length < 2 ^ (prefixWord ++ tailWord_4218965).sum := by decide
  have hdescent : baseEnd_4218965 < baseStart_4218965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4218992 : List Nat := [2, 1, 1, 1, 5, 2, 3, 3, 5]
def baseStart_4218992 : Nat := 118140960795 + 4218992 * 2 ^ 59
def prefixEnd_4218992 : Nat := 4983230072969 + 3 ^ 40 * 4218992 * 2
def baseEnd_4218992 : Nat := 240707863719318045344135

theorem tailTrace_4218992 : CollatzResearch.WordTrace tailWord_4218992 prefixEnd_4218992 240707863719318045344135 := by
  unfold tailWord_4218992
  simp only [CollatzResearch.WordTrace]
  refine ⟨76939639965660002656537615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102586186620880003542050153 76939639965660002656537615)
  ·
    refine ⟨115409459948490003984806423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76939639965660002656537615 115409459948490003984806423)
    ·
      refine ⟨173114189922735005977209635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115409459948490003984806423 173114189922735005977209635)
      ·
        refine ⟨259671284884102508965814453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173114189922735005977209635 259671284884102508965814453)
        ·
          refine ⟨24344182957884610215545105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 259671284884102508965814453 24344182957884610215545105)
          ·
            refine ⟨18258137218413457661658829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24344182957884610215545105 18258137218413457661658829)
            ·
              refine ⟨6846801456905046623122061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18258137218413457661658829 6846801456905046623122061)
              ·
                refine ⟨2567550546339392483670773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6846801456905046623122061 2567550546339392483670773)
                ·
                  refine ⟨240707863719318045344135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2567550546339392483670773 240707863719318045344135)
                  ·
                    rfl

theorem cell23_4218992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 5].length) (baseStart_4218992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4218992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4218992 prefixEnd_4218992 := by exact prefixLift 4218992
  have htrace : WordTrace (prefixWord ++ tailWord_4218992) baseStart_4218992 baseEnd_4218992 := by
    simpa [prefixWord, tailWord_4218992, baseEnd_4218992] using wordTrace_append hprefix tailTrace_4218992
  have hstable : (prefixWord ++ tailWord_4218992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4218992).length < 2 ^ (prefixWord ++ tailWord_4218992).sum := by decide
  have hdescent : baseEnd_4218992 < baseStart_4218992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4218992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219005 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_4219005 : Nat := 118140960795 + 4219005 * 2 ^ 59
def prefixEnd_4219005 : Nat := 4983230072969 + 3 ^ 40 * 4219005 * 2
def baseEnd_4219005 : Nat := 722125816240790285744885

theorem tailTrace_4219005 : CollatzResearch.WordTrace tailWord_4219005 prefixEnd_4219005 722125816240790285744885 := by
  unfold tailWord_4219005
  simp only [CollatzResearch.WordTrace]
  refine ⟨153879754080272908533298469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102586502720181939022198979 153879754080272908533298469)
  ·
    refine ⟨28852453890051170349993463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153879754080272908533298469 28852453890051170349993463)
    ·
      refine ⟨43278680835076755524990195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28852453890051170349993463 43278680835076755524990195)
      ·
        refine ⟨64918021252615133287485293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43278680835076755524990195 64918021252615133287485293)
        ·
          refine ⟨24344257969730674982806985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64918021252615133287485293 24344257969730674982806985)
          ·
            refine ⟨18258193477298006237105239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24344257969730674982806985 18258193477298006237105239)
            ·
              refine ⟨27387290215947009355657859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18258193477298006237105239 27387290215947009355657859)
              ·
                refine ⟨41080935323920514033486789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27387290215947009355657859 41080935323920514033486789)
                ·
                  refine ⟨7702675373235096381278773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41080935323920514033486789 7702675373235096381278773)
                  ·
                    refine ⟨722125816240790285744885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7702675373235096381278773 722125816240790285744885)
                    ·
                      rfl

theorem cell23_4219005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_4219005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219005 prefixEnd_4219005 := by exact prefixLift 4219005
  have htrace : WordTrace (prefixWord ++ tailWord_4219005) baseStart_4219005 baseEnd_4219005 := by
    simpa [prefixWord, tailWord_4219005, baseEnd_4219005] using wordTrace_append hprefix tailTrace_4219005
  have hstable : (prefixWord ++ tailWord_4219005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219005).length < 2 ^ (prefixWord ++ tailWord_4219005).sum := by decide
  have hdescent : baseEnd_4219005 < baseStart_4219005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219009 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 7]
def baseStart_4219009 : Nat := 118140960795 + 4219009 * 2 ^ 59
def prefixEnd_4219009 : Nat := 4983230072969 + 3 ^ 40 * 4219009 * 2
def baseEnd_4219009 : Nat := 240708833627220982398293

theorem tailTrace_4219009 : CollatzResearch.WordTrace tailWord_4219009 prefixEnd_4219009 240708833627220982398293 := by
  unfold tailWord_4219009
  simp only [CollatzResearch.WordTrace]
  refine ⟨153879899972258417216444081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102586599981505611477629387 153879899972258417216444081)
  ·
    refine ⟨115409924979193812912333061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153879899972258417216444081 115409924979193812912333061)
    ·
      refine ⟨21639360933598839921062449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115409924979193812912333061 21639360933598839921062449)
      ·
        refine ⟨16229520700199129940796837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21639360933598839921062449 16229520700199129940796837)
        ·
          refine ⟨3043035131287336863899407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16229520700199129940796837 3043035131287336863899407)
          ·
            refine ⟨4564552696931005295849111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3043035131287336863899407 4564552696931005295849111)
            ·
              refine ⟨6846829045396507943773667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4564552696931005295849111 6846829045396507943773667)
              ·
                refine ⟨10270243568094761915660501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6846829045396507943773667 10270243568094761915660501)
                ·
                  refine ⟨240708833627220982398293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10270243568094761915660501 240708833627220982398293)
                  ·
                    rfl

theorem cell23_4219009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 7].length) (baseStart_4219009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219009 prefixEnd_4219009 := by exact prefixLift 4219009
  have htrace : WordTrace (prefixWord ++ tailWord_4219009) baseStart_4219009 baseEnd_4219009 := by
    simpa [prefixWord, tailWord_4219009, baseEnd_4219009] using wordTrace_append hprefix tailTrace_4219009
  have hstable : (prefixWord ++ tailWord_4219009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219009).length < 2 ^ (prefixWord ++ tailWord_4219009).sum := by decide
  have hdescent : baseEnd_4219009 < baseStart_4219009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219012 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_4219012 : Nat := 118140960795 + 4219012 * 2 ^ 59
def prefixEnd_4219012 : Nat := 4983230072969 + 3 ^ 40 * 4219012 * 2
def baseEnd_4219012 : Nat := 2166381043086952329847123

theorem tailTrace_4219012 : CollatzResearch.WordTrace tailWord_4219012 prefixEnd_4219012 2166381043086952329847123 := by
  unfold tailWord_4219012
  simp only [CollatzResearch.WordTrace]
  refine ⟨76940004695623774364401645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102586672927498365819202193 76940004695623774364401645)
  ·
    refine ⟨28852501760858915386650617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76940004695623774364401645 28852501760858915386650617)
    ·
      refine ⟨21639376320644186539987963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28852501760858915386650617 21639376320644186539987963)
      ·
        refine ⟨32459064480966279809981945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21639376320644186539987963 32459064480966279809981945)
        ·
          refine ⟨24344298360724709857486459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32459064480966279809981945 24344298360724709857486459)
          ·
            refine ⟨36516447541087064786229689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24344298360724709857486459 36516447541087064786229689)
            ·
              refine ⟨27387335655815298589672267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36516447541087064786229689 27387335655815298589672267)
              ·
                refine ⟨41081003483722947884508401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27387335655815298589672267 41081003483722947884508401)
                ·
                  refine ⟨30810752612792210913381301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41081003483722947884508401 30810752612792210913381301)
                  ·
                    refine ⟨2888508057449269773129497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30810752612792210913381301 2888508057449269773129497)
                    ·
                      refine ⟨2166381043086952329847123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2888508057449269773129497 2166381043086952329847123)
                      ·
                        rfl

theorem cell23_4219012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_4219012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219012 prefixEnd_4219012 := by exact prefixLift 4219012
  have htrace : WordTrace (prefixWord ++ tailWord_4219012) baseStart_4219012 baseEnd_4219012 := by
    simpa [prefixWord, tailWord_4219012, baseEnd_4219012] using wordTrace_append hprefix tailTrace_4219012
  have hstable : (prefixWord ++ tailWord_4219012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219012).length < 2 ^ (prefixWord ++ tailWord_4219012).sum := by decide
  have hdescent : baseEnd_4219012 < baseStart_4219012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219169 : List Nat := [1, 2, 3, 2, 1, 1, 4, 3, 1, 2, 3]
def baseStart_4219169 : Nat := 118140960795 + 4219169 * 2 ^ 59
def prefixEnd_4219169 : Nat := 4983230072969 + 3 ^ 40 * 4219169 * 2
def baseEnd_4219169 : Nat := 2166461659549708215583901

theorem tailTrace_4219169 : CollatzResearch.WordTrace tailWord_4219169 prefixEnd_4219169 2166461659549708215583901 := by
  unfold tailWord_4219169
  simp only [CollatzResearch.WordTrace]
  refine ⟨153885735651678764542268561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102590490434452509694845707 153885735651678764542268561)
  ·
    refine ⟨115414301738759073406701421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153885735651678764542268561 115414301738759073406701421)
    ·
      refine ⟨43280363152034652527513033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115414301738759073406701421 43280363152034652527513033)
      ·
        refine ⟨32460272364025989395634775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43280363152034652527513033 32460272364025989395634775)
        ·
          refine ⟨48690408546038984093452163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32460272364025989395634775 48690408546038984093452163)
          ·
            refine ⟨73035612819058476140178245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48690408546038984093452163 73035612819058476140178245)
            ·
              refine ⟨13694177403573464276283421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73035612819058476140178245 13694177403573464276283421)
              ·
                refine ⟨5135316526340049103606283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13694177403573464276283421 5135316526340049103606283)
                ·
                  refine ⟨7702974789510073655409425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5135316526340049103606283 7702974789510073655409425)
                  ·
                    refine ⟨5777231092132555241557069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7702974789510073655409425 5777231092132555241557069)
                    ·
                      refine ⟨2166461659549708215583901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5777231092132555241557069 2166461659549708215583901)
                      ·
                        rfl

theorem cell23_4219169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_4219169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219169 prefixEnd_4219169 := by exact prefixLift 4219169
  have htrace : WordTrace (prefixWord ++ tailWord_4219169) baseStart_4219169 baseEnd_4219169 := by
    simpa [prefixWord, tailWord_4219169, baseEnd_4219169] using wordTrace_append hprefix tailTrace_4219169
  have hstable : (prefixWord ++ tailWord_4219169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219169).length < 2 ^ (prefixWord ++ tailWord_4219169).sum := by decide
  have hdescent : baseEnd_4219169 < baseStart_4219169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219172 : List Nat := [2, 3, 1, 3, 1, 4, 9]
def baseStart_4219172 : Nat := 118140960795 + 4219172 * 2 ^ 59
def prefixEnd_4219172 : Nat := 4983230072969 + 3 ^ 40 * 4219172 * 2
def baseEnd_4219172 : Nat := 26746459259156440788227

theorem tailTrace_4219172 : CollatzResearch.WordTrace tailWord_4219172 prefixEnd_4219172 26746459259156440788227 := by
  unfold tailWord_4219172
  simp only [CollatzResearch.WordTrace]
  refine ⟨76942922535333948027313885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102590563380445264036418513 76942922535333948027313885)
  ·
    refine ⟨28853595950750230510242707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76942922535333948027313885 28853595950750230510242707)
    ·
      refine ⟨43280393926125345765364061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28853595950750230510242707 43280393926125345765364061)
      ·
        refine ⟨16230147722297004662011523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43280393926125345765364061 16230147722297004662011523)
        ·
          refine ⟨24345221583445506993017285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16230147722297004662011523 24345221583445506993017285)
          ·
            refine ⟨4564729046896032561190741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24345221583445506993017285 4564729046896032561190741)
            ·
              refine ⟨26746459259156440788227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4564729046896032561190741 26746459259156440788227)
              ·
                rfl

theorem cell23_4219172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 9].length) (baseStart_4219172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219172 prefixEnd_4219172 := by exact prefixLift 4219172
  have htrace : WordTrace (prefixWord ++ tailWord_4219172) baseStart_4219172 baseEnd_4219172 := by
    simpa [prefixWord, tailWord_4219172, baseEnd_4219172] using wordTrace_append hprefix tailTrace_4219172
  have hstable : (prefixWord ++ tailWord_4219172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219172).length < 2 ^ (prefixWord ++ tailWord_4219172).sum := by decide
  have hdescent : baseEnd_4219172 < baseStart_4219172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219193 : List Nat := [1, 2, 1, 6, 1, 3, 2, 1, 2, 4]
def baseStart_4219193 : Nat := 118140960795 + 4219193 * 2 ^ 59
def prefixEnd_4219193 : Nat := 4983230072969 + 3 ^ 40 * 4219193 * 2
def baseEnd_4219193 : Nat := 722157994361805373894597

theorem tailTrace_4219193 : CollatzResearch.WordTrace tailWord_4219193 prefixEnd_4219193 722157994361805373894597 := by
  unfold tailWord_4219193
  simp only [CollatzResearch.WordTrace]
  refine ⟨153886611003591816641142233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102591074002394544427428155 153886611003591816641142233)
  ·
    refine ⟨115414958252693862480856675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153886611003591816641142233 115414958252693862480856675)
    ·
      refine ⟨173122437379040793721285013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115414958252693862480856675 173122437379040793721285013)
      ·
        refine ⟨8115114252142537205685235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 173122437379040793721285013 8115114252142537205685235)
        ·
          refine ⟨12172671378213805808527853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8115114252142537205685235 12172671378213805808527853)
          ·
            refine ⟨4564751766830177178197945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12172671378213805808527853 4564751766830177178197945)
            ·
              refine ⟨3423563825122632883648459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4564751766830177178197945 3423563825122632883648459)
              ·
                refine ⟨5135345737683949325472689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3423563825122632883648459 5135345737683949325472689)
                ·
                  refine ⟨3851509303262961994104517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5135345737683949325472689 3851509303262961994104517)
                  ·
                    refine ⟨722157994361805373894597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3851509303262961994104517 722157994361805373894597)
                    ·
                      rfl

theorem cell23_4219193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 2, 4].length) (baseStart_4219193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219193 prefixEnd_4219193 := by exact prefixLift 4219193
  have htrace : WordTrace (prefixWord ++ tailWord_4219193) baseStart_4219193 baseEnd_4219193 := by
    simpa [prefixWord, tailWord_4219193, baseEnd_4219193] using wordTrace_append hprefix tailTrace_4219193
  have hstable : (prefixWord ++ tailWord_4219193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219193).length < 2 ^ (prefixWord ++ tailWord_4219193).sum := by decide
  have hdescent : baseEnd_4219193 < baseStart_4219193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219205 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_4219205 : Nat := 118140960795 + 4219205 * 2 ^ 59
def prefixEnd_4219205 : Nat := 4983230072969 + 3 ^ 40 * 4219205 * 2
def baseEnd_4219205 : Nat := 2166480144853270074733735

theorem tailTrace_4219205 : CollatzResearch.WordTrace tailWord_4219205 prefixEnd_4219205 2166480144853270074733735 := by
  unfold tailWord_4219205
  simp only [CollatzResearch.WordTrace]
  refine ⟨153887048679548342690579069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102591365786365561793719379 153887048679548342690579069)
  ·
    refine ⟨57707643254830628508967151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153887048679548342690579069 57707643254830628508967151)
    ·
      refine ⟨86561464882245942763450727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57707643254830628508967151 86561464882245942763450727)
      ·
        refine ⟨129842197323368914145176091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86561464882245942763450727 129842197323368914145176091)
        ·
          refine ⟨194763295985053371217764137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129842197323368914145176091 194763295985053371217764137)
          ·
            refine ⟨146072471988790028413323103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194763295985053371217764137 146072471988790028413323103)
            ·
              refine ⟨219108707983185042619984655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146072471988790028413323103 219108707983185042619984655)
              ·
                refine ⟨328663061974777563929976983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219108707983185042619984655 328663061974777563929976983)
                ·
                  refine ⟨492994592962166345894965475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328663061974777563929976983 492994592962166345894965475)
                  ·
                    refine ⟨739491889443249518842448213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 492994592962166345894965475 739491889443249518842448213)
                    ·
                      refine ⟨2166480144853270074733735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 739491889443249518842448213 2166480144853270074733735)
                      ·
                        rfl

theorem cell23_4219205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_4219205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219205 prefixEnd_4219205 := by exact prefixLift 4219205
  have htrace : WordTrace (prefixWord ++ tailWord_4219205) baseStart_4219205 baseEnd_4219205 := by
    simpa [prefixWord, tailWord_4219205, baseEnd_4219205] using wordTrace_append hprefix tailTrace_4219205
  have hstable : (prefixWord ++ tailWord_4219205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219205).length < 2 ^ (prefixWord ++ tailWord_4219205).sum := by decide
  have hdescent : baseEnd_4219205 < baseStart_4219205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219215 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 3, 8]
def baseStart_4219215 : Nat := 118140960795 + 4219215 * 2 ^ 59
def prefixEnd_4219215 : Nat := 4983230072969 + 3 ^ 40 * 4219215 * 2
def baseEnd_4219215 : Nat := 722161759886605011869563

theorem tailTrace_4219215 : CollatzResearch.WordTrace tailWord_4219215 prefixEnd_4219215 722161759886605011869563 := by
  unfold tailWord_4219215
  simp only [CollatzResearch.WordTrace]
  refine ⟨153887413409512114398443099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102591608939674742932295399 153887413409512114398443099)
  ·
    refine ⟨230831120114268171597664649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153887413409512114398443099 230831120114268171597664649)
    ·
      refine ⟨173123340085701128698248487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230831120114268171597664649 173123340085701128698248487)
      ·
        refine ⟨259685010128551693047372731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173123340085701128698248487 259685010128551693047372731)
        ·
          refine ⟨389527515192827539571059097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259685010128551693047372731 389527515192827539571059097)
          ·
            refine ⟨292145636394620654678294323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389527515192827539571059097 292145636394620654678294323)
            ·
              refine ⟨438218454591930982017441485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292145636394620654678294323 438218454591930982017441485)
              ·
                refine ⟨164331920471974118256540557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 438218454591930982017441485 164331920471974118256540557)
                ·
                  refine ⟨61624470176990294346202709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164331920471974118256540557 61624470176990294346202709)
                  ·
                    refine ⟨722161759886605011869563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61624470176990294346202709 722161759886605011869563)
                    ·
                      rfl

theorem cell23_4219215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_4219215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219215 prefixEnd_4219215 := by exact prefixLift 4219215
  have htrace : WordTrace (prefixWord ++ tailWord_4219215) baseStart_4219215 baseEnd_4219215 := by
    simpa [prefixWord, tailWord_4219215, baseEnd_4219215] using wordTrace_append hprefix tailTrace_4219215
  have hstable : (prefixWord ++ tailWord_4219215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219215).length < 2 ^ (prefixWord ++ tailWord_4219215).sum := by decide
  have hdescent : baseEnd_4219215 < baseStart_4219215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219290 : List Nat := [3, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2]
def baseStart_4219290 : Nat := 118140960795 + 4219290 * 2 ^ 59
def prefixEnd_4219290 : Nat := 4983230072969 + 3 ^ 40 * 4219290 * 2
def baseEnd_4219290 : Nat := 2166523790708902242170845

theorem tailTrace_4219290 : CollatzResearch.WordTrace tailWord_4219290 prefixEnd_4219290 2166523790708902242170845 := by
  unfold tailWord_4219290
  simp only [CollatzResearch.WordTrace]
  refine ⟨38472537221060100551855831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102593432589493601471615549 38472537221060100551855831)
  ·
    refine ⟨57708805831590150827783747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38472537221060100551855831 57708805831590150827783747)
    ·
      refine ⟨86563208747385226241675621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57708805831590150827783747 86563208747385226241675621)
      ·
        refine ⟨16230601640134729920314179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86563208747385226241675621 16230601640134729920314179)
        ·
          refine ⟨24345902460202094880471269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16230601640134729920314179 24345902460202094880471269)
          ·
            refine ⟨4564856711287892790088363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24345902460202094880471269 4564856711287892790088363)
            ·
              refine ⟨6847285066931839185132545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4564856711287892790088363 6847285066931839185132545)
              ·
                refine ⟨5135463800198879388849409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6847285066931839185132545 5135463800198879388849409)
                ·
                  refine ⟨3851597850149159541637057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5135463800198879388849409 3851597850149159541637057)
                  ·
                    refine ⟨2888698387611869656227793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3851597850149159541637057 2888698387611869656227793)
                    ·
                      refine ⟨2166523790708902242170845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2888698387611869656227793 2166523790708902242170845)
                      ·
                        rfl

theorem cell23_4219290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_4219290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219290 prefixEnd_4219290 := by exact prefixLift 4219290
  have htrace : WordTrace (prefixWord ++ tailWord_4219290) baseStart_4219290 baseEnd_4219290 := by
    simpa [prefixWord, tailWord_4219290, baseEnd_4219290] using wordTrace_append hprefix tailTrace_4219290
  have hstable : (prefixWord ++ tailWord_4219290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219290).length < 2 ^ (prefixWord ++ tailWord_4219290).sum := by decide
  have hdescent : baseEnd_4219290 < baseStart_4219290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219392 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 7]
def baseStart_4219392 : Nat := 118140960795 + 4219392 * 2 ^ 59
def prefixEnd_4219392 : Nat := 4983230072969 + 3 ^ 40 * 4219392 * 2
def baseEnd_4219392 : Nat := 2166576165735660843095375

theorem tailTrace_4219392 : CollatzResearch.WordTrace tailWord_4219392 prefixEnd_4219392 2166576165735660843095375 := by
  unfold tailWord_4219392
  simp only [CollatzResearch.WordTrace]
  refine ⟨76946934564935436813818215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102595912753247249085090953 76946934564935436813818215)
  ·
    refine ⟨115420401847403155220727323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76946934564935436813818215 115420401847403155220727323)
    ·
      refine ⟨173130602771104732831090985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115420401847403155220727323 173130602771104732831090985)
      ·
        refine ⟨129847952078328549623318239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173130602771104732831090985 129847952078328549623318239)
        ·
          refine ⟨194771928117492824434977359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129847952078328549623318239 194771928117492824434977359)
          ·
            refine ⟨292157892176239236652466039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194771928117492824434977359 292157892176239236652466039)
            ·
              refine ⟨438236838264358854978699059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292157892176239236652466039 438236838264358854978699059)
              ·
                refine ⟨657355257396538282468048589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438236838264358854978699059 657355257396538282468048589)
                ·
                  refine ⟨246508221523701855925518221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657355257396538282468048589 246508221523701855925518221)
                  ·
                    refine ⟨92440583071388195972069333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246508221523701855925518221 92440583071388195972069333)
                    ·
                      refine ⟨2166576165735660843095375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92440583071388195972069333 2166576165735660843095375)
                      ·
                        rfl

theorem cell23_4219392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_4219392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219392 prefixEnd_4219392 := by exact prefixLift 4219392
  have htrace : WordTrace (prefixWord ++ tailWord_4219392) baseStart_4219392 baseEnd_4219392 := by
    simpa [prefixWord, tailWord_4219392, baseEnd_4219392] using wordTrace_append hprefix tailTrace_4219392
  have hstable : (prefixWord ++ tailWord_4219392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219392).length < 2 ^ (prefixWord ++ tailWord_4219392).sum := by decide
  have hdescent : baseEnd_4219392 < baseStart_4219392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219429 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 1, 6]
def baseStart_4219429 : Nat := 118140960795 + 4219429 * 2 ^ 59
def prefixEnd_4219429 : Nat := 4983230072969 + 3 ^ 40 * 4219429 * 2
def baseEnd_4219429 : Nat := 722198388173292399444235

theorem tailTrace_4219429 : CollatzResearch.WordTrace tailWord_4219429 prefixEnd_4219429 722198388173292399444235 := by
  unfold tailWord_4219429
  simp only [CollatzResearch.WordTrace]
  refine ⟨153895218630736828946733341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102596812420491219297822227 153895218630736828946733341)
  ·
    refine ⟨57710706986526310855025003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153895218630736828946733341 57710706986526310855025003)
    ·
      refine ⟨86566060479789466282537505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57710706986526310855025003 86566060479789466282537505)
      ·
        refine ⟨64924545359842099711903129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86566060479789466282537505 64924545359842099711903129)
        ·
          refine ⟨48693409019881574783927347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64924545359842099711903129 48693409019881574783927347)
          ·
            refine ⟨73040113529822362175891021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48693409019881574783927347 73040113529822362175891021)
            ·
              refine ⟨27390042573683385815959133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73040113529822362175891021 27390042573683385815959133)
              ·
                refine ⟨10271265965131269680984675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27390042573683385815959133 10271265965131269680984675)
                ·
                  refine ⟨15406898947696904521477013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10271265965131269680984675 15406898947696904521477013)
                  ·
                    refine ⟨722198388173292399444235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15406898947696904521477013 722198388173292399444235)
                    ·
                      rfl

theorem cell23_4219429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_4219429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219429 prefixEnd_4219429 := by exact prefixLift 4219429
  have htrace : WordTrace (prefixWord ++ tailWord_4219429) baseStart_4219429 baseEnd_4219429 := by
    simpa [prefixWord, tailWord_4219429, baseEnd_4219429] using wordTrace_append hprefix tailTrace_4219429
  have hstable : (prefixWord ++ tailWord_4219429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219429).length < 2 ^ (prefixWord ++ tailWord_4219429).sum := by decide
  have hdescent : baseEnd_4219429 < baseStart_4219429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219453 : List Nat := [1, 4, 1, 3, 2, 2, 1, 3, 1, 1, 4]
def baseStart_4219453 : Nat := 118140960795 + 4219453 * 2 ^ 59
def prefixEnd_4219453 : Nat := 4983230072969 + 3 ^ 40 * 4219453 * 2
def baseEnd_4219453 : Nat := 2166607488055585104432595

theorem tailTrace_4219453 : CollatzResearch.WordTrace tailWord_4219453 prefixEnd_4219453 2166607488055585104432595 := by
  unfold tailWord_4219453
  simp only [CollatzResearch.WordTrace]
  refine ⟨153896093982649881045607013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102597395988433254030404675 153896093982649881045607013)
  ·
    refine ⟨28855517621746852696051315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153896093982649881045607013 28855517621746852696051315)
    ·
      refine ⟨43283276432620279044076973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28855517621746852696051315 43283276432620279044076973)
      ·
        refine ⟨16231228662232604641528865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43283276432620279044076973 16231228662232604641528865)
        ·
          refine ⟨12173421496674453481146649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16231228662232604641528865 12173421496674453481146649)
          ·
            refine ⟨9130066122505840110859987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12173421496674453481146649 9130066122505840110859987)
            ·
              refine ⟨13695099183758760166289981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9130066122505840110859987 13695099183758760166289981)
              ·
                refine ⟨5135662193909535062358743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13695099183758760166289981 5135662193909535062358743)
                ·
                  refine ⟨7703493290864302593538115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5135662193909535062358743 7703493290864302593538115)
                  ·
                    refine ⟨11555239936296453890307173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7703493290864302593538115 11555239936296453890307173)
                    ·
                      refine ⟨2166607488055585104432595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11555239936296453890307173 2166607488055585104432595)
                      ·
                        rfl

theorem cell23_4219453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_4219453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219453 prefixEnd_4219453 := by exact prefixLift 4219453
  have htrace : WordTrace (prefixWord ++ tailWord_4219453) baseStart_4219453 baseEnd_4219453 := by
    simpa [prefixWord, tailWord_4219453, baseEnd_4219453] using wordTrace_append hprefix tailTrace_4219453
  have hstable : (prefixWord ++ tailWord_4219453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219453).length < 2 ^ (prefixWord ++ tailWord_4219453).sum := by decide
  have hdescent : baseEnd_4219453 < baseStart_4219453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219463 : List Nat := [1, 1, 4, 1, 4, 1, 3, 2, 2, 4]
def baseStart_4219463 : Nat := 118140960795 + 4219463 * 2 ^ 59
def prefixEnd_4219463 : Nat := 4983230072969 + 3 ^ 40 * 4219463 * 2
def baseEnd_4219463 : Nat := 722204207620710021769183

theorem tailTrace_4219463 : CollatzResearch.WordTrace tailWord_4219463 prefixEnd_4219463 722204207620710021769183 := by
  unfold tailWord_4219463
  simp only [CollatzResearch.WordTrace]
  refine ⟨153896458712613652753471043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102597639141742435168980695 153896458712613652753471043)
  ·
    refine ⟨230844688068920479130206565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153896458712613652753471043 230844688068920479130206565)
    ·
      refine ⟨43283379012922589836913731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230844688068920479130206565 43283379012922589836913731)
      ·
        refine ⟨64925068519383884755370597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43283379012922589836913731 64925068519383884755370597)
        ·
          refine ⟨12173450347384478391631987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64925068519383884755370597 12173450347384478391631987)
          ·
            refine ⟨18260175521076717587447981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12173450347384478391631987 18260175521076717587447981)
            ·
              refine ⟨6847565820403769095292993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18260175521076717587447981 6847565820403769095292993)
              ·
                refine ⟨5135674365302826821469745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6847565820403769095292993 5135674365302826821469745)
                ·
                  refine ⟨3851755773977120116102309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5135674365302826821469745 3851755773977120116102309)
                  ·
                    refine ⟨722204207620710021769183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3851755773977120116102309 722204207620710021769183)
                    ·
                      rfl

theorem cell23_4219463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_4219463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219463 prefixEnd_4219463 := by exact prefixLift 4219463
  have htrace : WordTrace (prefixWord ++ tailWord_4219463) baseStart_4219463 baseEnd_4219463 := by
    simpa [prefixWord, tailWord_4219463, baseEnd_4219463] using wordTrace_append hprefix tailTrace_4219463
  have hstable : (prefixWord ++ tailWord_4219463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219463).length < 2 ^ (prefixWord ++ tailWord_4219463).sum := by decide
  have hdescent : baseEnd_4219463 < baseStart_4219463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219493 : List Nat := [1, 3, 1, 3, 4, 2, 2, 7]
def baseStart_4219493 : Nat := 118140960795 + 4219493 * 2 ^ 59
def prefixEnd_4219493 : Nat := 4983230072969 + 3 ^ 40 * 4219493 * 2
def baseEnd_4219493 : Nat := 80245482491917220293793

theorem tailTrace_4219493 : CollatzResearch.WordTrace tailWord_4219493 prefixEnd_4219493 80245482491917220293793 := by
  unfold tailWord_4219493
  simp only [CollatzResearch.WordTrace]
  refine ⟨153897552902504967877063133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102598368601669978584708755 153897552902504967877063133)
  ·
    refine ⟨57711582338439362953898675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153897552902504967877063133 57711582338439362953898675)
    ·
      refine ⟨86567373507659044430848013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57711582338439362953898675 86567373507659044430848013)
      ·
        refine ⟨32462765065372141661568005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86567373507659044430848013 32462765065372141661568005)
        ·
          refine ⟨6086768449757276561544001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32462765065372141661568005 6086768449757276561544001)
          ·
            refine ⟨4565076337317957421158001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6086768449757276561544001 4565076337317957421158001)
            ·
              refine ⟨3423807252988468065868501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4565076337317957421158001 3423807252988468065868501)
              ·
                refine ⟨80245482491917220293793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3423807252988468065868501 80245482491917220293793)
                ·
                  rfl

theorem cell23_4219493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 7].length) (baseStart_4219493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219493 prefixEnd_4219493 := by exact prefixLift 4219493
  have htrace : WordTrace (prefixWord ++ tailWord_4219493) baseStart_4219493 baseEnd_4219493 := by
    simpa [prefixWord, tailWord_4219493, baseEnd_4219493] using wordTrace_append hprefix tailTrace_4219493
  have hstable : (prefixWord ++ tailWord_4219493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219493).length < 2 ^ (prefixWord ++ tailWord_4219493).sum := by decide
  have hdescent : baseEnd_4219493 < baseStart_4219493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219504 : List Nat := [2, 1, 1, 1, 7, 2, 1, 3, 1, 2, 2]
def baseStart_4219504 : Nat := 118140960795 + 4219504 * 2 ^ 59
def prefixEnd_4219504 : Nat := 4983230072969 + 3 ^ 40 * 4219504 * 2
def baseEnd_4219504 : Nat := 2166633675568964404894861

theorem tailTrace_4219504 : CollatzResearch.WordTrace tailWord_4219504 prefixEnd_4219504 2166633675568964404894861 := by
  unfold tailWord_4219504
  simp only [CollatzResearch.WordTrace]
  refine ⟨76948977052732558377856783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102598636070310077837142377 76948977052732558377856783)
  ·
    refine ⟨115423465579098837566785175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76948977052732558377856783 115423465579098837566785175)
    ·
      refine ⟨173135198368648256350177763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115423465579098837566785175 173135198368648256350177763)
      ·
        refine ⟨259702797552972384525266645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173135198368648256350177763 259702797552972384525266645)
        ·
          refine ⟨6086784317647790262310937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 259702797552972384525266645 6086784317647790262310937)
          ·
            refine ⟨4565088238235842696733203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6086784317647790262310937 4565088238235842696733203)
            ·
              refine ⟨6847632357353764045099805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4565088238235842696733203 6847632357353764045099805)
              ·
                refine ⟨2567862134007661516912427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6847632357353764045099805 2567862134007661516912427)
                ·
                  refine ⟨3851793201011492275368641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2567862134007661516912427 3851793201011492275368641)
                  ·
                    refine ⟨2888844900758619206526481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3851793201011492275368641 2888844900758619206526481)
                    ·
                      refine ⟨2166633675568964404894861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2888844900758619206526481 2166633675568964404894861)
                      ·
                        rfl

theorem cell23_4219504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 1, 2, 2].length) (baseStart_4219504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219504 prefixEnd_4219504 := by exact prefixLift 4219504
  have htrace : WordTrace (prefixWord ++ tailWord_4219504) baseStart_4219504 baseEnd_4219504 := by
    simpa [prefixWord, tailWord_4219504, baseEnd_4219504] using wordTrace_append hprefix tailTrace_4219504
  have hstable : (prefixWord ++ tailWord_4219504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219504).length < 2 ^ (prefixWord ++ tailWord_4219504).sum := by decide
  have hdescent : baseEnd_4219504 < baseStart_4219504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219519 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 2, 6]
def baseStart_4219519 : Nat := 118140960795 + 4219519 * 2 ^ 59
def prefixEnd_4219519 : Nat := 4983230072969 + 3 ^ 40 * 4219519 * 2
def baseEnd_4219519 : Nat := 722213792592927282069097

theorem tailTrace_4219519 : CollatzResearch.WordTrace tailWord_4219519 prefixEnd_4219519 722213792592927282069097 := by
  unfold tailWord_4219519
  simp only [CollatzResearch.WordTrace]
  refine ⟨153898501200410774317509611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102599000800273849545006407 153898501200410774317509611)
  ·
    refine ⟨230847751800616161476264417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153898501200410774317509611 230847751800616161476264417)
    ·
      refine ⟨173135813850462121107198313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230847751800616161476264417 173135813850462121107198313)
      ·
        refine ⟨129851860387846590830398735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173135813850462121107198313 129851860387846590830398735)
        ·
          refine ⟨194777790581769886245598103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129851860387846590830398735 194777790581769886245598103)
          ·
            refine ⟨292166685872654829368397155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194777790581769886245598103 292166685872654829368397155)
            ·
              refine ⟨438250028808982244052595733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292166685872654829368397155 438250028808982244052595733)
              ·
                refine ⟨20542970100421042689965425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 438250028808982244052595733 20542970100421042689965425)
                ·
                  refine ⟨15407227575315782017474069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20542970100421042689965425 15407227575315782017474069)
                  ·
                    refine ⟨722213792592927282069097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15407227575315782017474069 722213792592927282069097)
                    ·
                      rfl

theorem cell23_4219519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 6].length) (baseStart_4219519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219519 prefixEnd_4219519 := by exact prefixLift 4219519
  have htrace : WordTrace (prefixWord ++ tailWord_4219519) baseStart_4219519 baseEnd_4219519 := by
    simpa [prefixWord, tailWord_4219519, baseEnd_4219519] using wordTrace_append hprefix tailTrace_4219519
  have hstable : (prefixWord ++ tailWord_4219519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219519).length < 2 ^ (prefixWord ++ tailWord_4219519).sum := by decide
  have hdescent : baseEnd_4219519 < baseStart_4219519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219529 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 3, 3, 5]
def baseStart_4219529 : Nat := 118140960795 + 4219529 * 2 ^ 59
def prefixEnd_4219529 : Nat := 4983230072969 + 3 ^ 40 * 4219529 * 2
def baseEnd_4219529 : Nat := 2166646512585326807082245

theorem tailTrace_4219529 : CollatzResearch.WordTrace tailWord_4219529 prefixEnd_4219529 2166646512585326807082245 := by
  unfold tailWord_4219529
  simp only [CollatzResearch.WordTrace]
  refine ⟨153898865930374546025373641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102599243953583030683582427 153898865930374546025373641)
  ·
    refine ⟨115424149447780909519030231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153898865930374546025373641 115424149447780909519030231)
    ·
      refine ⟨173136224171671364278545347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115424149447780909519030231 173136224171671364278545347)
      ·
        refine ⟨259704336257507046417818021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173136224171671364278545347 259704336257507046417818021)
        ·
          refine ⟨48694563048282571203340879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 259704336257507046417818021 48694563048282571203340879)
          ·
            refine ⟨73041844572423856805011319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48694563048282571203340879 73041844572423856805011319)
            ·
              refine ⟨109562766858635785207516979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73041844572423856805011319 109562766858635785207516979)
              ·
                refine ⟨164344150287953677811275469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109562766858635785207516979 164344150287953677811275469)
                ·
                  refine ⟨61629056357982629179228301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164344150287953677811275469 61629056357982629179228301)
                  ·
                    refine ⟨23110896134243485942210613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61629056357982629179228301 23110896134243485942210613)
                    ·
                      refine ⟨2166646512585326807082245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23110896134243485942210613 2166646512585326807082245)
                      ·
                        rfl

theorem cell23_4219529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_4219529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219529 prefixEnd_4219529 := by exact prefixLift 4219529
  have htrace : WordTrace (prefixWord ++ tailWord_4219529) baseStart_4219529 baseEnd_4219529 := by
    simpa [prefixWord, tailWord_4219529, baseEnd_4219529] using wordTrace_append hprefix tailTrace_4219529
  have hstable : (prefixWord ++ tailWord_4219529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219529).length < 2 ^ (prefixWord ++ tailWord_4219529).sum := by decide
  have hdescent : baseEnd_4219529 < baseStart_4219529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219543 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 1, 4, 2]
def baseStart_4219543 : Nat := 118140960795 + 4219543 * 2 ^ 59
def prefixEnd_4219543 : Nat := 4983230072969 + 3 ^ 40 * 4219543 * 2
def baseEnd_4219543 : Nat := 2166653701314489752307181

theorem tailTrace_4219543 : CollatzResearch.WordTrace tailWord_4219543 prefixEnd_4219543 2166653701314489752307181 := by
  unfold tailWord_4219543
  simp only [CollatzResearch.WordTrace]
  refine ⟨153899376552323826416383283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102599584368215884277588855 153899376552323826416383283)
  ·
    refine ⟨230849064828485739624574925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153899376552323826416383283 230849064828485739624574925)
    ·
      refine ⟨86568399310682152359215597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230849064828485739624574925 86568399310682152359215597)
      ·
        refine ⟨32463149741505807134705849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86568399310682152359215597 32463149741505807134705849)
        ·
          refine ⟨24347362306129355351029387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32463149741505807134705849 24347362306129355351029387)
          ·
            refine ⟨36521043459194033026544081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24347362306129355351029387 36521043459194033026544081)
            ·
              refine ⟨27390782594395524769908061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36521043459194033026544081 27390782594395524769908061)
              ·
                refine ⟨10271543472898321788715523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27390782594395524769908061 10271543472898321788715523)
                ·
                  refine ⟨15407315209347482683073285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10271543472898321788715523 15407315209347482683073285)
                  ·
                    refine ⟨2888871601752653003076241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15407315209347482683073285 2888871601752653003076241)
                    ·
                      refine ⟨2166653701314489752307181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2888871601752653003076241 2166653701314489752307181)
                      ·
                        rfl

theorem cell23_4219543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_4219543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219543 prefixEnd_4219543 := by exact prefixLift 4219543
  have htrace : WordTrace (prefixWord ++ tailWord_4219543) baseStart_4219543 baseEnd_4219543 := by
    simpa [prefixWord, tailWord_4219543, baseEnd_4219543] using wordTrace_append hprefix tailTrace_4219543
  have hstable : (prefixWord ++ tailWord_4219543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219543).length < 2 ^ (prefixWord ++ tailWord_4219543).sum := by decide
  have hdescent : baseEnd_4219543 < baseStart_4219543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219579 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 5, 7]
def baseStart_4219579 : Nat := 118140960795 + 4219579 * 2 ^ 59
def prefixEnd_4219579 : Nat := 4983230072969 + 3 ^ 40 * 4219579 * 2
def baseEnd_4219579 : Nat := 722224062206017203819005

theorem tailTrace_4219579 : CollatzResearch.WordTrace tailWord_4219579 prefixEnd_4219579 722224062206017203819005 := by
  unfold tailWord_4219579
  simp only [CollatzResearch.WordTrace]
  refine ⟨153900689580193404564693791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102600459720128936376462527 153900689580193404564693791)
  ·
    refine ⟨230851034370290106847040687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153900689580193404564693791 230851034370290106847040687)
    ·
      refine ⟨346276551555435160270561031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230851034370290106847040687 346276551555435160270561031)
      ·
        refine ⟨519414827333152740405841547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346276551555435160270561031 519414827333152740405841547)
        ·
          refine ⟨779122240999729110608762321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519414827333152740405841547 779122240999729110608762321)
          ·
            refine ⟨584341680749796832956571741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 779122240999729110608762321 584341680749796832956571741)
            ·
              refine ⟨219128130281173812358714403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 584341680749796832956571741 219128130281173812358714403)
              ·
                refine ⟨328692195421760718538071605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219128130281173812358714403 328692195421760718538071605)
                ·
                  refine ⟨30814893320790067362944213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 328692195421760718538071605 30814893320790067362944213)
                  ·
                    refine ⟨722224062206017203819005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30814893320790067362944213 722224062206017203819005)
                    ·
                      rfl

theorem cell23_4219579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 7].length) (baseStart_4219579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219579 prefixEnd_4219579 := by exact prefixLift 4219579
  have htrace : WordTrace (prefixWord ++ tailWord_4219579) baseStart_4219579 baseEnd_4219579 := by
    simpa [prefixWord, tailWord_4219579, baseEnd_4219579] using wordTrace_append hprefix tailTrace_4219579
  have hstable : (prefixWord ++ tailWord_4219579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219579).length < 2 ^ (prefixWord ++ tailWord_4219579).sum := by decide
  have hdescent : baseEnd_4219579 < baseStart_4219579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219583 : List Nat := [1, 1, 2, 2, 2, 5, 1, 4, 5]
def baseStart_4219583 : Nat := 118140960795 + 4219583 * 2 ^ 59
def prefixEnd_4219583 : Nat := 4983230072969 + 3 ^ 40 * 4219583 * 2
def baseEnd_4219583 : Nat := 240741582282296621756333

theorem tailTrace_4219583 : CollatzResearch.WordTrace tailWord_4219583 prefixEnd_4219583 240741582282296621756333 := by
  unfold tailWord_4219583
  simp only [CollatzResearch.WordTrace]
  refine ⟨153900835472178913247839403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102600556981452608831892935 153900835472178913247839403)
  ·
    refine ⟨230851253208268369871759105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153900835472178913247839403 230851253208268369871759105)
    ·
      refine ⟨173138439906201277403819329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230851253208268369871759105 173138439906201277403819329)
      ·
        refine ⟨129853829929650958052864497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173138439906201277403819329 129853829929650958052864497)
        ·
          refine ⟨97390372447238218539648373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129853829929650958052864497 97390372447238218539648373)
          ·
            refine ⟨9130347416928582988092035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97390372447238218539648373 9130347416928582988092035)
            ·
              refine ⟨13695521125392874482138053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9130347416928582988092035 13695521125392874482138053)
              ·
                refine ⟨2567910211011163965400885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13695521125392874482138053 2567910211011163965400885)
                ·
                  refine ⟨240741582282296621756333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2567910211011163965400885 240741582282296621756333)
                  ·
                    rfl

theorem cell23_4219583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 5].length) (baseStart_4219583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219583 prefixEnd_4219583 := by exact prefixLift 4219583
  have htrace : WordTrace (prefixWord ++ tailWord_4219583) baseStart_4219583 baseEnd_4219583 := by
    simpa [prefixWord, tailWord_4219583, baseEnd_4219583] using wordTrace_append hprefix tailTrace_4219583
  have hstable : (prefixWord ++ tailWord_4219583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219583).length < 2 ^ (prefixWord ++ tailWord_4219583).sum := by decide
  have hdescent : baseEnd_4219583 < baseStart_4219583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219633 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 4, 4, 2]
def baseStart_4219633 : Nat := 118140960795 + 4219633 * 2 ^ 59
def prefixEnd_4219633 : Nat := 4983230072969 + 3 ^ 40 * 4219633 * 2
def baseEnd_4219633 : Nat := 2166699914573394400181767

theorem tailTrace_4219633 : CollatzResearch.WordTrace tailWord_4219633 prefixEnd_4219633 2166699914573394400181767 := by
  unfold tailWord_4219633
  simp only [CollatzResearch.WordTrace]
  refine ⟨153902659121997771787159553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102601772747998514524773035 153902659121997771787159553)
  ·
    refine ⟨115426994341498328840369665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153902659121997771787159553 115426994341498328840369665)
    ·
      refine ⟨86570245756123746630277249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115426994341498328840369665 86570245756123746630277249)
      ·
        refine ⟨64927684317092809972707937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86570245756123746630277249 64927684317092809972707937)
        ·
          refine ⟨48695763237819607479530953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64927684317092809972707937 48695763237819607479530953)
          ·
            refine ⟨36521822428364705609648215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48695763237819607479530953 36521822428364705609648215)
            ·
              refine ⟨54782733642547058414472323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36521822428364705609648215 54782733642547058414472323)
              ·
                refine ⟨82174100463820587621708485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54782733642547058414472323 82174100463820587621708485)
                ·
                  refine ⟨15407643836966360179070341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82174100463820587621708485 15407643836966360179070341)
                  ·
                    refine ⟨2888933219431192533575689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15407643836966360179070341 2888933219431192533575689)
                    ·
                      refine ⟨2166699914573394400181767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2888933219431192533575689 2166699914573394400181767)
                      ·
                        rfl

theorem cell23_4219633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_4219633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219633 prefixEnd_4219633 := by exact prefixLift 4219633
  have htrace : WordTrace (prefixWord ++ tailWord_4219633) baseStart_4219633 baseEnd_4219633 := by
    simpa [prefixWord, tailWord_4219633, baseEnd_4219633] using wordTrace_append hprefix tailTrace_4219633
  have hstable : (prefixWord ++ tailWord_4219633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219633).length < 2 ^ (prefixWord ++ tailWord_4219633).sum := by decide
  have hdescent : baseEnd_4219633 < baseStart_4219633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219733 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 1, 6]
def baseStart_4219733 : Nat := 118140960795 + 4219733 * 2 ^ 59
def prefixEnd_4219733 : Nat := 4983230072969 + 3 ^ 40 * 4219733 * 2
def baseEnd_4219733 : Nat := 722250420879614669643769

theorem tailTrace_4219733 : CollatzResearch.WordTrace tailWord_4219733 prefixEnd_4219733 722250420879614669643769 := by
  unfold tailWord_4219733
  simp only [CollatzResearch.WordTrace]
  refine ⟨153906306421635488865799853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102604204281090325910533235 153906306421635488865799853)
  ·
    refine ⟨57714864908113308324674945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153906306421635488865799853 57714864908113308324674945)
    ·
      refine ⟨43286148681084981243506209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57714864908113308324674945 43286148681084981243506209)
      ·
        refine ⟨32464611510813735932629657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43286148681084981243506209 32464611510813735932629657)
        ·
          refine ⟨24348458633110301949472243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32464611510813735932629657 24348458633110301949472243)
          ·
            refine ⟨36522687949665452924208365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24348458633110301949472243 36522687949665452924208365)
            ·
              refine ⟨13696007981124544846578137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36522687949665452924208365 13696007981124544846578137)
              ·
                refine ⟨10272005985843408634933603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13696007981124544846578137 10272005985843408634933603)
                ·
                  refine ⟨15408008978765112952400405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10272005985843408634933603 15408008978765112952400405)
                  ·
                    refine ⟨722250420879614669643769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15408008978765112952400405 722250420879614669643769)
                    ·
                      rfl

theorem cell23_4219733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_4219733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219733 prefixEnd_4219733 := by exact prefixLift 4219733
  have htrace : WordTrace (prefixWord ++ tailWord_4219733) baseStart_4219733 baseEnd_4219733 := by
    simpa [prefixWord, tailWord_4219733, baseEnd_4219733] using wordTrace_append hprefix tailTrace_4219733
  have hstable : (prefixWord ++ tailWord_4219733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219733).length < 2 ^ (prefixWord ++ tailWord_4219733).sum := by decide
  have hdescent : baseEnd_4219733 < baseStart_4219733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219751 : List Nat := [1, 1, 5, 1, 2, 4, 2, 2, 1, 1, 3]
def baseStart_4219751 : Nat := 118140960795 + 4219751 * 2 ^ 59
def prefixEnd_4219751 : Nat := 4983230072969 + 3 ^ 40 * 4219751 * 2
def baseEnd_4219751 : Nat := 2166760505290624938506225

theorem tailTrace_4219751 : CollatzResearch.WordTrace tailWord_4219751 prefixEnd_4219751 2166760505290624938506225 := by
  unfold tailWord_4219751
  simp only [CollatzResearch.WordTrace]
  refine ⟨153906962935570277939955107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102604641957046851959970071 153906962935570277939955107)
  ·
    refine ⟨230860444403355416909932661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153906962935570277939955107 230860444403355416909932661)
    ·
      refine ⟨21643166662814570335306187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 230860444403355416909932661 21643166662814570335306187)
      ·
        refine ⟨32464749994221855502959281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21643166662814570335306187 32464749994221855502959281)
        ·
          refine ⟨24348562495666391627219461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32464749994221855502959281 24348562495666391627219461)
          ·
            refine ⟨4565355467937448430103649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24348562495666391627219461 4565355467937448430103649)
            ·
              refine ⟨3424016600953086322577737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4565355467937448430103649 3424016600953086322577737)
              ·
                refine ⟨2568012450714814741933303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3424016600953086322577737 2568012450714814741933303)
                ·
                  refine ⟨3852018676072222112899955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568012450714814741933303 3852018676072222112899955)
                  ·
                    refine ⟨5778028014108333169349933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3852018676072222112899955 5778028014108333169349933)
                    ·
                      refine ⟨2166760505290624938506225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5778028014108333169349933 2166760505290624938506225)
                      ·
                        rfl

theorem cell23_4219751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_4219751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219751 prefixEnd_4219751 := by exact prefixLift 4219751
  have htrace : WordTrace (prefixWord ++ tailWord_4219751) baseStart_4219751 baseEnd_4219751 := by
    simpa [prefixWord, tailWord_4219751, baseEnd_4219751] using wordTrace_append hprefix tailTrace_4219751
  have hstable : (prefixWord ++ tailWord_4219751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219751).length < 2 ^ (prefixWord ++ tailWord_4219751).sum := by decide
  have hdescent : baseEnd_4219751 < baseStart_4219751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219757 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_4219757 : Nat := 118140960795 + 4219757 * 2 ^ 59
def prefixEnd_4219757 : Nat := 4983230072969 + 3 ^ 40 * 4219757 * 2
def baseEnd_4219757 : Nat := 2166763586174551915031197

theorem tailTrace_4219757 : CollatzResearch.WordTrace tailWord_4219757 prefixEnd_4219757 2166763586174551915031197 := by
  unfold tailWord_4219757
  simp only [CollatzResearch.WordTrace]
  refine ⟨153907181773548540964673525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102604787849032360643115683 153907181773548540964673525)
  ·
    refine ⟨14428798291270175715438143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153907181773548540964673525 14428798291270175715438143)
    ·
      refine ⟨21643197436905263573157215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14428798291270175715438143 21643197436905263573157215)
      ·
        refine ⟨32464796155357895359735823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21643197436905263573157215 32464796155357895359735823)
        ·
          refine ⟨48697194233036843039603735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32464796155357895359735823 48697194233036843039603735)
          ·
            refine ⟨73045791349555264559405603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48697194233036843039603735 73045791349555264559405603)
            ·
              refine ⟨109568687024332896839108405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73045791349555264559405603 109568687024332896839108405)
              ·
                refine ⟨10272064408531209078666413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109568687024332896839108405 10272064408531209078666413)
                ·
                  refine ⟨3852024153199203404499905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10272064408531209078666413 3852024153199203404499905)
                  ·
                    refine ⟨2889018114899402553374929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3852024153199203404499905 2889018114899402553374929)
                    ·
                      refine ⟨2166763586174551915031197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2889018114899402553374929 2166763586174551915031197)
                      ·
                        rfl

theorem cell23_4219757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_4219757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219757 prefixEnd_4219757 := by exact prefixLift 4219757
  have htrace : WordTrace (prefixWord ++ tailWord_4219757) baseStart_4219757 baseEnd_4219757 := by
    simpa [prefixWord, tailWord_4219757, baseEnd_4219757] using wordTrace_append hprefix tailTrace_4219757
  have hstable : (prefixWord ++ tailWord_4219757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219757).length < 2 ^ (prefixWord ++ tailWord_4219757).sum := by decide
  have hdescent : baseEnd_4219757 < baseStart_4219757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219778 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_4219778 : Nat := 118140960795 + 4219778 * 2 ^ 59
def prefixEnd_4219778 : Nat := 4983230072969 + 3 ^ 40 * 4219778 * 2
def baseEnd_4219778 : Nat := 2166774369268296332868601

theorem tailTrace_4219778 : CollatzResearch.WordTrace tailWord_4219778 prefixEnd_4219778 2166774369268296332868601 := by
  unfold tailWord_4219778
  simp only [CollatzResearch.WordTrace]
  refine ⟨38476986926618115387796997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102605298470981641034125325 38476986926618115387796997)
  ·
    refine ⟨7214435048740896635211937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38476986926618115387796997 7214435048740896635211937)
    ·
      refine ⟨5410826286555672476408953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7214435048740896635211937 5410826286555672476408953)
      ·
        refine ⟨4058119714916754357306715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5410826286555672476408953 4058119714916754357306715)
        ·
          refine ⟨6087179572375131535960073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4058119714916754357306715 6087179572375131535960073)
          ·
            refine ⟨4565384679281348651970055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6087179572375131535960073 4565384679281348651970055)
            ·
              refine ⟨6848077018922022977955083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4565384679281348651970055 6848077018922022977955083)
              ·
                refine ⟨10272115528383034466932625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6848077018922022977955083 10272115528383034466932625)
                ·
                  refine ⟨7704086646287275850199469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10272115528383034466932625 7704086646287275850199469)
                  ·
                    refine ⟨2889032492357728443824801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7704086646287275850199469 2889032492357728443824801)
                    ·
                      refine ⟨2166774369268296332868601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2889032492357728443824801 2166774369268296332868601)
                      ·
                        rfl

theorem cell23_4219778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_4219778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219778 prefixEnd_4219778 := by exact prefixLift 4219778
  have htrace : WordTrace (prefixWord ++ tailWord_4219778) baseStart_4219778 baseEnd_4219778 := by
    simpa [prefixWord, tailWord_4219778, baseEnd_4219778] using wordTrace_append hprefix tailTrace_4219778
  have hstable : (prefixWord ++ tailWord_4219778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219778).length < 2 ^ (prefixWord ++ tailWord_4219778).sum := by decide
  have hdescent : baseEnd_4219778 < baseStart_4219778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219794 : List Nat := [3, 2, 3, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_4219794 : Nat := 118140960795 + 4219794 * 2 ^ 59
def prefixEnd_4219794 : Nat := 4983230072969 + 3 ^ 40 * 4219794 * 2
def baseEnd_4219794 : Nat := 2166782584958768270268527

theorem tailTrace_4219794 : CollatzResearch.WordTrace tailWord_4219794 prefixEnd_4219794 2166782584958768270268527 := by
  unfold tailWord_4219794
  simp only [CollatzResearch.WordTrace]
  refine ⟨38477132818603624070942609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102605687516276330855846957 38477132818603624070942609)
  ·
    refine ⟨28857849613952718053206957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38477132818603624070942609 28857849613952718053206957)
    ·
      refine ⟨10821693605232269269952609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28857849613952718053206957 10821693605232269269952609)
      ·
        refine ⟨8116270203924201952464457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10821693605232269269952609 8116270203924201952464457)
        ·
          refine ⟨6087202652943151464348343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8116270203924201952464457 6087202652943151464348343)
          ·
            refine ⟨9130803979414727196522515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6087202652943151464348343 9130803979414727196522515)
            ·
              refine ⟨13696205969122090794783773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9130803979414727196522515 13696205969122090794783773)
              ·
                refine ⟨5136077238420784048043915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13696205969122090794783773 5136077238420784048043915)
                ·
                  refine ⟨7704115857631176072065873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5136077238420784048043915 7704115857631176072065873)
                  ·
                    refine ⟨5778086893223382054049405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7704115857631176072065873 5778086893223382054049405)
                    ·
                      refine ⟨2166782584958768270268527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5778086893223382054049405 2166782584958768270268527)
                      ·
                        rfl

theorem cell23_4219794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_4219794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219794 prefixEnd_4219794 := by exact prefixLift 4219794
  have htrace : WordTrace (prefixWord ++ tailWord_4219794) baseStart_4219794 baseEnd_4219794 := by
    simpa [prefixWord, tailWord_4219794, baseEnd_4219794] using wordTrace_append hprefix tailTrace_4219794
  have hstable : (prefixWord ++ tailWord_4219794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219794).length < 2 ^ (prefixWord ++ tailWord_4219794).sum := by decide
  have hdescent : baseEnd_4219794 < baseStart_4219794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219807 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 4, 1, 3]
def baseStart_4219807 : Nat := 118140960795 + 4219807 * 2 ^ 59
def prefixEnd_4219807 : Nat := 4983230072969 + 3 ^ 40 * 4219807 * 2
def baseEnd_4219807 : Nat := 2166789260207276719405967

theorem tailTrace_4219807 : CollatzResearch.WordTrace tailWord_4219807 prefixEnd_4219807 2166789260207276719405967 := by
  unfold tailWord_4219807
  simp only [CollatzResearch.WordTrace]
  refine ⟨153909005423367399503993675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102606003615578266335995783 153909005423367399503993675)
  ·
    refine ⟨230863508135051099255990513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153909005423367399503993675 230863508135051099255990513)
    ·
      refine ⟨173147631101288324441992885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230863508135051099255990513 173147631101288324441992885)
      ·
        refine ⟨16232590415745780416436833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 173147631101288324441992885 16232590415745780416436833)
        ·
          refine ⟨12174442811809335312327625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16232590415745780416436833 12174442811809335312327625)
          ·
            refine ⟨9130832108857001484245719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12174442811809335312327625 9130832108857001484245719)
            ·
              refine ⟨13696248163285502226368579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9130832108857001484245719 13696248163285502226368579)
              ·
                refine ⟨20544372244928253339552869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13696248163285502226368579 20544372244928253339552869)
                ·
                  refine ⟨3852069795924047501166163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20544372244928253339552869 3852069795924047501166163)
                  ·
                    refine ⟨5778104693886071251749245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3852069795924047501166163 5778104693886071251749245)
                    ·
                      refine ⟨2166789260207276719405967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5778104693886071251749245 2166789260207276719405967)
                      ·
                        rfl

theorem cell23_4219807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_4219807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219807 prefixEnd_4219807 := by exact prefixLift 4219807
  have htrace : WordTrace (prefixWord ++ tailWord_4219807) baseStart_4219807 baseEnd_4219807 := by
    simpa [prefixWord, tailWord_4219807, baseEnd_4219807] using wordTrace_append hprefix tailTrace_4219807
  have hstable : (prefixWord ++ tailWord_4219807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219807).length < 2 ^ (prefixWord ++ tailWord_4219807).sum := by decide
  have hdescent : baseEnd_4219807 < baseStart_4219807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219821 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_4219821 : Nat := 118140960795 + 4219821 * 2 ^ 59
def prefixEnd_4219821 : Nat := 4983230072969 + 3 ^ 40 * 4219821 * 2
def baseEnd_4219821 : Nat := 2166796448936439664630903

theorem tailTrace_4219821 : CollatzResearch.WordTrace tailWord_4219821 prefixEnd_4219821 2166796448936439664630903 := by
  unfold tailWord_4219821
  simp only [CollatzResearch.WordTrace]
  refine ⟨153909516045316679895003317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102606344030211119930002211 153909516045316679895003317)
  ·
    refine ⟨14429017129248438740156561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153909516045316679895003317 14429017129248438740156561)
    ·
      refine ⟨10821762846936329055117421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14429017129248438740156561 10821762846936329055117421)
      ·
        refine ⟨4058161067601123395669033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10821762846936329055117421 4058161067601123395669033)
        ·
          refine ⟨3043620800700842546751775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4058161067601123395669033 3043620800700842546751775)
          ·
            refine ⟨4565431201051263820127663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3043620800700842546751775 4565431201051263820127663)
            ·
              refine ⟨6848146801576895730191495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4565431201051263820127663 6848146801576895730191495)
              ·
                refine ⟨10272220202365343595287243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6848146801576895730191495 10272220202365343595287243)
                ·
                  refine ⟨15408330303548015392930865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10272220202365343595287243 15408330303548015392930865)
                  ·
                    refine ⟨11556247727661011544698149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15408330303548015392930865 11556247727661011544698149)
                    ·
                      refine ⟨2166796448936439664630903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11556247727661011544698149 2166796448936439664630903)
                      ·
                        rfl

theorem cell23_4219821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_4219821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219821 prefixEnd_4219821 := by exact prefixLift 4219821
  have htrace : WordTrace (prefixWord ++ tailWord_4219821) baseStart_4219821 baseEnd_4219821 := by
    simpa [prefixWord, tailWord_4219821, baseEnd_4219821] using wordTrace_append hprefix tailTrace_4219821
  have hstable : (prefixWord ++ tailWord_4219821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219821).length < 2 ^ (prefixWord ++ tailWord_4219821).sum := by decide
  have hdescent : baseEnd_4219821 < baseStart_4219821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219847 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 4, 2, 2]
def baseStart_4219847 : Nat := 118140960795 + 4219847 * 2 ^ 59
def prefixEnd_4219847 : Nat := 4983230072969 + 3 ^ 40 * 4219847 * 2
def baseEnd_4219847 : Nat := 2166809799433456562905783

theorem tailTrace_4219847 : CollatzResearch.WordTrace tailWord_4219847 prefixEnd_4219847 2166809799433456562905783 := by
  unfold tailWord_4219847
  simp only [CollatzResearch.WordTrace]
  refine ⟨153910464343222486335449795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102606976228814990890299863 153910464343222486335449795)
  ·
    refine ⟨230865696514833729503174693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153910464343222486335449795 230865696514833729503174693)
    ·
      refine ⟨43287318096531324281845255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230865696514833729503174693 43287318096531324281845255)
      ·
        refine ⟨64930977144796986422767883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43287318096531324281845255 64930977144796986422767883)
        ·
          refine ⟨97396465717195479634151825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64930977144796986422767883 97396465717195479634151825)
          ·
            refine ⟨73047349287896609725613869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97396465717195479634151825 73047349287896609725613869)
            ·
              refine ⟨27392755982961228647105201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73047349287896609725613869 27392755982961228647105201)
              ·
                refine ⟨20544566987220921485328901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27392755982961228647105201 20544566987220921485328901)
                ·
                  refine ⟨3852106310103922778499169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20544566987220921485328901 3852106310103922778499169)
                  ·
                    refine ⟨2889079732577942083874377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3852106310103922778499169 2889079732577942083874377)
                    ·
                      refine ⟨2166809799433456562905783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2889079732577942083874377 2166809799433456562905783)
                      ·
                        rfl

theorem cell23_4219847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_4219847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219847 prefixEnd_4219847 := by exact prefixLift 4219847
  have htrace : WordTrace (prefixWord ++ tailWord_4219847) baseStart_4219847 baseEnd_4219847 := by
    simpa [prefixWord, tailWord_4219847, baseEnd_4219847] using wordTrace_append hprefix tailTrace_4219847
  have hstable : (prefixWord ++ tailWord_4219847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219847).length < 2 ^ (prefixWord ++ tailWord_4219847).sum := by decide
  have hdescent : baseEnd_4219847 < baseStart_4219847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219880 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_4219880 : Nat := 118140960795 + 4219880 * 2 ^ 59
def prefixEnd_4219880 : Nat := 4983230072969 + 3 ^ 40 * 4219880 * 2
def baseEnd_4219880 : Nat := 2166826744295054933793131

theorem tailTrace_4219880 : CollatzResearch.WordTrace tailWord_4219880 prefixEnd_4219880 2166826744295054933793131 := by
  unfold tailWord_4219880
  simp only [CollatzResearch.WordTrace]
  refine ⟨76955833976051466485700547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102607778634735288647600729 76955833976051466485700547)
  ·
    refine ⟨115433750964077199728550821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76955833976051466485700547 115433750964077199728550821)
    ·
      refine ⟨21643828305764474949103279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115433750964077199728550821 21643828305764474949103279)
      ·
        refine ⟨32465742458646712423654919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21643828305764474949103279 32465742458646712423654919)
        ·
          refine ⟨48698613687970068635482379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32465742458646712423654919 48698613687970068635482379)
          ·
            refine ⟨73047920531955102953223569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48698613687970068635482379 73047920531955102953223569)
            ·
              refine ⟨54785940398966327214917677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73047920531955102953223569 54785940398966327214917677)
              ·
                refine ⟨20544727649612372705594129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54785940398966327214917677 20544727649612372705594129)
                ·
                  refine ⟨15408545737209279529195597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20544727649612372705594129 15408545737209279529195597)
                  ·
                    refine ⟨5778204651453479823448349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15408545737209279529195597 5778204651453479823448349)
                    ·
                      refine ⟨2166826744295054933793131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5778204651453479823448349 2166826744295054933793131)
                      ·
                        rfl

theorem cell23_4219880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_4219880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219880 prefixEnd_4219880 := by exact prefixLift 4219880
  have htrace : WordTrace (prefixWord ++ tailWord_4219880) baseStart_4219880 baseEnd_4219880 := by
    simpa [prefixWord, tailWord_4219880, baseEnd_4219880] using wordTrace_append hprefix tailTrace_4219880
  have hstable : (prefixWord ++ tailWord_4219880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219880).length < 2 ^ (prefixWord ++ tailWord_4219880).sum := by decide
  have hdescent : baseEnd_4219880 < baseStart_4219880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219900 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 2, 5]
def baseStart_4219900 : Nat := 118140960795 + 4219900 * 2 ^ 59
def prefixEnd_4219900 : Nat := 4983230072969 + 3 ^ 40 * 4219900 * 2
def baseEnd_4219900 : Nat := 722279004636048285181013

theorem tailTrace_4219900 : CollatzResearch.WordTrace tailWord_4219900 prefixEnd_4219900 722279004636048285181013 := by
  unfold tailWord_4219900
  simp only [CollatzResearch.WordTrace]
  refine ⟨76956198706015238193564577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102608264941353650924752769 76956198706015238193564577)
  ·
    refine ⟨57717149029511428645173433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76956198706015238193564577 57717149029511428645173433)
    ·
      refine ⟨43287861772133571483880075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57717149029511428645173433 43287861772133571483880075)
      ·
        refine ⟨64931792658200357225820113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43287861772133571483880075 64931792658200357225820113)
        ·
          refine ⟨48698844493650267919365085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64931792658200357225820113 48698844493650267919365085)
          ·
            refine ⟨18262066685118850469761907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48698844493650267919365085 18262066685118850469761907)
            ·
              refine ⟨27393100027678275704642861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18262066685118850469761907 27393100027678275704642861)
              ·
                refine ⟨10272412510379353389241073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27393100027678275704642861 10272412510379353389241073)
                ·
                  refine ⟨7704309382784515041930805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10272412510379353389241073 7704309382784515041930805)
                  ·
                    refine ⟨722279004636048285181013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7704309382784515041930805 722279004636048285181013)
                    ·
                      rfl

theorem cell23_4219900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_4219900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219900 prefixEnd_4219900 := by exact prefixLift 4219900
  have htrace : WordTrace (prefixWord ++ tailWord_4219900) baseStart_4219900 baseEnd_4219900 := by
    simpa [prefixWord, tailWord_4219900, baseEnd_4219900] using wordTrace_append hprefix tailTrace_4219900
  have hstable : (prefixWord ++ tailWord_4219900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219900).length < 2 ^ (prefixWord ++ tailWord_4219900).sum := by decide
  have hdescent : baseEnd_4219900 < baseStart_4219900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219923 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 5]
def baseStart_4219923 : Nat := 118140960795 + 4219923 * 2 ^ 59
def prefixEnd_4219923 : Nat := 4983230072969 + 3 ^ 40 * 4219923 * 2
def baseEnd_4219923 : Nat := 2166848823963198265555433

theorem tailTrace_4219923 : CollatzResearch.WordTrace tailWord_4219923 prefixEnd_4219923 2166848823963198265555433 := by
  unfold tailWord_4219923
  simp only [CollatzResearch.WordTrace]
  refine ⟨153913236290947151315216423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102608824193964767543477615 153913236290947151315216423)
  ·
    refine ⟨230869854436420726972824635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153913236290947151315216423 230869854436420726972824635)
    ·
      refine ⟨346304781654631090459236953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230869854436420726972824635 346304781654631090459236953)
      ·
        refine ⟨259728586240973317844427715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346304781654631090459236953 259728586240973317844427715)
        ·
          refine ⟨389592879361459976766641573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259728586240973317844427715 389592879361459976766641573)
          ·
            refine ⟨73048664880273745643745295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 389592879361459976766641573 73048664880273745643745295)
            ·
              refine ⟨109572997320410618465617943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73048664880273745643745295 109572997320410618465617943)
              ·
                refine ⟨164359495980615927698426915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109572997320410618465617943 164359495980615927698426915)
                ·
                  refine ⟨246539243970923891547640373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164359495980615927698426915 246539243970923891547640373)
                  ·
                    refine ⟨23113054122274114832591285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 246539243970923891547640373 23113054122274114832591285)
                    ·
                      refine ⟨2166848823963198265555433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23113054122274114832591285 2166848823963198265555433)
                      ·
                        rfl

theorem cell23_4219923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_4219923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219923 prefixEnd_4219923 := by exact prefixLift 4219923
  have htrace : WordTrace (prefixWord ++ tailWord_4219923) baseStart_4219923 baseEnd_4219923 := by
    simpa [prefixWord, tailWord_4219923, baseEnd_4219923] using wordTrace_append hprefix tailTrace_4219923
  have hstable : (prefixWord ++ tailWord_4219923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219923).length < 2 ^ (prefixWord ++ tailWord_4219923).sum := by decide
  have hdescent : baseEnd_4219923 < baseStart_4219923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219937 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 1, 6, 2]
def baseStart_4219937 : Nat := 118140960795 + 4219937 * 2 ^ 59
def prefixEnd_4219937 : Nat := 4983230072969 + 3 ^ 40 * 4219937 * 2
def baseEnd_4219937 : Nat := 2166856012692361210780369

theorem tailTrace_4219937 : CollatzResearch.WordTrace tailWord_4219937 prefixEnd_4219937 2166856012692361210780369 := by
  unfold tailWord_4219937
  simp only [CollatzResearch.WordTrace]
  refine ⟨153913746912896431706226065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102609164608597621137484043 153913746912896431706226065)
  ·
    refine ⟨115435310184672323779669549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153913746912896431706226065 115435310184672323779669549)
    ·
      refine ⟨43288241319252121417376081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115435310184672323779669549 43288241319252121417376081)
      ·
        refine ⟨32466180989439091063032061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43288241319252121417376081 32466180989439091063032061)
        ·
          refine ⟨12174817871039659148637023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32466180989439091063032061 12174817871039659148637023)
          ·
            refine ⟨18262226806559488722955535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12174817871039659148637023 18262226806559488722955535)
            ·
              refine ⟨27393340209839233084433303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18262226806559488722955535 27393340209839233084433303)
              ·
                refine ⟨41090010314758849626649955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27393340209839233084433303 41090010314758849626649955)
                ·
                  refine ⟨61635015472138274439974933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41090010314758849626649955 61635015472138274439974933)
                  ·
                    refine ⟨2889141350256481614373825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61635015472138274439974933 2889141350256481614373825)
                    ·
                      refine ⟨2166856012692361210780369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2889141350256481614373825 2166856012692361210780369)
                      ·
                        rfl

theorem cell23_4219937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_4219937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219937 prefixEnd_4219937 := by exact prefixLift 4219937
  have htrace : WordTrace (prefixWord ++ tailWord_4219937) baseStart_4219937 baseEnd_4219937 := by
    simpa [prefixWord, tailWord_4219937, baseEnd_4219937] using wordTrace_append hprefix tailTrace_4219937
  have hstable : (prefixWord ++ tailWord_4219937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219937).length < 2 ^ (prefixWord ++ tailWord_4219937).sum := by decide
  have hdescent : baseEnd_4219937 < baseStart_4219937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219963 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 8]
def baseStart_4219963 : Nat := 118140960795 + 4219963 * 2 ^ 59
def prefixEnd_4219963 : Nat := 4983230072969 + 3 ^ 40 * 4219963 * 2
def baseEnd_4219963 : Nat := 2166869363189378109055249

theorem tailTrace_4219963 : CollatzResearch.WordTrace tailWord_4219963 prefixEnd_4219963 2166869363189378109055249 := by
  unfold tailWord_4219963
  simp only [CollatzResearch.WordTrace]
  refine ⟨153914695210802238146672543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102609796807201492097781695 153914695210802238146672543)
  ·
    refine ⟨230872042816203357220008815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153914695210802238146672543 230872042816203357220008815)
    ·
      refine ⟨346308064224305035830013223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230872042816203357220008815 346308064224305035830013223)
      ·
        refine ⟨519462096336457553745019835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346308064224305035830013223 519462096336457553745019835)
        ·
          refine ⟨779193144504686330617529753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519462096336457553745019835 779193144504686330617529753)
          ·
            refine ⟨584394858378514747963147315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 779193144504686330617529753 584394858378514747963147315)
            ·
              refine ⟨876592287567772121944720973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584394858378514747963147315 876592287567772121944720973)
              ·
                refine ⟨328722107837914545729270365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 876592287567772121944720973 328722107837914545729270365)
                ·
                  refine ⟨123270790439217954648476387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328722107837914545729270365 123270790439217954648476387)
                  ·
                    refine ⟨184906185658826931972714581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123270790439217954648476387 184906185658826931972714581)
                    ·
                      refine ⟨2166869363189378109055249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 184906185658826931972714581 2166869363189378109055249)
                      ·
                        rfl

theorem cell23_4219963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_4219963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219963 prefixEnd_4219963 := by exact prefixLift 4219963
  have htrace : WordTrace (prefixWord ++ tailWord_4219963) baseStart_4219963 baseEnd_4219963 := by
    simpa [prefixWord, tailWord_4219963, baseEnd_4219963] using wordTrace_append hprefix tailTrace_4219963
  have hstable : (prefixWord ++ tailWord_4219963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219963).length < 2 ^ (prefixWord ++ tailWord_4219963).sum := by decide
  have hdescent : baseEnd_4219963 < baseStart_4219963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219964 : List Nat := [2, 2, 2, 2, 2, 2, 1, 5, 1, 4]
def baseStart_4219964 : Nat := 118140960795 + 4219964 * 2 ^ 59
def prefixEnd_4219964 : Nat := 4983230072969 + 3 ^ 40 * 4219964 * 2
def baseEnd_4219964 : Nat := 722289958890010868380915

theorem tailTrace_4219964 : CollatzResearch.WordTrace tailWord_4219964 prefixEnd_4219964 722289958890010868380915 := by
  unfold tailWord_4219964
  simp only [CollatzResearch.WordTrace]
  refine ⟨76957365841899307658729473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102609821122532410211639297 76957365841899307658729473)
  ·
    refine ⟨57718024381424480744047105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76957365841899307658729473 57718024381424480744047105)
    ·
      refine ⟨43288518286068360558035329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57718024381424480744047105 43288518286068360558035329)
      ·
        refine ⟨32466388714551270418526497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43288518286068360558035329 32466388714551270418526497)
        ·
          refine ⟨24349791535913452813894873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32466388714551270418526497 24349791535913452813894873)
          ·
            refine ⟨18262343651935089610421155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24349791535913452813894873 18262343651935089610421155)
            ·
              refine ⟨27393515477902634415631733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18262343651935089610421155 27393515477902634415631733)
              ·
                refine ⟨2568142076053371976465475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27393515477902634415631733 2568142076053371976465475)
                ·
                  refine ⟨3852213114080057964698213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568142076053371976465475 3852213114080057964698213)
                  ·
                    refine ⟨722289958890010868380915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3852213114080057964698213 722289958890010868380915)
                    ·
                      rfl

theorem cell23_4219964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_4219964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219964 prefixEnd_4219964 := by exact prefixLift 4219964
  have htrace : WordTrace (prefixWord ++ tailWord_4219964) baseStart_4219964 baseEnd_4219964 := by
    simpa [prefixWord, tailWord_4219964, baseEnd_4219964] using wordTrace_append hprefix tailTrace_4219964
  have hstable : (prefixWord ++ tailWord_4219964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219964).length < 2 ^ (prefixWord ++ tailWord_4219964).sum := by decide
  have hdescent : baseEnd_4219964 < baseStart_4219964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219981 : List Nat := [1, 6, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_4219981 : Nat := 118140960795 + 4219981 * 2 ^ 59
def prefixEnd_4219981 : Nat := 4983230072969 + 3 ^ 40 * 4219981 * 2
def baseEnd_4219981 : Nat := 722292868613719679543389

theorem tailTrace_4219981 : CollatzResearch.WordTrace tailWord_4219981 prefixEnd_4219981 722292868613719679543389 := by
  unfold tailWord_4219981
  simp only [CollatzResearch.WordTrace]
  refine ⟨153915351724737027220827797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102610234483158018147218531 153915351724737027220827797)
  ·
    refine ⟨7214782112097048150976303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 153915351724737027220827797 7214782112097048150976303)
    ·
      refine ⟨10822173168145572226464455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7214782112097048150976303 10822173168145572226464455)
      ·
        refine ⟨16233259752218358339696683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10822173168145572226464455 16233259752218358339696683)
        ·
          refine ⟨24349889628327537509545025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16233259752218358339696683 24349889628327537509545025)
          ·
            refine ⟨18262417221245653132158769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24349889628327537509545025 18262417221245653132158769)
            ·
              refine ⟨13696812915934239849119077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18262417221245653132158769 13696812915934239849119077)
              ·
                refine ⟨2568152421737669971709827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13696812915934239849119077 2568152421737669971709827)
                ·
                  refine ⟨3852228632606504957564741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568152421737669971709827 3852228632606504957564741)
                  ·
                    refine ⟨722292868613719679543389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3852228632606504957564741 722292868613719679543389)
                    ·
                      rfl

theorem cell23_4219981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_4219981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219981 prefixEnd_4219981 := by exact prefixLift 4219981
  have htrace : WordTrace (prefixWord ++ tailWord_4219981) baseStart_4219981 baseEnd_4219981 := by
    simpa [prefixWord, tailWord_4219981, baseEnd_4219981] using wordTrace_append hprefix tailTrace_4219981
  have hstable : (prefixWord ++ tailWord_4219981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219981).length < 2 ^ (prefixWord ++ tailWord_4219981).sum := by decide
  have hdescent : baseEnd_4219981 < baseStart_4219981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4219987 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 3, 1, 3]
def baseStart_4219987 : Nat := 118140960795 + 4219987 * 2 ^ 59
def prefixEnd_4219987 : Nat := 4983230072969 + 3 ^ 40 * 4219987 * 2
def baseEnd_4219987 : Nat := 2166881686725086015155139

theorem tailTrace_4219987 : CollatzResearch.WordTrace tailWord_4219987 prefixEnd_4219987 2166881686725086015155139 := by
  unfold tailWord_4219987
  simp only [CollatzResearch.WordTrace]
  refine ⟨153915570562715290245546215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102610380375143526830364143 153915570562715290245546215)
  ·
    refine ⟨230873355844072935368319323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153915570562715290245546215 230873355844072935368319323)
    ·
      refine ⟨346310033766109403052478985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230873355844072935368319323 346310033766109403052478985)
      ·
        refine ⟨259732525324582052289359239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346310033766109403052478985 259732525324582052289359239)
        ·
          refine ⟨389598787986873078434038859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259732525324582052289359239 389598787986873078434038859)
          ·
            refine ⟨584398181980309617651058289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389598787986873078434038859 584398181980309617651058289)
            ·
              refine ⟨438298636485232213238293717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584398181980309617651058289 438298636485232213238293717)
              ·
                refine ⟨10272624292622629997772509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 438298636485232213238293717 10272624292622629997772509)
                ·
                  refine ⟨3852234109733486249164691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10272624292622629997772509 3852234109733486249164691)
                  ·
                    refine ⟨5778351164600229373747037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3852234109733486249164691 5778351164600229373747037)
                    ·
                      refine ⟨2166881686725086015155139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5778351164600229373747037 2166881686725086015155139)
                      ·
                        rfl

theorem cell23_4219987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 1, 3].length) (baseStart_4219987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4219987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4219987 prefixEnd_4219987 := by exact prefixLift 4219987
  have htrace : WordTrace (prefixWord ++ tailWord_4219987) baseStart_4219987 baseEnd_4219987 := by
    simpa [prefixWord, tailWord_4219987, baseEnd_4219987] using wordTrace_append hprefix tailTrace_4219987
  have hstable : (prefixWord ++ tailWord_4219987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4219987).length < 2 ^ (prefixWord ++ tailWord_4219987).sum := by decide
  have hdescent : baseEnd_4219987 < baseStart_4219987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4219987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220007 : List Nat := [1, 1, 5, 1, 1, 3, 1, 4, 1, 5]
def baseStart_4220007 : Nat := 118140960795 + 4220007 * 2 ^ 59
def prefixEnd_4220007 : Nat := 4983230072969 + 3 ^ 40 * 4220007 * 2
def baseEnd_4220007 : Nat := 722297318779391978968349

theorem tailTrace_4220007 : CollatzResearch.WordTrace tailWord_4220007 prefixEnd_4220007 722297318779391978968349 := by
  unfold tailWord_4220007
  simp only [CollatzResearch.WordTrace]
  refine ⟨153916300022642833661274275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102610866681761889107516183 153916300022642833661274275)
  ·
    refine ⟨230874450033964250491911413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153916300022642833661274275 230874450033964250491911413)
    ·
      refine ⟨21644479690684148483616695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 230874450033964250491911413 21644479690684148483616695)
      ·
        refine ⟨32466719536026222725425043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21644479690684148483616695 32466719536026222725425043)
        ·
          refine ⟨48700079304039334088137565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32466719536026222725425043 48700079304039334088137565)
          ·
            refine ⟨18262529739014750283051587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48700079304039334088137565 18262529739014750283051587)
            ·
              refine ⟨27393794608522125424577381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18262529739014750283051587 27393794608522125424577381)
              ·
                refine ⟨5136336489097898517108259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27393794608522125424577381 5136336489097898517108259)
                ·
                  refine ⟨7704504733646847775662389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5136336489097898517108259 7704504733646847775662389)
                  ·
                    refine ⟨722297318779391978968349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7704504733646847775662389 722297318779391978968349)
                    ·
                      rfl

theorem cell23_4220007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_4220007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220007 prefixEnd_4220007 := by exact prefixLift 4220007
  have htrace : WordTrace (prefixWord ++ tailWord_4220007) baseStart_4220007 baseEnd_4220007 := by
    simpa [prefixWord, tailWord_4220007, baseEnd_4220007] using wordTrace_append hprefix tailTrace_4220007
  have hstable : (prefixWord ++ tailWord_4220007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220007).length < 2 ^ (prefixWord ++ tailWord_4220007).sum := by decide
  have hdescent : baseEnd_4220007 < baseStart_4220007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220014 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_4220014 : Nat := 118140960795 + 4220014 * 2 ^ 59
def prefixEnd_4220014 : Nat := 4983230072969 + 3 ^ 40 * 4220014 * 2
def baseEnd_4220014 : Nat := 2166895550702757409517515

theorem tailTrace_4220014 : CollatzResearch.WordTrace tailWord_4220014 prefixEnd_4220014 2166895550702757409517515 := by
  unfold tailWord_4220014
  simp only [CollatzResearch.WordTrace]
  refine ⟨19239569416702184232097387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102611036889078315904519397 19239569416702184232097387)
  ·
    refine ⟨28859354125053276348146081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19239569416702184232097387 28859354125053276348146081)
    ·
      refine ⟨21644515593789957261109561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28859354125053276348146081 21644515593789957261109561)
      ·
        refine ⟨16233386695342467945832171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21644515593789957261109561 16233386695342467945832171)
        ·
          refine ⟨24350080043013701918748257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16233386695342467945832171 24350080043013701918748257)
          ·
            refine ⟨18262560032260276439061193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24350080043013701918748257 18262560032260276439061193)
            ·
              refine ⟨13696920024195207329295895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18262560032260276439061193 13696920024195207329295895)
              ·
                refine ⟨20545380036292810993943843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13696920024195207329295895 20545380036292810993943843)
                ·
                  refine ⟨30818070054439216490915765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20545380036292810993943843 30818070054439216490915765)
                  ·
                    refine ⟨2889194067603676546023353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30818070054439216490915765 2889194067603676546023353)
                    ·
                      refine ⟨2166895550702757409517515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2889194067603676546023353 2166895550702757409517515)
                      ·
                        rfl

theorem cell23_4220014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_4220014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220014 prefixEnd_4220014 := by exact prefixLift 4220014
  have htrace : WordTrace (prefixWord ++ tailWord_4220014) baseStart_4220014 baseEnd_4220014 := by
    simpa [prefixWord, tailWord_4220014, baseEnd_4220014] using wordTrace_append hprefix tailTrace_4220014
  have hstable : (prefixWord ++ tailWord_4220014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220014).length < 2 ^ (prefixWord ++ tailWord_4220014).sum := by decide
  have hdescent : baseEnd_4220014 < baseStart_4220014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220074 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4220074 : Nat := 118140960795 + 4220074 * 2 ^ 59
def prefixEnd_4220074 : Nat := 4983230072969 + 3 ^ 40 * 4220074 * 2
def baseEnd_4220074 : Nat := 2166926359542027174767239

theorem tailTrace_4220074 : CollatzResearch.WordTrace tailWord_4220074 prefixEnd_4220074 2166926359542027174767239 := by
  unfold tailWord_4220074
  simp only [CollatzResearch.WordTrace]
  refine ⟨38479685928350026025990819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102612495808933402735975517 38479685928350026025990819)
  ·
    refine ⟨57719528892525039038986229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38479685928350026025990819 57719528892525039038986229)
    ·
      refine ⟨5411205833674222409904959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57719528892525039038986229 5411205833674222409904959)
      ·
        refine ⟨8116808750511333614857439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5411205833674222409904959 8116808750511333614857439)
        ·
          refine ⟨12175213125767000422286159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8116808750511333614857439 12175213125767000422286159)
          ·
            refine ⟨18262819688650500633429239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12175213125767000422286159 18262819688650500633429239)
            ·
              refine ⟨27394229532975750950143859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18262819688650500633429239 27394229532975750950143859)
              ·
                refine ⟨41091344299463626425215789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27394229532975750950143859 41091344299463626425215789)
                ·
                  refine ⟨15409254112298859909455921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41091344299463626425215789 15409254112298859909455921)
                  ·
                    refine ⟨11556940584224144932091941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15409254112298859909455921 11556940584224144932091941)
                    ·
                      refine ⟨2166926359542027174767239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11556940584224144932091941 2166926359542027174767239)
                      ·
                        rfl

theorem cell23_4220074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4220074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220074 prefixEnd_4220074 := by exact prefixLift 4220074
  have htrace : WordTrace (prefixWord ++ tailWord_4220074) baseStart_4220074 baseEnd_4220074 := by
    simpa [prefixWord, tailWord_4220074, baseEnd_4220074] using wordTrace_append hprefix tailTrace_4220074
  have hstable : (prefixWord ++ tailWord_4220074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220074).length < 2 ^ (prefixWord ++ tailWord_4220074).sum := by decide
  have hdescent : baseEnd_4220074 < baseStart_4220074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220104 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 3, 3, 2]
def baseStart_4220104 : Nat := 118140960795 + 4220104 * 2 ^ 59
def prefixEnd_4220104 : Nat := 4983230072969 + 3 ^ 40 * 4220104 * 2
def baseEnd_4220104 : Nat := 2166941763961662057392101

theorem tailTrace_4220104 : CollatzResearch.WordTrace tailWord_4220104 prefixEnd_4220104 2166941763961662057392101 := by
  unfold tailWord_4220104
  simp only [CollatzResearch.WordTrace]
  refine ⟨76959918951645709613777683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102613225268860946151703577 76959918951645709613777683)
  ·
    refine ⟨115439878427468564420666525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76959918951645709613777683 115439878427468564420666525)
    ·
      refine ⟨43289954410300711657749947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115439878427468564420666525 43289954410300711657749947)
      ·
        refine ⟨64934931615451067486624921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43289954410300711657749947 64934931615451067486624921)
        ·
          refine ⟨48701198711588300614968691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64934931615451067486624921 48701198711588300614968691)
          ·
            refine ⟨73051798067382450922453037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48701198711588300614968691 73051798067382450922453037)
            ·
              refine ⟨27394424275268419095919889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73051798067382450922453037 27394424275268419095919889)
              ·
                refine ⟨20545818206451314321939917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27394424275268419095919889 20545818206451314321939917)
                ·
                  refine ⟨7704681827419242870727469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20545818206451314321939917 7704681827419242870727469)
                  ·
                    refine ⟨2889255685282216076522801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7704681827419242870727469 2889255685282216076522801)
                    ·
                      refine ⟨2166941763961662057392101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2889255685282216076522801 2166941763961662057392101)
                      ·
                        rfl

theorem cell23_4220104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_4220104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220104 prefixEnd_4220104 := by exact prefixLift 4220104
  have htrace : WordTrace (prefixWord ++ tailWord_4220104) baseStart_4220104 baseEnd_4220104 := by
    simpa [prefixWord, tailWord_4220104, baseEnd_4220104] using wordTrace_append hprefix tailTrace_4220104
  have hstable : (prefixWord ++ tailWord_4220104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220104).length < 2 ^ (prefixWord ++ tailWord_4220104).sum := by decide
  have hdescent : baseEnd_4220104 < baseStart_4220104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220138 : List Nat := [3, 1, 3, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_4220138 : Nat := 118140960795 + 4220138 * 2 ^ 59
def prefixEnd_4220138 : Nat := 4983230072969 + 3 ^ 40 * 4220138 * 2
def baseEnd_4220138 : Nat := 2166959222303914924366945

theorem tailTrace_4220138 : CollatzResearch.WordTrace tailWord_4220138 prefixEnd_4220138 2166959222303914924366945 := by
  unfold tailWord_4220138
  simp only [CollatzResearch.WordTrace]
  refine ⟨38480269496292060758573267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102614051990112162022862045 38480269496292060758573267)
  ·
    refine ⟨57720404244438091137859901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38480269496292060758573267 57720404244438091137859901)
    ·
      refine ⟨21645151591664284176697463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57720404244438091137859901 21645151591664284176697463)
      ·
        refine ⟨32467727387496426265046195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21645151591664284176697463 32467727387496426265046195)
        ·
          refine ⟨48701591081244639397569293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32467727387496426265046195 48701591081244639397569293)
          ·
            refine ⟨18263096655466739774088485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48701591081244639397569293 18263096655466739774088485)
            ·
              refine ⟨3424330622900013707641591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18263096655466739774088485 3424330622900013707641591)
              ·
                refine ⟨5136495934350020561462387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3424330622900013707641591 5136495934350020561462387)
                ·
                  refine ⟨7704743901525030842193581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5136495934350020561462387 7704743901525030842193581)
                  ·
                    refine ⟨2889278963071886565822593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7704743901525030842193581 2889278963071886565822593)
                    ·
                      refine ⟨2166959222303914924366945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2889278963071886565822593 2166959222303914924366945)
                      ·
                        rfl

theorem cell23_4220138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_4220138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220138 prefixEnd_4220138 := by exact prefixLift 4220138
  have htrace : WordTrace (prefixWord ++ tailWord_4220138) baseStart_4220138 baseEnd_4220138 := by
    simpa [prefixWord, tailWord_4220138, baseEnd_4220138] using wordTrace_append hprefix tailTrace_4220138
  have hstable : (prefixWord ++ tailWord_4220138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220138).length < 2 ^ (prefixWord ++ tailWord_4220138).sum := by decide
  have hdescent : baseEnd_4220138 < baseStart_4220138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220147 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 4]
def baseStart_4220147 : Nat := 118140960795 + 4220147 * 2 ^ 59
def prefixEnd_4220147 : Nat := 4983230072969 + 3 ^ 40 * 4220147 * 2
def baseEnd_4220147 : Nat := 2166963843629805389154403

theorem tailTrace_4220147 : CollatzResearch.WordTrace tailWord_4220147 prefixEnd_4220147 2166963843629805389154403 := by
  unfold tailWord_4220147
  simp only [CollatzResearch.WordTrace]
  refine ⟨153921406242135637571370695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102614270828090425047580463 153921406242135637571370695)
  ·
    refine ⟨230882109363203456357056043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153921406242135637571370695 230882109363203456357056043)
    ·
      refine ⟨346323164044805184535584065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230882109363203456357056043 346323164044805184535584065)
      ·
        refine ⟨259742373033603888401688049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346323164044805184535584065 259742373033603888401688049)
        ·
          refine ⟨194806779775202916301266037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259742373033603888401688049 194806779775202916301266037)
          ·
            refine ⟨18263135603925273403243691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 194806779775202916301266037 18263135603925273403243691)
            ·
              refine ⟨27394703405887910104865537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18263135603925273403243691 27394703405887910104865537)
              ·
                refine ⟨20546027554415932578649153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27394703405887910104865537 20546027554415932578649153)
                ·
                  refine ⟨15409520665811949433986865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20546027554415932578649153 15409520665811949433986865)
                  ·
                    refine ⟨11557140499358962075490149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15409520665811949433986865 11557140499358962075490149)
                    ·
                      refine ⟨2166963843629805389154403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11557140499358962075490149 2166963843629805389154403)
                      ·
                        rfl

theorem cell23_4220147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_4220147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220147 prefixEnd_4220147 := by exact prefixLift 4220147
  have htrace : WordTrace (prefixWord ++ tailWord_4220147) baseStart_4220147 baseEnd_4220147 := by
    simpa [prefixWord, tailWord_4220147, baseEnd_4220147] using wordTrace_append hprefix tailTrace_4220147
  have hstable : (prefixWord ++ tailWord_4220147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220147).length < 2 ^ (prefixWord ++ tailWord_4220147).sum := by decide
  have hdescent : baseEnd_4220147 < baseStart_4220147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220164 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_4220164 : Nat := 118140960795 + 4220164 * 2 ^ 59
def prefixEnd_4220164 : Nat := 4983230072969 + 3 ^ 40 * 4220164 * 2
def baseEnd_4220164 : Nat := 2166972572800931822641825

theorem tailTrace_4220164 : CollatzResearch.WordTrace tailWord_4220164 prefixEnd_4220164 2166972572800931822641825 := by
  unfold tailWord_4220164
  simp only [CollatzResearch.WordTrace]
  refine ⟨76961013141537024737369773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102614684188716032983159697 76961013141537024737369773)
  ·
    refine ⟨28860379928076384276513665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76961013141537024737369773 28860379928076384276513665)
    ·
      refine ⟨21645284946057288207385249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28860379928076384276513665 21645284946057288207385249)
      ·
        refine ⟨16233963709542966155538937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21645284946057288207385249 16233963709542966155538937)
        ·
          refine ⟨12175472782157224616654203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16233963709542966155538937 12175472782157224616654203)
          ·
            refine ⟨18263209173235836924981305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12175472782157224616654203 18263209173235836924981305)
            ·
              refine ⟨13697406879926877693735979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18263209173235836924981305 13697406879926877693735979)
              ·
                refine ⟨20546110319890316540603969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13697406879926877693735979 20546110319890316540603969)
                ·
                  refine ⟨15409582739917737405452977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20546110319890316540603969 15409582739917737405452977)
                  ·
                    refine ⟨11557187054938303054089733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15409582739917737405452977 11557187054938303054089733)
                    ·
                      refine ⟨2166972572800931822641825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11557187054938303054089733 2166972572800931822641825)
                      ·
                        rfl

theorem cell23_4220164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_4220164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220164 prefixEnd_4220164 := by exact prefixLift 4220164
  have htrace : WordTrace (prefixWord ++ tailWord_4220164) baseStart_4220164 baseEnd_4220164 := by
    simpa [prefixWord, tailWord_4220164, baseEnd_4220164] using wordTrace_append hprefix tailTrace_4220164
  have hstable : (prefixWord ++ tailWord_4220164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220164).length < 2 ^ (prefixWord ++ tailWord_4220164).sum := by decide
  have hdescent : baseEnd_4220164 < baseStart_4220164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220168 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 1, 4, 2]
def baseStart_4220168 : Nat := 118140960795 + 4220168 * 2 ^ 59
def prefixEnd_4220168 : Nat := 4983230072969 + 3 ^ 40 * 4220168 * 2
def baseEnd_4220168 : Nat := 2166974626723549806991807

theorem tailTrace_4220168 : CollatzResearch.WordTrace tailWord_4220168 prefixEnd_4220168 2166974626723549806991807 := by
  unfold tailWord_4220168
  simp only [CollatzResearch.WordTrace]
  refine ⟨76961086087529779078942579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102614781450039705438590105 76961086087529779078942579)
  ·
    refine ⟨115441629131294668618413869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76961086087529779078942579 115441629131294668618413869)
    ·
      refine ⟨43290610924235500731905201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115441629131294668618413869 43290610924235500731905201)
      ·
        refine ⟨32467958193176625548928901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43290610924235500731905201 32467958193176625548928901)
        ·
          refine ⟨6087742161220617290424169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32467958193176625548928901 6087742161220617290424169)
          ·
            refine ⟨4565806620915462967818127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6087742161220617290424169 4565806620915462967818127)
            ·
              refine ⟨6848709931373194451727191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4565806620915462967818127 6848709931373194451727191)
              ·
                refine ⟨10273064897059791677590787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6848709931373194451727191 10273064897059791677590787)
                ·
                  refine ⟨15409597345589687516386181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10273064897059791677590787 15409597345589687516386181)
                  ·
                    refine ⟨2889299502298066409322409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15409597345589687516386181 2889299502298066409322409)
                    ·
                      refine ⟨2166974626723549806991807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2889299502298066409322409 2166974626723549806991807)
                      ·
                        rfl

theorem cell23_4220168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_4220168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220168 prefixEnd_4220168 := by exact prefixLift 4220168
  have htrace : WordTrace (prefixWord ++ tailWord_4220168) baseStart_4220168 baseEnd_4220168 := by
    simpa [prefixWord, tailWord_4220168, baseEnd_4220168] using wordTrace_append hprefix tailTrace_4220168
  have hstable : (prefixWord ++ tailWord_4220168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220168).length < 2 ^ (prefixWord ++ tailWord_4220168).sum := by decide
  have hdescent : baseEnd_4220168 < baseStart_4220168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220187 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 2, 5]
def baseStart_4220187 : Nat := 118140960795 + 4220187 * 2 ^ 59
def prefixEnd_4220187 : Nat := 4983230072969 + 3 ^ 40 * 4220187 * 2
def baseEnd_4220187 : Nat := 722328127618661744218073

theorem tailTrace_4220187 : CollatzResearch.WordTrace tailWord_4220187 prefixEnd_4220187 722328127618661744218073 := by
  unfold tailWord_4220187
  simp only [CollatzResearch.WordTrace]
  refine ⟨153922865161990724402826815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102615243441327149601884543 153922865161990724402826815)
  ·
    refine ⟨230884297742986086604240223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153922865161990724402826815 230884297742986086604240223)
    ·
      refine ⟨346326446614479129906360335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230884297742986086604240223 346326446614479129906360335)
      ·
        refine ⟨519489669921718694859540503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346326446614479129906360335 519489669921718694859540503)
        ·
          refine ⟨779234504882578042289310755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519489669921718694859540503 779234504882578042289310755)
          ·
            refine ⟨1168851757323867063433966133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779234504882578042289310755 1168851757323867063433966133)
            ·
              refine ⟨109579852249112537196934325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1168851757323867063433966133 109579852249112537196934325)
              ·
                refine ⟨10273111148354300362212593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109579852249112537196934325 10273111148354300362212593)
                ·
                  refine ⟨7704833361265725271659445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10273111148354300362212593 7704833361265725271659445)
                  ·
                    refine ⟨722328127618661744218073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7704833361265725271659445 722328127618661744218073)
                    ·
                      rfl

theorem cell23_4220187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 5].length) (baseStart_4220187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220187 prefixEnd_4220187 := by exact prefixLift 4220187
  have htrace : WordTrace (prefixWord ++ tailWord_4220187) baseStart_4220187 baseEnd_4220187 := by
    simpa [prefixWord, tailWord_4220187, baseEnd_4220187] using wordTrace_append hprefix tailTrace_4220187
  have hstable : (prefixWord ++ tailWord_4220187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220187).length < 2 ^ (prefixWord ++ tailWord_4220187).sum := by decide
  have hdescent : baseEnd_4220187 < baseStart_4220187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220224 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 1, 6, 2]
def baseStart_4220224 : Nat := 118140960795 + 4220224 * 2 ^ 59
def prefixEnd_4220224 : Nat := 4983230072969 + 3 ^ 40 * 4220224 * 2
def baseEnd_4220224 : Nat := 2167003381640201587891549

theorem tailTrace_4220224 : CollatzResearch.WordTrace tailWord_4220224 prefixEnd_4220224 2167003381640201587891549 := by
  unfold tailWord_4220224
  simp only [CollatzResearch.WordTrace]
  refine ⟨76962107331428339860961863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102616143108571119814615817 76962107331428339860961863)
  ·
    refine ⟨115443160997142509791442795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76962107331428339860961863 115443160997142509791442795)
    ·
      refine ⟨173164741495713764687164193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115443160997142509791442795 173164741495713764687164193)
      ·
        refine ⟨129873556121785323515373145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173164741495713764687164193 129873556121785323515373145)
        ·
          refine ⟨97405167091338992636529859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129873556121785323515373145 97405167091338992636529859)
          ·
            refine ⟨146107750637008488954794789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97405167091338992636529859 146107750637008488954794789)
            ·
              refine ⟨27395203244439091679024023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146107750637008488954794789 27395203244439091679024023)
              ·
                refine ⟨41092804866658637518536035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27395203244439091679024023 41092804866658637518536035)
                ·
                  refine ⟨61639207299987956277804053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41092804866658637518536035 61639207299987956277804053)
                  ·
                    refine ⟨2889337842186935450522065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61639207299987956277804053 2889337842186935450522065)
                    ·
                      refine ⟨2167003381640201587891549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2889337842186935450522065 2167003381640201587891549)
                      ·
                        rfl

theorem cell23_4220224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 6, 2].length) (baseStart_4220224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220224 prefixEnd_4220224 := by exact prefixLift 4220224
  have htrace : WordTrace (prefixWord ++ tailWord_4220224) baseStart_4220224 baseEnd_4220224 := by
    simpa [prefixWord, tailWord_4220224, baseEnd_4220224] using wordTrace_append hprefix tailTrace_4220224
  have hstable : (prefixWord ++ tailWord_4220224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220224).length < 2 ^ (prefixWord ++ tailWord_4220224).sum := by decide
  have hdescent : baseEnd_4220224 < baseStart_4220224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220234 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 3, 4]
def baseStart_4220234 : Nat := 118140960795 + 4220234 * 2 ^ 59
def prefixEnd_4220234 : Nat := 4983230072969 + 3 ^ 40 * 4220234 * 2
def baseEnd_4220234 : Nat := 722336172148915516255501

theorem tailTrace_4220234 : CollatzResearch.WordTrace tailWord_4220234 prefixEnd_4220234 722336172148915516255501 := by
  unfold tailWord_4220234
  simp only [CollatzResearch.WordTrace]
  refine ⟨38481144848205112857446939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102616386261880300953191837 38481144848205112857446939)
  ·
    refine ⟨57721717272307669286170409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38481144848205112857446939 57721717272307669286170409)
    ·
      refine ⟨43291287954230751964627807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57721717272307669286170409 43291287954230751964627807)
      ·
        refine ⟨64936931931346127946941711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43291287954230751964627807 64936931931346127946941711)
        ·
          refine ⟨97405397897019191920412567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64936931931346127946941711 97405397897019191920412567)
          ·
            refine ⟨146108096845528787880618851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97405397897019191920412567 146108096845528787880618851)
            ·
              refine ⟨219162145268293181820928277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146108096845528787880618851 219162145268293181820928277)
              ·
                refine ⟨10273225559451242897856013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 219162145268293181820928277 10273225559451242897856013)
                ·
                  refine ⟨3852459584794216086696005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10273225559451242897856013 3852459584794216086696005)
                  ·
                    refine ⟨722336172148915516255501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3852459584794216086696005 722336172148915516255501)
                    ·
                      rfl

theorem cell23_4220234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_4220234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220234 prefixEnd_4220234 := by exact prefixLift 4220234
  have htrace : WordTrace (prefixWord ++ tailWord_4220234) baseStart_4220234 baseEnd_4220234 := by
    simpa [prefixWord, tailWord_4220234, baseEnd_4220234] using wordTrace_append hprefix tailTrace_4220234
  have hstable : (prefixWord ++ tailWord_4220234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220234).length < 2 ^ (prefixWord ++ tailWord_4220234).sum := by decide
  have hdescent : baseEnd_4220234 < baseStart_4220234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220268 : List Nat := [2, 2, 1, 1, 5, 2, 1, 4, 1, 4]
def baseStart_4220268 : Nat := 118140960795 + 4220268 * 2 ^ 59
def prefixEnd_4220268 : Nat := 4983230072969 + 3 ^ 40 * 4220268 * 2
def baseEnd_4220268 : Nat := 722341991596333138580449

theorem tailTrace_4220268 : CollatzResearch.WordTrace tailWord_4220268 prefixEnd_4220268 722341991596333138580449 := by
  unfold tailWord_4220268
  simp only [CollatzResearch.WordTrace]
  refine ⟨76962909737348637618262729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102617212983131516824350305 76962909737348637618262729)
  ·
    refine ⟨57722182303011478213697047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76962909737348637618262729 57722182303011478213697047)
    ·
      refine ⟨86583273454517217320545571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57722182303011478213697047 86583273454517217320545571)
      ·
        refine ⟨129874910181775825980818357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86583273454517217320545571 129874910181775825980818357)
        ·
          refine ⟨12175772829541483685701721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129874910181775825980818357 12175772829541483685701721)
          ·
            refine ⟨9131829622156112764276291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12175772829541483685701721 9131829622156112764276291)
            ·
              refine ⟨13697744433234169146414437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9131829622156112764276291 13697744433234169146414437)
              ·
                refine ⟨2568327081231406714952707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13697744433234169146414437 2568327081231406714952707)
                ·
                  refine ⟨3852490621847110072429061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568327081231406714952707 3852490621847110072429061)
                  ·
                    refine ⟨722341991596333138580449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3852490621847110072429061 722341991596333138580449)
                    ·
                      rfl

theorem cell23_4220268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_4220268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220268 prefixEnd_4220268 := by exact prefixLift 4220268
  have htrace : WordTrace (prefixWord ++ tailWord_4220268) baseStart_4220268 baseEnd_4220268 := by
    simpa [prefixWord, tailWord_4220268, baseEnd_4220268] using wordTrace_append hprefix tailTrace_4220268
  have hstable : (prefixWord ++ tailWord_4220268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220268).length < 2 ^ (prefixWord ++ tailWord_4220268).sum := by decide
  have hdescent : baseEnd_4220268 < baseStart_4220268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220291 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 5, 1, 3]
def baseStart_4220291 : Nat := 118140960795 + 4220291 * 2 ^ 59
def prefixEnd_4220291 : Nat := 4983230072969 + 3 ^ 40 * 4220291 * 2
def baseEnd_4220291 : Nat := 2167037784844052825753741

theorem tailTrace_4220291 : CollatzResearch.WordTrace tailWord_4220291 prefixEnd_4220291 2167037784844052825753741 := by
  unfold tailWord_4220291
  simp only [CollatzResearch.WordTrace]
  refine ⟨153926658353613950164612727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102617772235742633443075151 153926658353613950164612727)
  ·
    refine ⟨230889987530420925246919091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153926658353613950164612727 230889987530420925246919091)
    ·
      refine ⟨346334981295631387870378637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230889987530420925246919091 346334981295631387870378637)
      ·
        refine ⟨129875617985861770451391989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346334981295631387870378637 129875617985861770451391989)
        ·
          refine ⟨12175839186174540979817999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129875617985861770451391989 12175839186174540979817999)
          ·
            refine ⟨18263758779261811469726999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12175839186174540979817999 18263758779261811469726999)
            ·
              refine ⟨27395638168892717204590499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18263758779261811469726999 27395638168892717204590499)
              ·
                refine ⟨41093457253339075806885749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27395638168892717204590499 41093457253339075806885749)
                ·
                  refine ⟨3852511617500538356895539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41093457253339075806885749 3852511617500538356895539)
                  ·
                    refine ⟨5778767426250807535343309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3852511617500538356895539 5778767426250807535343309)
                    ·
                      refine ⟨2167037784844052825753741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5778767426250807535343309 2167037784844052825753741)
                      ·
                        rfl

theorem cell23_4220291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_4220291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220291 prefixEnd_4220291 := by exact prefixLift 4220291
  have htrace : WordTrace (prefixWord ++ tailWord_4220291) baseStart_4220291 baseEnd_4220291 := by
    simpa [prefixWord, tailWord_4220291, baseEnd_4220291] using wordTrace_append hprefix tailTrace_4220291
  have hstable : (prefixWord ++ tailWord_4220291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220291).length < 2 ^ (prefixWord ++ tailWord_4220291).sum := by decide
  have hdescent : baseEnd_4220291 < baseStart_4220291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220341 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 1, 6]
def baseStart_4220341 : Nat := 118140960795 + 4220341 * 2 ^ 59
def prefixEnd_4220341 : Nat := 4983230072969 + 3 ^ 40 * 4220341 * 2
def baseEnd_4220341 : Nat := 722354486292259210042837

theorem tailTrace_4220341 : CollatzResearch.WordTrace tailWord_4220341 prefixEnd_4220341 722354486292259210042837 := by
  unfold tailWord_4220341
  simp only [CollatzResearch.WordTrace]
  refine ⟨153928482003432808703932877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102618988002288539135955251 153928482003432808703932877)
  ·
    refine ⟨57723180751287303263974829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153928482003432808703932877 57723180751287303263974829)
    ·
      refine ⟨21646192781732738723990561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57723180751287303263974829 21646192781732738723990561)
      ·
        refine ⟨16234644586299554042992921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21646192781732738723990561 16234644586299554042992921)
        ·
          refine ⟨12175983439724665532244691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16234644586299554042992921 12175983439724665532244691)
          ·
            refine ⟨18263975159586998298367037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12175983439724665532244691 18263975159586998298367037)
            ·
              refine ⟨6848990684845124361887639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18263975159586998298367037 6848990684845124361887639)
              ·
                refine ⟨10273486027267686542831459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6848990684845124361887639 10273486027267686542831459)
                ·
                  refine ⟨15410229040901529814247189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10273486027267686542831459 15410229040901529814247189)
                  ·
                    refine ⟨722354486292259210042837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15410229040901529814247189 722354486292259210042837)
                    ·
                      rfl

theorem cell23_4220341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_4220341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220341 prefixEnd_4220341 := by exact prefixLift 4220341
  have htrace : WordTrace (prefixWord ++ tailWord_4220341) baseStart_4220341 baseEnd_4220341 := by
    simpa [prefixWord, tailWord_4220341, baseEnd_4220341] using wordTrace_append hprefix tailTrace_4220341
  have hstable : (prefixWord ++ tailWord_4220341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220341).length < 2 ^ (prefixWord ++ tailWord_4220341).sum := by decide
  have hdescent : baseEnd_4220341 < baseStart_4220341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220408 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 3, 3, 2]
def baseStart_4220408 : Nat := 118140960795 + 4220408 * 2 ^ 59
def prefixEnd_4220408 : Nat := 4983230072969 + 3 ^ 40 * 4220408 * 2
def baseEnd_4220408 : Nat := 2167097862080628867990703

theorem tailTrace_4220408 : CollatzResearch.WordTrace tailWord_4220408 prefixEnd_4220408 2167097862080628867990703 := by
  unfold tailWord_4220408
  simp only [CollatzResearch.WordTrace]
  refine ⟨76965462847095039573310939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102620617129460052764414585 76965462847095039573310939)
  ·
    refine ⟨115448194270642559359966409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76965462847095039573310939 115448194270642559359966409)
    ·
      refine ⟨86586145702981919519974807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115448194270642559359966409 86586145702981919519974807)
      ·
        refine ⟨129879218554472879279962211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86586145702981919519974807 129879218554472879279962211)
        ·
          refine ⟨194818827831709318919943317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129879218554472879279962211 194818827831709318919943317)
          ·
            refine ⟨9132132554611374324372343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 194818827831709318919943317 9132132554611374324372343)
            ·
              refine ⟨13698198831917061486558515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9132132554611374324372343 13698198831917061486558515)
              ·
                refine ⟨20547298247875592229837773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13698198831917061486558515 20547298247875592229837773)
                ·
                  refine ⟨7705236842953347086189165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20547298247875592229837773 7705236842953347086189165)
                  ·
                    refine ⟨2889463816107505157320937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7705236842953347086189165 2889463816107505157320937)
                    ·
                      refine ⟨2167097862080628867990703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2889463816107505157320937 2167097862080628867990703)
                      ·
                        rfl

theorem cell23_4220408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 3, 3, 2].length) (baseStart_4220408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220408 prefixEnd_4220408 := by exact prefixLift 4220408
  have htrace : WordTrace (prefixWord ++ tailWord_4220408) baseStart_4220408 baseEnd_4220408 := by
    simpa [prefixWord, tailWord_4220408, baseEnd_4220408] using wordTrace_append hprefix tailTrace_4220408
  have hstable : (prefixWord ++ tailWord_4220408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220408).length < 2 ^ (prefixWord ++ tailWord_4220408).sum := by decide
  have hdescent : baseEnd_4220408 < baseStart_4220408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220425 : List Nat := [1, 2, 1, 1, 3, 1, 7, 1, 1, 3, 2]
def baseStart_4220425 : Nat := 118140960795 + 4220425 * 2 ^ 59
def prefixEnd_4220425 : Nat := 4983230072969 + 3 ^ 40 * 4220425 * 2
def baseEnd_4220425 : Nat := 2167106591251755301478125

theorem tailTrace_4220425 : CollatzResearch.WordTrace tailWord_4220425 prefixEnd_4220425 2167106591251755301478125 := by
  unfold tailWord_4220425
  simp only [CollatzResearch.WordTrace]
  refine ⟨153931545735128491049990729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102621030490085660699993819 153931545735128491049990729)
  ·
    refine ⟨115448659301346368287493047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153931545735128491049990729 115448659301346368287493047)
    ·
      refine ⟨173172988952019552431239571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115448659301346368287493047 173172988952019552431239571)
      ·
        refine ⟨259759483428029328646859357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173172988952019552431239571 259759483428029328646859357)
        ·
          refine ⟨97409806285510998242572259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259759483428029328646859357 97409806285510998242572259)
          ·
            refine ⟨146114709428266497363858389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97409806285510998242572259 146114709428266497363858389)
            ·
              refine ⟨3424563502224996031965431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 146114709428266497363858389 3424563502224996031965431)
              ·
                refine ⟨5136845253337494047948147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3424563502224996031965431 5136845253337494047948147)
                ·
                  refine ⟨7705267880006241071922221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5136845253337494047948147 7705267880006241071922221)
                  ·
                    refine ⟨2889475455002340401970833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7705267880006241071922221 2889475455002340401970833)
                    ·
                      refine ⟨2167106591251755301478125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2889475455002340401970833 2167106591251755301478125)
                      ·
                        rfl

theorem cell23_4220425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 1, 3, 2].length) (baseStart_4220425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220425 prefixEnd_4220425 := by exact prefixLift 4220425
  have htrace : WordTrace (prefixWord ++ tailWord_4220425) baseStart_4220425 baseEnd_4220425 := by
    simpa [prefixWord, tailWord_4220425, baseEnd_4220425] using wordTrace_append hprefix tailTrace_4220425
  have hstable : (prefixWord ++ tailWord_4220425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220425).length < 2 ^ (prefixWord ++ tailWord_4220425).sum := by decide
  have hdescent : baseEnd_4220425 < baseStart_4220425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220551 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 8]
def baseStart_4220551 : Nat := 118140960795 + 4220551 * 2 ^ 59
def prefixEnd_4220551 : Nat := 4983230072969 + 3 ^ 40 * 4220551 * 2
def baseEnd_4220551 : Nat := 240796809979357978722505

theorem tailTrace_4220551 : CollatzResearch.WordTrace tailWord_4220551 prefixEnd_4220551 240796809979357978722505 := by
  unfold tailWord_4220551
  simp only [CollatzResearch.WordTrace]
  refine ⟨153936141332672014569077507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102624094221781343046051671 153936141332672014569077507)
  ·
    refine ⟨230904211999008021853616261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153936141332672014569077507 230904211999008021853616261)
    ·
      refine ⟨43294539749814004097553049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230904211999008021853616261 43294539749814004097553049)
      ·
        refine ⟨32470904812360503073164787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43294539749814004097553049 32470904812360503073164787)
        ·
          refine ⟨48706357218540754609747181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32470904812360503073164787 48706357218540754609747181)
          ·
            refine ⟨18264883956952782978655193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48706357218540754609747181 18264883956952782978655193)
            ·
              refine ⟨13698662967714587233991395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18264883956952782978655193 13698662967714587233991395)
              ·
                refine ⟨20547994451571880850987093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13698662967714587233991395 20547994451571880850987093)
                ·
                  refine ⟨240796809979357978722505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20547994451571880850987093 240796809979357978722505)
                  ·
                    rfl

theorem cell23_4220551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 8].length) (baseStart_4220551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220551 prefixEnd_4220551 := by exact prefixLift 4220551
  have htrace : WordTrace (prefixWord ++ tailWord_4220551) baseStart_4220551 baseEnd_4220551 := by
    simpa [prefixWord, tailWord_4220551, baseEnd_4220551] using wordTrace_append hprefix tailTrace_4220551
  have hstable : (prefixWord ++ tailWord_4220551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220551).length < 2 ^ (prefixWord ++ tailWord_4220551).sum := by decide
  have hdescent : baseEnd_4220551 < baseStart_4220551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220561 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 3]
def baseStart_4220561 : Nat := 118140960795 + 4220561 * 2 ^ 59
def prefixEnd_4220561 : Nat := 4983230072969 + 3 ^ 40 * 4220561 * 2
def baseEnd_4220561 : Nat := 2167176424620766769377499

theorem tailTrace_4220561 : CollatzResearch.WordTrace tailWord_4220561 prefixEnd_4220561 2167176424620766769377499 := by
  unfold tailWord_4220561
  simp only [CollatzResearch.WordTrace]
  refine ⟨153936506062635786276941537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102624337375090524184627691 153936506062635786276941537)
  ·
    refine ⟨115452379546976839707706153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153936506062635786276941537 115452379546976839707706153)
    ·
      refine ⟨86589284660232629780779615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115452379546976839707706153 86589284660232629780779615)
      ·
        refine ⟨129883926990348944671169423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86589284660232629780779615 129883926990348944671169423)
        ·
          refine ⟨194825890485523417006754135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129883926990348944671169423 194825890485523417006754135)
          ·
            refine ⟨292238835728285125510131203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194825890485523417006754135 292238835728285125510131203)
            ·
              refine ⟨438358253592427688265196805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292238835728285125510131203 438358253592427688265196805)
              ·
                refine ⟨82192172548580191549724401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 438358253592427688265196805 82192172548580191549724401)
                ·
                  refine ⟨61644129411435143662293301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82192172548580191549724401 61644129411435143662293301)
                  ·
                    refine ⟨5779137132322044718339997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61644129411435143662293301 5779137132322044718339997)
                    ·
                      refine ⟨2167176424620766769377499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5779137132322044718339997 2167176424620766769377499)
                      ·
                        rfl

theorem cell23_4220561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_4220561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220561 prefixEnd_4220561 := by exact prefixLift 4220561
  have htrace : WordTrace (prefixWord ++ tailWord_4220561) baseStart_4220561 baseEnd_4220561 := by
    simpa [prefixWord, tailWord_4220561, baseEnd_4220561] using wordTrace_append hprefix tailTrace_4220561
  have hstable : (prefixWord ++ tailWord_4220561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220561).length < 2 ^ (prefixWord ++ tailWord_4220561).sum := by decide
  have hdescent : baseEnd_4220561 < baseStart_4220561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220568 : List Nat := [2, 1, 2, 4, 1, 3, 1, 3, 6]
def baseStart_4220568 : Nat := 118140960795 + 4220568 * 2 ^ 59
def prefixEnd_4220568 : Nat := 4983230072969 + 3 ^ 40 * 4220568 * 2
def baseEnd_4220568 : Nat := 240797779887260915776663

theorem tailTrace_4220568 : CollatzResearch.WordTrace tailWord_4220568 prefixEnd_4220568 240797779887260915776663 := by
  unfold tailWord_4220568
  simp only [CollatzResearch.WordTrace]
  refine ⟨76968380686805213236223179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102624507582406950981630905 76968380686805213236223179)
  ·
    refine ⟨115452571030207819854334769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76968380686805213236223179 115452571030207819854334769)
    ·
      refine ⟨86589428272655864890751077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115452571030207819854334769 86589428272655864890751077)
      ·
        refine ⟨16235517801122974667015827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86589428272655864890751077 16235517801122974667015827)
        ·
          refine ⟨24353276701684462000523741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16235517801122974667015827 24353276701684462000523741)
          ·
            refine ⟨9132478763131673250196403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24353276701684462000523741 9132478763131673250196403)
            ·
              refine ⟨13698718144697509875294605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9132478763131673250196403 13698718144697509875294605)
              ·
                refine ⟨5137019304261566203235477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13698718144697509875294605 5137019304261566203235477)
                ·
                  refine ⟨240797779887260915776663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5137019304261566203235477 240797779887260915776663)
                  ·
                    rfl

theorem cell23_4220568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 6].length) (baseStart_4220568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220568 prefixEnd_4220568 := by exact prefixLift 4220568
  have htrace : WordTrace (prefixWord ++ tailWord_4220568) baseStart_4220568 baseEnd_4220568 := by
    simpa [prefixWord, tailWord_4220568, baseEnd_4220568] using wordTrace_append hprefix tailTrace_4220568
  have hstable : (prefixWord ++ tailWord_4220568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220568).length < 2 ^ (prefixWord ++ tailWord_4220568).sum := by decide
  have hdescent : baseEnd_4220568 < baseStart_4220568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220605 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 2, 3, 2]
def baseStart_4220605 : Nat := 118140960795 + 4220605 * 2 ^ 59
def prefixEnd_4220605 : Nat := 4983230072969 + 3 ^ 40 * 4220605 * 2
def baseEnd_4220605 : Nat := 2167199017769564597227297

theorem tailTrace_4220605 : CollatzResearch.WordTrace tailWord_4220605 prefixEnd_4220605 2167199017769564597227297 := by
  unfold tailWord_4220605
  simp only [CollatzResearch.WordTrace]
  refine ⟨153938110874476381791543269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102625407249650921194362179 153938110874476381791543269)
  ·
    refine ⟨28863395788964321585914363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153938110874476381791543269 28863395788964321585914363)
    ·
      refine ⟨43295093683446482378871545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28863395788964321585914363 43295093683446482378871545)
      ·
        refine ⟨32471320262584861784153659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43295093683446482378871545 32471320262584861784153659)
        ·
          refine ⟨48706980393877292676230489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32471320262584861784153659 48706980393877292676230489)
          ·
            refine ⟨36530235295407969507172867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48706980393877292676230489 36530235295407969507172867)
            ·
              refine ⟨54795352943111954260759301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36530235295407969507172867 54795352943111954260759301)
              ·
                refine ⟨10274128676833491423892369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54795352943111954260759301 10274128676833491423892369)
                ·
                  refine ⟨7705596507625118567919277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10274128676833491423892369 7705596507625118567919277)
                  ·
                    refine ⟨2889598690359419462969729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7705596507625118567919277 2889598690359419462969729)
                    ·
                      refine ⟨2167199017769564597227297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2889598690359419462969729 2167199017769564597227297)
                      ·
                        rfl

theorem cell23_4220605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_4220605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220605 prefixEnd_4220605 := by exact prefixLift 4220605
  have htrace : WordTrace (prefixWord ++ tailWord_4220605) baseStart_4220605 baseEnd_4220605 := by
    simpa [prefixWord, tailWord_4220605, baseEnd_4220605] using wordTrace_append hprefix tailTrace_4220605
  have hstable : (prefixWord ++ tailWord_4220605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220605).length < 2 ^ (prefixWord ++ tailWord_4220605).sum := by decide
  have hdescent : baseEnd_4220605 < baseStart_4220605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220655 : List Nat := [1, 1, 2, 1, 5, 1, 3, 3, 1, 2, 3]
def baseStart_4220655 : Nat := 118140960795 + 4220655 * 2 ^ 59
def prefixEnd_4220655 : Nat := 4983230072969 + 3 ^ 40 * 4220655 * 2
def baseEnd_4220655 : Nat := 2167224691802289401602067

theorem tailTrace_4220655 : CollatzResearch.WordTrace tailWord_4220655 prefixEnd_4220655 2167224691802289401602067 := by
  unfold tailWord_4220655
  simp only [CollatzResearch.WordTrace]
  refine ⟨153939934524295240330863419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102626623016196826887242279 153939934524295240330863419)
  ·
    refine ⟨230909901786442860496295129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153939934524295240330863419 230909901786442860496295129)
    ·
      refine ⟨173182426339832145372221347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230909901786442860496295129 173182426339832145372221347)
      ·
        refine ⟨259773639509748218058332021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173182426339832145372221347 259773639509748218058332021)
        ·
          refine ⟨24353778704038895442968627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 259773639509748218058332021 24353778704038895442968627)
          ·
            refine ⟨36530668056058343164452941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24353778704038895442968627 36530668056058343164452941)
            ·
              refine ⟨13699000521021878686669853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36530668056058343164452941 13699000521021878686669853)
              ·
                refine ⟨5137125195383204507501195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13699000521021878686669853 5137125195383204507501195)
                ·
                  refine ⟨7705687793074806761251793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5137125195383204507501195 7705687793074806761251793)
                  ·
                    refine ⟨5779265844806105070938845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7705687793074806761251793 5779265844806105070938845)
                    ·
                      refine ⟨2167224691802289401602067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5779265844806105070938845 2167224691802289401602067)
                      ·
                        rfl

theorem cell23_4220655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 2, 3].length) (baseStart_4220655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220655 prefixEnd_4220655 := by exact prefixLift 4220655
  have htrace : WordTrace (prefixWord ++ tailWord_4220655) baseStart_4220655 baseEnd_4220655 := by
    simpa [prefixWord, tailWord_4220655, baseEnd_4220655] using wordTrace_append hprefix tailTrace_4220655
  have hstable : (prefixWord ++ tailWord_4220655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220655).length < 2 ^ (prefixWord ++ tailWord_4220655).sum := by decide
  have hdescent : baseEnd_4220655 < baseStart_4220655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220662 : List Nat := [5, 1, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_4220662 : Nat := 118140960795 + 4220662 * 2 ^ 59
def prefixEnd_4220662 : Nat := 4983230072969 + 3 ^ 40 * 4220662 * 2
def baseEnd_4220662 : Nat := 722409428722290291404845

theorem tailTrace_4220662 : CollatzResearch.WordTrace tailWord_4220662 prefixEnd_4220662 722409428722290291404845 := by
  unfold tailWord_4220662
  simp only [CollatzResearch.WordTrace]
  refine ⟨9621261864704367532898015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102626793223513253684245493 9621261864704367532898015)
  ·
    refine ⟨14431892797056551299347023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9621261864704367532898015 14431892797056551299347023)
    ·
      refine ⟨21647839195584826949020535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14431892797056551299347023 21647839195584826949020535)
      ·
        refine ⟨32471758793377240423530803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21647839195584826949020535 32471758793377240423530803)
        ·
          refine ⟨48707638190065860635296205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32471758793377240423530803 48707638190065860635296205)
          ·
            refine ⟨18265364321274697738236077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48707638190065860635296205 18265364321274697738236077)
            ·
              refine ⟨6849511620478011651838529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18265364321274697738236077 6849511620478011651838529)
              ·
                refine ⟨5137133715358508738878897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6849511620478011651838529 5137133715358508738878897)
                ·
                  refine ⟨3852850286518881554159173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5137133715358508738878897 3852850286518881554159173)
                  ·
                    refine ⟨722409428722290291404845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3852850286518881554159173 722409428722290291404845)
                    ·
                      rfl

theorem cell23_4220662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_4220662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220662 prefixEnd_4220662 := by exact prefixLift 4220662
  have htrace : WordTrace (prefixWord ++ tailWord_4220662) baseStart_4220662 baseEnd_4220662 := by
    simpa [prefixWord, tailWord_4220662, baseEnd_4220662] using wordTrace_append hprefix tailTrace_4220662
  have hstable : (prefixWord ++ tailWord_4220662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220662).length < 2 ^ (prefixWord ++ tailWord_4220662).sum := by decide
  have hdescent : baseEnd_4220662 < baseStart_4220662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220671 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 1, 9]
def baseStart_4220671 : Nat := 118140960795 + 4220671 * 2 ^ 59
def prefixEnd_4220671 : Nat := 4983230072969 + 3 ^ 40 * 4220671 * 2
def baseEnd_4220671 : Nat := 722410969164253779667331

theorem tailTrace_4220671 : CollatzResearch.WordTrace tailWord_4220671 prefixEnd_4220671 722410969164253779667331 := by
  unfold tailWord_4220671
  simp only [CollatzResearch.WordTrace]
  refine ⟨153940518092237275063445867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102627012061491516708963911 153940518092237275063445867)
  ·
    refine ⟨230910777138355912595168801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153940518092237275063445867 230910777138355912595168801)
    ·
      refine ⟨173183082853766934446376601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230910777138355912595168801 173183082853766934446376601)
      ·
        refine ⟨129887312140325200834782451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173183082853766934446376601 129887312140325200834782451)
        ·
          refine ⟨194830968210487801252173677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129887312140325200834782451 194830968210487801252173677)
          ·
            refine ⟨73061613078932925469565129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194830968210487801252173677 73061613078932925469565129)
            ·
              refine ⟨54796209809199694102173847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73061613078932925469565129 54796209809199694102173847)
              ·
                refine ⟨82194314713799541153260771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54796209809199694102173847 82194314713799541153260771)
                ·
                  refine ⟨123291472070699311729891157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82194314713799541153260771 123291472070699311729891157)
                  ·
                    refine ⟨722410969164253779667331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 123291472070699311729891157 722410969164253779667331)
                    ·
                      rfl

theorem cell23_4220671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_4220671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220671 prefixEnd_4220671 := by exact prefixLift 4220671
  have htrace : WordTrace (prefixWord ++ tailWord_4220671) baseStart_4220671 baseEnd_4220671 := by
    simpa [prefixWord, tailWord_4220671, baseEnd_4220671] using wordTrace_append hprefix tailTrace_4220671
  have hstable : (prefixWord ++ tailWord_4220671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220671).length < 2 ^ (prefixWord ++ tailWord_4220671).sum := by decide
  have hdescent : baseEnd_4220671 < baseStart_4220671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220679 : List Nat := [1, 1, 4, 4, 2, 1, 3, 1, 2, 4]
def baseStart_4220679 : Nat := 118140960795 + 4220679 * 2 ^ 59
def prefixEnd_4220679 : Nat := 4983230072969 + 3 ^ 40 * 4220679 * 2
def baseEnd_4220679 : Nat := 722412338445999102567319

theorem tailTrace_4220679 : CollatzResearch.WordTrace tailWord_4220679 prefixEnd_4220679 722412338445999102567319 := by
  unfold tailWord_4220679
  simp only [CollatzResearch.WordTrace]
  refine ⟨153940809876208292429737091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102627206584138861619824727 153940809876208292429737091)
  ·
    refine ⟨230911214814312438644605637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153940809876208292429737091 230911214814312438644605637)
    ·
      refine ⟨43295852777683582245863557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230911214814312438644605637 43295852777683582245863557)
      ·
        refine ⟨8117972395815671671099417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43295852777683582245863557 8117972395815671671099417)
        ·
          refine ⟨6088479296861753753324563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8117972395815671671099417 6088479296861753753324563)
          ·
            refine ⟨9132718945292630629986845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6088479296861753753324563 9132718945292630629986845)
            ·
              refine ⟨3424769604484736486245067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9132718945292630629986845 3424769604484736486245067)
              ·
                refine ⟨5137154406727104729367601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3424769604484736486245067 5137154406727104729367601)
                ·
                  refine ⟨3852865805045328547025701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5137154406727104729367601 3852865805045328547025701)
                  ·
                    refine ⟨722412338445999102567319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3852865805045328547025701 722412338445999102567319)
                    ·
                      rfl

theorem cell23_4220679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_4220679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220679 prefixEnd_4220679 := by exact prefixLift 4220679
  have htrace : WordTrace (prefixWord ++ tailWord_4220679) baseStart_4220679 baseEnd_4220679 := by
    simpa [prefixWord, tailWord_4220679, baseEnd_4220679] using wordTrace_append hprefix tailTrace_4220679
  have hstable : (prefixWord ++ tailWord_4220679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220679).length < 2 ^ (prefixWord ++ tailWord_4220679).sum := by decide
  have hdescent : baseEnd_4220679 < baseStart_4220679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220691 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 8]
def baseStart_4220691 : Nat := 118140960795 + 4220691 * 2 ^ 59
def prefixEnd_4220691 : Nat := 4983230072969 + 3 ^ 40 * 4220691 * 2
def baseEnd_4220691 : Nat := 2167243177105851260751901

theorem tailTrace_4220691 : CollatzResearch.WordTrace tailWord_4220691 prefixEnd_4220691 2167243177105851260751901 := by
  unfold tailWord_4220691
  simp only [CollatzResearch.WordTrace]
  refine ⟨153941247552164818479173927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102627498368109878986115951 153941247552164818479173927)
  ·
    refine ⟨230911871328247227718760891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153941247552164818479173927 230911871328247227718760891)
    ·
      refine ⟨346367806992370841578141337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230911871328247227718760891 346367806992370841578141337)
      ·
        refine ⟨259775855244278131183606003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346367806992370841578141337 259775855244278131183606003)
        ·
          refine ⟨389663782866417196775409005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259775855244278131183606003 389663782866417196775409005)
          ·
            refine ⟨146123918574906448790778377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 389663782866417196775409005 146123918574906448790778377)
            ·
              refine ⟨109592938931179836593083783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146123918574906448790778377 109592938931179836593083783)
              ·
                refine ⟨164389408396769754889625675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109592938931179836593083783 164389408396769754889625675)
                ·
                  refine ⟨246584112595154632334438513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164389408396769754889625675 246584112595154632334438513)
                  ·
                    refine ⟨184938084446365974250828885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 246584112595154632334438513 184938084446365974250828885)
                    ·
                      refine ⟨2167243177105851260751901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 184938084446365974250828885 2167243177105851260751901)
                      ·
                        rfl

theorem cell23_4220691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_4220691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220691 prefixEnd_4220691 := by exact prefixLift 4220691
  have htrace : WordTrace (prefixWord ++ tailWord_4220691) baseStart_4220691 baseEnd_4220691 := by
    simpa [prefixWord, tailWord_4220691, baseEnd_4220691] using wordTrace_append hprefix tailTrace_4220691
  have hstable : (prefixWord ++ tailWord_4220691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220691).length < 2 ^ (prefixWord ++ tailWord_4220691).sum := by decide
  have hdescent : baseEnd_4220691 < baseStart_4220691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220698 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_4220698 : Nat := 118140960795 + 4220698 * 2 ^ 59
def prefixEnd_4220698 : Nat := 4983230072969 + 3 ^ 40 * 4220698 * 2
def baseEnd_4220698 : Nat := 2167246771470432733364369

theorem tailTrace_4220698 : CollatzResearch.WordTrace tailWord_4220698 prefixEnd_4220698 2167246771470432733364369 := by
  unfold tailWord_4220698
  simp only [CollatzResearch.WordTrace]
  refine ⟨38485375715784864668669687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102627668575426305783119165 38485375715784864668669687)
  ·
    refine ⟨57728063573677297003004531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38485375715784864668669687 57728063573677297003004531)
    ·
      refine ⟨86592095360515945504506797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57728063573677297003004531 86592095360515945504506797)
      ·
        refine ⟨32472035760193479564190049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86592095360515945504506797 32472035760193479564190049)
        ·
          refine ⟨24354026820145109673142537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32472035760193479564190049 24354026820145109673142537)
          ·
            refine ⟨18265520115108832254856903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24354026820145109673142537 18265520115108832254856903)
            ·
              refine ⟨27398280172663248382285355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18265520115108832254856903 27398280172663248382285355)
              ·
                refine ⟨41097420258994872573428033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27398280172663248382285355 41097420258994872573428033)
                ·
                  refine ⟨30823065194246154430071025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41097420258994872573428033 30823065194246154430071025)
                  ·
                    refine ⟨23117298895684615822553269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30823065194246154430071025 23117298895684615822553269)
                    ·
                      refine ⟨2167246771470432733364369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23117298895684615822553269 2167246771470432733364369)
                      ·
                        rfl

theorem cell23_4220698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_4220698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220698 prefixEnd_4220698 := by exact prefixLift 4220698
  have htrace : WordTrace (prefixWord ++ tailWord_4220698) baseStart_4220698 baseEnd_4220698 := by
    simpa [prefixWord, tailWord_4220698, baseEnd_4220698] using wordTrace_append hprefix tailTrace_4220698
  have hstable : (prefixWord ++ tailWord_4220698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220698).length < 2 ^ (prefixWord ++ tailWord_4220698).sum := by decide
  have hdescent : baseEnd_4220698 < baseStart_4220698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220775 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_4220775 : Nat := 118140960795 + 4220775 * 2 ^ 59
def prefixEnd_4220775 : Nat := 4983230072969 + 3 ^ 40 * 4220775 * 2
def baseEnd_4220775 : Nat := 2167286309480828932101515

theorem tailTrace_4220775 : CollatzResearch.WordTrace tailWord_4220775 prefixEnd_4220775 2167286309480828932101515 := by
  unfold tailWord_4220775
  simp only [CollatzResearch.WordTrace]
  refine ⟨153944311283860500825231779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102629540855907000550154519 153944311283860500825231779)
  ·
    refine ⟨230916466925790751237847669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153944311283860500825231779 230916466925790751237847669)
    ·
      refine ⟨21648418774292882928548219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 230916466925790751237847669 21648418774292882928548219)
      ·
        refine ⟨32472628161439324392822329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21648418774292882928548219 32472628161439324392822329)
        ·
          refine ⟨24354471121079493294616747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32472628161439324392822329 24354471121079493294616747)
          ·
            refine ⟨36531706681619239941925121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24354471121079493294616747 36531706681619239941925121)
            ·
              refine ⟨27398780011214429956443841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36531706681619239941925121 27398780011214429956443841)
              ·
                refine ⟨20549085008410822467332881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27398780011214429956443841 20549085008410822467332881)
                ·
                  refine ⟨15411813756308116850499661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20549085008410822467332881 15411813756308116850499661)
                  ·
                    refine ⟨5779430158615543818937373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15411813756308116850499661 5779430158615543818937373)
                    ·
                      refine ⟨2167286309480828932101515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5779430158615543818937373 2167286309480828932101515)
                      ·
                        rfl

theorem cell23_4220775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_4220775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220775 prefixEnd_4220775 := by exact prefixLift 4220775
  have htrace : WordTrace (prefixWord ++ tailWord_4220775) baseStart_4220775 baseEnd_4220775 := by
    simpa [prefixWord, tailWord_4220775, baseEnd_4220775] using wordTrace_append hprefix tailTrace_4220775
  have hstable : (prefixWord ++ tailWord_4220775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220775).length < 2 ^ (prefixWord ++ tailWord_4220775).sum := by decide
  have hdescent : baseEnd_4220775 < baseStart_4220775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220785 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 1, 7, 2]
def baseStart_4220785 : Nat := 118140960795 + 4220785 * 2 ^ 59
def prefixEnd_4220785 : Nat := 4983230072969 + 3 ^ 40 * 4220785 * 2
def baseEnd_4220785 : Nat := 2167291444287373892976469

theorem tailTrace_4220785 : CollatzResearch.WordTrace tailWord_4220785 prefixEnd_4220785 2167291444287373892976469 := by
  unfold tailWord_4220785
  simp only [CollatzResearch.WordTrace]
  refine ⟨153944676013824272533095809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102629784009216181688730539 153944676013824272533095809)
  ·
    refine ⟨115458507010368204399821857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153944676013824272533095809 115458507010368204399821857)
    ·
      refine ⟨86593880257776153299866393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115458507010368204399821857 86593880257776153299866393)
      ·
        refine ⟨64945410193332114974899795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86593880257776153299866393 64945410193332114974899795)
        ·
          refine ⟨97418115289998172462349693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64945410193332114974899795 97418115289998172462349693)
          ·
            refine ⟨36531793233749314673381135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97418115289998172462349693 36531793233749314673381135)
            ·
              refine ⟨54797689850623972010071703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36531793233749314673381135 54797689850623972010071703)
              ·
                refine ⟨82196534775935958015107555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54797689850623972010071703 82196534775935958015107555)
                ·
                  refine ⟨123294802163903937022661333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82196534775935958015107555 123294802163903937022661333)
                  ·
                    refine ⟨2889721925716498523968625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 123294802163903937022661333 2889721925716498523968625)
                    ·
                      refine ⟨2167291444287373892976469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2889721925716498523968625 2167291444287373892976469)
                      ·
                        rfl

theorem cell23_4220785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_4220785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220785 prefixEnd_4220785 := by exact prefixLift 4220785
  have htrace : WordTrace (prefixWord ++ tailWord_4220785) baseStart_4220785 baseEnd_4220785 := by
    simpa [prefixWord, tailWord_4220785, baseEnd_4220785] using wordTrace_append hprefix tailTrace_4220785
  have hstable : (prefixWord ++ tailWord_4220785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220785).length < 2 ^ (prefixWord ++ tailWord_4220785).sum := by decide
  have hdescent : baseEnd_4220785 < baseStart_4220785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220835 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 3]
def baseStart_4220835 : Nat := 118140960795 + 4220835 * 2 ^ 59
def prefixEnd_4220835 : Nat := 4983230072969 + 3 ^ 40 * 4220835 * 2
def baseEnd_4220835 : Nat := 2167317118320098697351239

theorem tailTrace_4220835 : CollatzResearch.WordTrace tailWord_4220835 prefixEnd_4220835 2167317118320098697351239 := by
  unfold tailWord_4220835
  simp only [CollatzResearch.WordTrace]
  refine ⟨153946499663643131072415959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102630999775762087381610639 153946499663643131072415959)
  ·
    refine ⟨230919749495464696608623939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153946499663643131072415959 230919749495464696608623939)
    ·
      refine ⟨346379624243197044912935909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230919749495464696608623939 346379624243197044912935909)
      ·
        refine ⟨64946179545599445921175483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 346379624243197044912935909 64946179545599445921175483)
        ·
          refine ⟨97419269318399168881763225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64946179545599445921175483 97419269318399168881763225)
          ·
            refine ⟨73064451988799376661322419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97419269318399168881763225 73064451988799376661322419)
            ·
              refine ⟨109596677983199064991983629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73064451988799376661322419 109596677983199064991983629)
              ·
                refine ⟨41098754243699649371993861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109596677983199064991983629 41098754243699649371993861)
                ·
                  refine ⟨7706016420693684257248849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41098754243699649371993861 7706016420693684257248849)
                  ·
                    refine ⟨5779512315520263192936637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7706016420693684257248849 5779512315520263192936637)
                    ·
                      refine ⟨2167317118320098697351239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5779512315520263192936637 2167317118320098697351239)
                      ·
                        rfl

theorem cell23_4220835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_4220835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220835 prefixEnd_4220835 := by exact prefixLift 4220835
  have htrace : WordTrace (prefixWord ++ tailWord_4220835) baseStart_4220835 baseEnd_4220835 := by
    simpa [prefixWord, tailWord_4220835, baseEnd_4220835] using wordTrace_append hprefix tailTrace_4220835
  have hstable : (prefixWord ++ tailWord_4220835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220835).length < 2 ^ (prefixWord ++ tailWord_4220835).sum := by decide
  have hdescent : baseEnd_4220835 < baseStart_4220835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220876 : List Nat := [2, 2, 1, 4, 1, 4, 1, 3, 1, 4]
def baseStart_4220876 : Nat := 118140960795 + 4220876 * 2 ^ 59
def prefixEnd_4220876 : Nat := 4983230072969 + 3 ^ 40 * 4220876 * 2
def baseEnd_4220876 : Nat := 722446057008977678979517

theorem tailTrace_4220876 : CollatzResearch.WordTrace tailWord_4220876 prefixEnd_4220876 722446057008977678979517 := by
  unfold tailWord_4220876
  simp only [CollatzResearch.WordTrace]
  refine ⟨76973997528247297537329241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102631996704329730049772321 76973997528247297537329241)
  ·
    refine ⟨57730498146185473152996931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76973997528247297537329241 57730498146185473152996931)
    ·
      refine ⟨86595747219278209729495397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57730498146185473152996931 86595747219278209729495397)
      ·
        refine ⟨16236702603614664324280387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86595747219278209729495397 16236702603614664324280387)
        ·
          refine ⟨24355053905421996486420581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16236702603614664324280387 24355053905421996486420581)
          ·
            refine ⟨4566572607266624341203859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24355053905421996486420581 4566572607266624341203859)
            ·
              refine ⟨6849858910899936511805789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4566572607266624341203859 6849858910899936511805789)
              ·
                refine ⟨2568697091587476191927171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6849858910899936511805789 2568697091587476191927171)
                ·
                  refine ⟨3853045637381214287890757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568697091587476191927171 3853045637381214287890757)
                  ·
                    refine ⟨722446057008977678979517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3853045637381214287890757 722446057008977678979517)
                    ·
                      rfl

theorem cell23_4220876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_4220876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220876 prefixEnd_4220876 := by exact prefixLift 4220876
  have htrace : WordTrace (prefixWord ++ tailWord_4220876) baseStart_4220876 baseEnd_4220876 := by
    simpa [prefixWord, tailWord_4220876, baseEnd_4220876] using wordTrace_append hprefix tailTrace_4220876
  have hstable : (prefixWord ++ tailWord_4220876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220876).length < 2 ^ (prefixWord ++ tailWord_4220876).sum := by decide
  have hdescent : baseEnd_4220876 < baseStart_4220876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220886 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_4220886 : Nat := 118140960795 + 4220886 * 2 ^ 59
def prefixEnd_4220886 : Nat := 4983230072969 + 3 ^ 40 * 4220886 * 2
def baseEnd_4220886 : Nat := 2167343305833477997813505

theorem tailTrace_4220886 : CollatzResearch.WordTrace tailWord_4220886 prefixEnd_4220886 2167343305833477997813505 := by
  unfold tailWord_4220886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9621772486653647923907657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102632239857638911188348341 9621772486653647923907657)
  ·
    refine ⟨7216329364990235942930743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9621772486653647923907657 7216329364990235942930743)
    ·
      refine ⟨10824494047485353914396115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7216329364990235942930743 10824494047485353914396115)
      ·
        refine ⟨16236741071228030871594173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10824494047485353914396115 16236741071228030871594173)
        ·
          refine ⟨6088777901710511576847815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16236741071228030871594173 6088777901710511576847815)
          ·
            refine ⟨9133166852565767365271723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6088777901710511576847815 9133166852565767365271723)
            ·
              refine ⟨13699750278848651047907585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9133166852565767365271723 13699750278848651047907585)
              ·
                refine ⟨10274812709136488285930689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13699750278848651047907585 10274812709136488285930689)
                ·
                  refine ⟨7706109531852366214448017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10274812709136488285930689 7706109531852366214448017)
                  ·
                    refine ⟨5779582148889274660836013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7706109531852366214448017 5779582148889274660836013)
                    ·
                      refine ⟨2167343305833477997813505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5779582148889274660836013 2167343305833477997813505)
                      ·
                        rfl

theorem cell23_4220886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_4220886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220886 prefixEnd_4220886 := by exact prefixLift 4220886
  have htrace : WordTrace (prefixWord ++ tailWord_4220886) baseStart_4220886 baseEnd_4220886 := by
    simpa [prefixWord, tailWord_4220886, baseEnd_4220886] using wordTrace_append hprefix tailTrace_4220886
  have hstable : (prefixWord ++ tailWord_4220886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220886).length < 2 ^ (prefixWord ++ tailWord_4220886).sum := by decide
  have hdescent : baseEnd_4220886 < baseStart_4220886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220893 : List Nat := [1, 4, 3, 1, 3, 1, 3, 2, 1, 4]
def baseStart_4220893 : Nat := 118140960795 + 4220893 * 2 ^ 59
def prefixEnd_4220893 : Nat := 4983230072969 + 3 ^ 40 * 4220893 * 2
def baseEnd_4220893 : Nat := 722448966732686490141991

theorem tailTrace_4220893 : CollatzResearch.WordTrace tailWord_4220893 prefixEnd_4220893 722448966732686490141991 := by
  unfold tailWord_4220893
  simp only [CollatzResearch.WordTrace]
  refine ⟨153948615097433006978027333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102632410064955337985351555 153948615097433006978027333)
  ·
    refine ⟨28865365330768688808380125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153948615097433006978027333 28865365330768688808380125)
    ·
      refine ⟨10824511999038258303142547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28865365330768688808380125 10824511999038258303142547)
      ·
        refine ⟨16236767998557387454713821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10824511999038258303142547 16236767998557387454713821)
        ·
          refine ⟨6088787999459020295517683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16236767998557387454713821 6088787999459020295517683)
          ·
            refine ⟨9133181999188530443276525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6088787999459020295517683 9133181999188530443276525)
            ·
              refine ⟨3424943249695698916228697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9133181999188530443276525 3424943249695698916228697)
              ·
                refine ⟨2568707437271774187171523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3424943249695698916228697 2568707437271774187171523)
                ·
                  refine ⟨3853061155907661280757285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568707437271774187171523 3853061155907661280757285)
                  ·
                    refine ⟨722448966732686490141991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3853061155907661280757285 722448966732686490141991)
                    ·
                      rfl

theorem cell23_4220893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_4220893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220893 prefixEnd_4220893 := by exact prefixLift 4220893
  have htrace : WordTrace (prefixWord ++ tailWord_4220893) baseStart_4220893 baseEnd_4220893 := by
    simpa [prefixWord, tailWord_4220893, baseEnd_4220893] using wordTrace_append hprefix tailTrace_4220893
  have hstable : (prefixWord ++ tailWord_4220893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220893).length < 2 ^ (prefixWord ++ tailWord_4220893).sum := by decide
  have hdescent : baseEnd_4220893 < baseStart_4220893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220899 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 3, 1, 3]
def baseStart_4220899 : Nat := 118140960795 + 4220899 * 2 ^ 59
def prefixEnd_4220899 : Nat := 4983230072969 + 3 ^ 40 * 4220899 * 2
def baseEnd_4220899 : Nat := 2167349981081986446950945

theorem tailTrace_4220899 : CollatzResearch.WordTrace tailWord_4220899 prefixEnd_4220899 2167349981081986446950945 := by
  unfold tailWord_4220899
  simp only [CollatzResearch.WordTrace]
  refine ⟨153948833935411270002745751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102632555956940846668497167 153948833935411270002745751)
  ·
    refine ⟨230923250903116905004118627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153948833935411270002745751 230923250903116905004118627)
    ·
      refine ⟨346384876354675357506177941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230923250903116905004118627 346384876354675357506177941)
      ·
        refine ⟨16236791079125407383102091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 346384876354675357506177941 16236791079125407383102091)
        ·
          refine ⟨24355186618688111074653137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16236791079125407383102091 24355186618688111074653137)
          ·
            refine ⟨18266389964016083305989853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24355186618688111074653137 18266389964016083305989853)
            ·
              refine ⟨6849896236506031239746195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18266389964016083305989853 6849896236506031239746195)
              ·
                refine ⟨10274844354759046859619293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6849896236506031239746195 10274844354759046859619293)
                ·
                  refine ⟨3853066633034642572357235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10274844354759046859619293 3853066633034642572357235)
                  ·
                    refine ⟨5779599949551963858535853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3853066633034642572357235 5779599949551963858535853)
                    ·
                      refine ⟨2167349981081986446950945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5779599949551963858535853 2167349981081986446950945)
                      ·
                        rfl

theorem cell23_4220899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_4220899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220899 prefixEnd_4220899 := by exact prefixLift 4220899
  have htrace : WordTrace (prefixWord ++ tailWord_4220899) baseStart_4220899 baseEnd_4220899 := by
    simpa [prefixWord, tailWord_4220899, baseEnd_4220899] using wordTrace_append hprefix tailTrace_4220899
  have hstable : (prefixWord ++ tailWord_4220899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220899).length < 2 ^ (prefixWord ++ tailWord_4220899).sum := by decide
  have hdescent : baseEnd_4220899 < baseStart_4220899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220925 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_4220925 : Nat := 118140960795 + 4220925 * 2 ^ 59
def prefixEnd_4220925 : Nat := 4983230072969 + 3 ^ 40 * 4220925 * 2
def baseEnd_4220925 : Nat := 2167363331579003345225825

theorem tailTrace_4220925 : CollatzResearch.WordTrace tailWord_4220925 prefixEnd_4220925 2167363331579003345225825 := by
  unfold tailWord_4220925
  simp only [CollatzResearch.WordTrace]
  refine ⟨153949782233317076443192229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102633188155544717628794819 153949782233317076443192229)
  ·
    refine ⟨28865584168746951833098543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153949782233317076443192229 28865584168746951833098543)
    ·
      refine ⟨43298376253120427749647815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28865584168746951833098543 43298376253120427749647815)
      ·
        refine ⟨64947564379680641624471723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43298376253120427749647815 64947564379680641624471723)
        ·
          refine ⟨97421346569520962436707585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64947564379680641624471723 97421346569520962436707585)
          ·
            refine ⟨73066009927140721827530689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97421346569520962436707585 73066009927140721827530689)
            ·
              refine ⟨54799507445355541370648017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73066009927140721827530689 54799507445355541370648017)
              ·
                refine ⟨41099630584016656027986013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54799507445355541370648017 41099630584016656027986013)
                ·
                  refine ⟨15412361469006246010494755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41099630584016656027986013 15412361469006246010494755)
                  ·
                    refine ⟨23118542203509369015742133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15412361469006246010494755 23118542203509369015742133)
                    ·
                      refine ⟨2167363331579003345225825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23118542203509369015742133 2167363331579003345225825)
                      ·
                        rfl

theorem cell23_4220925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_4220925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220925 prefixEnd_4220925 := by exact prefixLift 4220925
  have htrace : WordTrace (prefixWord ++ tailWord_4220925) baseStart_4220925 baseEnd_4220925 := by
    simpa [prefixWord, tailWord_4220925, baseEnd_4220925] using wordTrace_append hprefix tailTrace_4220925
  have hstable : (prefixWord ++ tailWord_4220925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220925).length < 2 ^ (prefixWord ++ tailWord_4220925).sum := by decide
  have hdescent : baseEnd_4220925 < baseStart_4220925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220926 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_4220926 : Nat := 118140960795 + 4220926 * 2 ^ 59
def prefixEnd_4220926 : Nat := 4983230072969 + 3 ^ 40 * 4220926 * 2
def baseEnd_4220926 : Nat := 2167363845059657841313321

theorem tailTrace_4220926 : CollatzResearch.WordTrace tailWord_4220926 prefixEnd_4220926 2167363845059657841313321 := by
  unfold tailWord_4220926
  simp only [CollatzResearch.WordTrace]
  refine ⟨19243727338289181701747329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102633212470875635742652421 19243727338289181701747329)
  ·
    refine ⟨14432795503716886276310497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19243727338289181701747329 14432795503716886276310497)
    ·
      refine ⟨10824596627787664707232873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14432795503716886276310497 10824596627787664707232873)
      ·
        refine ⟨8118447470840748530424655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10824596627787664707232873 8118447470840748530424655)
        ·
          refine ⟨12177671206261122795636983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8118447470840748530424655 12177671206261122795636983)
          ·
            refine ⟨18266506809391684193455475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12177671206261122795636983 18266506809391684193455475)
            ·
              refine ⟨27399760214087526290183213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18266506809391684193455475 27399760214087526290183213)
              ·
                refine ⟨10274910080282822358818705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27399760214087526290183213 10274910080282822358818705)
                ·
                  refine ⟨7706182560212116769114029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10274910080282822358818705 7706182560212116769114029)
                  ·
                    refine ⟨2889818460079543788417761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7706182560212116769114029 2889818460079543788417761)
                    ·
                      refine ⟨2167363845059657841313321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2889818460079543788417761 2167363845059657841313321)
                      ·
                        rfl

theorem cell23_4220926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_4220926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220926 prefixEnd_4220926 := by exact prefixLift 4220926
  have htrace : WordTrace (prefixWord ++ tailWord_4220926) baseStart_4220926 baseEnd_4220926 := by
    simpa [prefixWord, tailWord_4220926, baseEnd_4220926] using wordTrace_append hprefix tailTrace_4220926
  have hstable : (prefixWord ++ tailWord_4220926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220926).length < 2 ^ (prefixWord ++ tailWord_4220926).sum := by decide
  have hdescent : baseEnd_4220926 < baseStart_4220926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220939 : List Nat := [1, 1, 1, 1, 6, 1, 5, 1, 1, 1, 4]
def baseStart_4220939 : Nat := 118140960795 + 4220939 * 2 ^ 59
def prefixEnd_4220939 : Nat := 4983230072969 + 3 ^ 40 * 4220939 * 2
def baseEnd_4220939 : Nat := 2167370520308166290450761

theorem tailTrace_4220939 : CollatzResearch.WordTrace tailWord_4220939 prefixEnd_4220939 2167370520308166290450761 := by
  unfold tailWord_4220939
  simp only [CollatzResearch.WordTrace]
  refine ⟨153950292855266356834201871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102633528570177571222801247 153950292855266356834201871)
  ·
    refine ⟨230925439282899535251302807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153950292855266356834201871 230925439282899535251302807)
    ·
      refine ⟨346388158924349302876954211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230925439282899535251302807 346388158924349302876954211)
      ·
        refine ⟨519582238386523954315431317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346388158924349302876954211 519582238386523954315431317)
        ·
          refine ⟨24355417424368310358535843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 519582238386523954315431317 24355417424368310358535843)
          ·
            refine ⟨36533126136552465537803765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24355417424368310358535843 36533126136552465537803765)
            ·
              refine ⟨3424980575301793644169103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36533126136552465537803765 3424980575301793644169103)
              ·
                refine ⟨5137470862952690466253655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3424980575301793644169103 5137470862952690466253655)
                ·
                  refine ⟨7706206294429035699380483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5137470862952690466253655 7706206294429035699380483)
                  ·
                    refine ⟨11559309441643553549070725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7706206294429035699380483 11559309441643553549070725)
                    ·
                      refine ⟨2167370520308166290450761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11559309441643553549070725 2167370520308166290450761)
                      ·
                        rfl

theorem cell23_4220939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 1, 1, 4].length) (baseStart_4220939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220939 prefixEnd_4220939 := by exact prefixLift 4220939
  have htrace : WordTrace (prefixWord ++ tailWord_4220939) baseStart_4220939 baseEnd_4220939 := by
    simpa [prefixWord, tailWord_4220939, baseEnd_4220939] using wordTrace_append hprefix tailTrace_4220939
  have hstable : (prefixWord ++ tailWord_4220939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220939).length < 2 ^ (prefixWord ++ tailWord_4220939).sum := by decide
  have hdescent : baseEnd_4220939 < baseStart_4220939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220989 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 4, 1, 3]
def baseStart_4220989 : Nat := 118140960795 + 4220989 * 2 ^ 59
def prefixEnd_4220989 : Nat := 4983230072969 + 3 ^ 40 * 4220989 * 2
def baseEnd_4220989 : Nat := 2167396194340891094825531

theorem tailTrace_4220989 : CollatzResearch.WordTrace tailWord_4220989 prefixEnd_4220989 2167396194340891094825531 := by
  unfold tailWord_4220989
  simp only [CollatzResearch.WordTrace]
  refine ⟨153952116505085215373522021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102634744336723476915681347 153952116505085215373522021)
  ·
    refine ⟨28866021844703477882535379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153952116505085215373522021 28866021844703477882535379)
    ·
      refine ⟨43299032767055216823803069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28866021844703477882535379 43299032767055216823803069)
      ·
        refine ⟨16237137287645706308926151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43299032767055216823803069 16237137287645706308926151)
        ·
          refine ⟨24355705931468559463389227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16237137287645706308926151 24355705931468559463389227)
          ·
            refine ⟨36533558897202839195083841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24355705931468559463389227 36533558897202839195083841)
            ·
              refine ⟨27400169172902129396312881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36533558897202839195083841 27400169172902129396312881)
              ·
                refine ⟨20550126879676597047234661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27400169172902129396312881 20550126879676597047234661)
                ·
                  refine ⟨3853148789939361946356499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20550126879676597047234661 3853148789939361946356499)
                  ·
                    refine ⟨5779723184909042919534749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3853148789939361946356499 5779723184909042919534749)
                    ·
                      refine ⟨2167396194340891094825531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5779723184909042919534749 2167396194340891094825531)
                      ·
                        rfl

theorem cell23_4220989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_4220989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220989 prefixEnd_4220989 := by exact prefixLift 4220989
  have htrace : WordTrace (prefixWord ++ tailWord_4220989) baseStart_4220989 baseEnd_4220989 := by
    simpa [prefixWord, tailWord_4220989, baseEnd_4220989] using wordTrace_append hprefix tailTrace_4220989
  have hstable : (prefixWord ++ tailWord_4220989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220989).length < 2 ^ (prefixWord ++ tailWord_4220989).sum := by decide
  have hdescent : baseEnd_4220989 < baseStart_4220989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220990 : List Nat := [4, 2, 1, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_4220990 : Nat := 118140960795 + 4220990 * 2 ^ 59
def prefixEnd_4220990 : Nat := 4983230072969 + 3 ^ 40 * 4220990 * 2
def baseEnd_4220990 : Nat := 2167396707821545590913027

theorem tailTrace_4220990 : CollatzResearch.WordTrace tailWord_4220990 prefixEnd_4220990 2167396707821545590913027 := by
  unfold tailWord_4220990
  simp only [CollatzResearch.WordTrace]
  refine ⟨19244019122260199068038553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102634768652054395029538949 19244019122260199068038553)
  ·
    refine ⟨14433014341695149301028915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19244019122260199068038553 14433014341695149301028915)
    ·
      refine ⟨21649521512542723951543373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14433014341695149301028915 21649521512542723951543373)
      ·
        refine ⟨8118570567203521481828765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21649521512542723951543373 8118570567203521481828765)
        ·
          refine ⟨3044463962701320555685787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8118570567203521481828765 3044463962701320555685787)
          ·
            refine ⟨4566695944051980833528681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3044463962701320555685787 4566695944051980833528681)
            ·
              refine ⟨3425021958038985625146511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4566695944051980833528681 3425021958038985625146511)
              ·
                refine ⟨5137532937058478437719767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3425021958038985625146511 5137532937058478437719767)
                ·
                  refine ⟨7706299405587717656579651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5137532937058478437719767 7706299405587717656579651)
                  ·
                    refine ⟨11559449108381576484869477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7706299405587717656579651 11559449108381576484869477)
                    ·
                      refine ⟨2167396707821545590913027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11559449108381576484869477 2167396707821545590913027)
                      ·
                        rfl

theorem cell23_4220990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_4220990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220990 prefixEnd_4220990 := by exact prefixLift 4220990
  have htrace : WordTrace (prefixWord ++ tailWord_4220990) baseStart_4220990 baseEnd_4220990 := by
    simpa [prefixWord, tailWord_4220990, baseEnd_4220990] using wordTrace_append hprefix tailTrace_4220990
  have hstable : (prefixWord ++ tailWord_4220990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220990).length < 2 ^ (prefixWord ++ tailWord_4220990).sum := by decide
  have hdescent : baseEnd_4220990 < baseStart_4220990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220993 : List Nat := [1, 2, 5, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_4220993 : Nat := 118140960795 + 4220993 * 2 ^ 59
def prefixEnd_4220993 : Nat := 4983230072969 + 3 ^ 40 * 4220993 * 2
def baseEnd_4220993 : Nat := 2167398248263509079175513

theorem tailTrace_4220993 : CollatzResearch.WordTrace tailWord_4220993 prefixEnd_4220993 2167398248263509079175513 := by
  unfold tailWord_4220993
  simp only [CollatzResearch.WordTrace]
  refine ⟨153952262397070724056667633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102634841598047149371111755 153952262397070724056667633)
  ·
    refine ⟨115464196797803043042500725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153952262397070724056667633 115464196797803043042500725)
    ·
      refine ⟨10824768449794035285234443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115464196797803043042500725 10824768449794035285234443)
      ·
        refine ⟨16237152674691052927851665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10824768449794035285234443 16237152674691052927851665)
        ·
          refine ⟨12177864506018289695888749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16237152674691052927851665 12177864506018289695888749)
          ·
            refine ⟨4566699189756858635958281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12177864506018289695888749 4566699189756858635958281)
            ·
              refine ⟨3425024392317643976968711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4566699189756858635958281 3425024392317643976968711)
              ·
                refine ⟨5137536588476465965453067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3425024392317643976968711 5137536588476465965453067)
                ·
                  refine ⟨7706304882714698948179601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5137536588476465965453067 7706304882714698948179601)
                  ·
                    refine ⟨5779728662036024211134701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7706304882714698948179601 5779728662036024211134701)
                    ·
                      refine ⟨2167398248263509079175513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5779728662036024211134701 2167398248263509079175513)
                      ·
                        rfl

theorem cell23_4220993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_4220993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220993 prefixEnd_4220993 := by exact prefixLift 4220993
  have htrace : WordTrace (prefixWord ++ tailWord_4220993) baseStart_4220993 baseEnd_4220993 := by
    simpa [prefixWord, tailWord_4220993, baseEnd_4220993] using wordTrace_append hprefix tailTrace_4220993
  have hstable : (prefixWord ++ tailWord_4220993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220993).length < 2 ^ (prefixWord ++ tailWord_4220993).sum := by decide
  have hdescent : baseEnd_4220993 < baseStart_4220993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4220995 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 4]
def baseStart_4220995 : Nat := 118140960795 + 4220995 * 2 ^ 59
def prefixEnd_4220995 : Nat := 4983230072969 + 3 ^ 40 * 4220995 * 2
def baseEnd_4220995 : Nat := 2167399275224818071350503

theorem tailTrace_4220995 : CollatzResearch.WordTrace tailWord_4220995 prefixEnd_4220995 2167399275224818071350503 := by
  unfold tailWord_4220995
  simp only [CollatzResearch.WordTrace]
  refine ⟨153952335343063478398240439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102634890228708985598826959 153952335343063478398240439)
  ·
    refine ⟨230928503014595217597360659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153952335343063478398240439 230928503014595217597360659)
    ·
      refine ⟨346392754521892826396040989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230928503014595217597360659 346392754521892826396040989)
      ·
        refine ⟨129897282945709809898515371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346392754521892826396040989 129897282945709809898515371)
        ·
          refine ⟨194845924418564714847773057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129897282945709809898515371 194845924418564714847773057)
          ·
            refine ⟨146134443313923536135829793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194845924418564714847773057 146134443313923536135829793)
            ·
              refine ⟨109600832485442652101872345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146134443313923536135829793 109600832485442652101872345)
              ·
                refine ⟨82200624364081989076404259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109600832485442652101872345 82200624364081989076404259)
                ·
                  refine ⟨123300936546122983614606389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82200624364081989076404259 123300936546122983614606389)
                  ·
                    refine ⟨11559462801199029713869349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 123300936546122983614606389 11559462801199029713869349)
                    ·
                      refine ⟨2167399275224818071350503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11559462801199029713869349 2167399275224818071350503)
                      ·
                        rfl

theorem cell23_4220995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_4220995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4220995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4220995 prefixEnd_4220995 := by exact prefixLift 4220995
  have htrace : WordTrace (prefixWord ++ tailWord_4220995) baseStart_4220995 baseEnd_4220995 := by
    simpa [prefixWord, tailWord_4220995, baseEnd_4220995] using wordTrace_append hprefix tailTrace_4220995
  have hstable : (prefixWord ++ tailWord_4220995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4220995).length < 2 ^ (prefixWord ++ tailWord_4220995).sum := by decide
  have hdescent : baseEnd_4220995 < baseStart_4220995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4220995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221006 : List Nat := [4, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3]
def baseStart_4221006 : Nat := 118140960795 + 4221006 * 2 ^ 59
def prefixEnd_4221006 : Nat := 4983230072969 + 3 ^ 40 * 4221006 * 2
def baseEnd_4221006 : Nat := 2167404923512017528312953

theorem tailTrace_4221006 : CollatzResearch.WordTrace tailWord_4221006 prefixEnd_4221006 2167404923512017528312953 := by
  unfold tailWord_4221006
  simp only [CollatzResearch.WordTrace]
  refine ⟨19244092068252953409611359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102635157697349084851260581 19244092068252953409611359)
  ·
    refine ⟨28866138102379430114417039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19244092068252953409611359 28866138102379430114417039)
    ·
      refine ⟨43299207153569145171625559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28866138102379430114417039 43299207153569145171625559)
      ·
        refine ⟨64948810730353717757438339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43299207153569145171625559 64948810730353717757438339)
        ·
          refine ⟨97423216095530576636157509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64948810730353717757438339 97423216095530576636157509)
          ·
            refine ⟨18266853017911983119279533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97423216095530576636157509 18266853017911983119279533)
            ·
              refine ⟨6850069881716993669729825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18266853017911983119279533 6850069881716993669729825)
              ·
                refine ⟨5137552411287745252297369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6850069881716993669729825 5137552411287745252297369)
                ·
                  refine ⟨3853164308465808939223027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5137552411287745252297369 3853164308465808939223027)
                  ·
                    refine ⟨5779746462698713408834541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3853164308465808939223027 5779746462698713408834541)
                    ·
                      refine ⟨2167404923512017528312953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5779746462698713408834541 2167404923512017528312953)
                      ·
                        rfl

theorem cell23_4221006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_4221006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221006 prefixEnd_4221006 := by exact prefixLift 4221006
  have htrace : WordTrace (prefixWord ++ tailWord_4221006) baseStart_4221006 baseEnd_4221006 := by
    simpa [prefixWord, tailWord_4221006, baseEnd_4221006] using wordTrace_append hprefix tailTrace_4221006
  have hstable : (prefixWord ++ tailWord_4221006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221006).length < 2 ^ (prefixWord ++ tailWord_4221006).sum := by decide
  have hdescent : baseEnd_4221006 < baseStart_4221006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221055 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 6]
def baseStart_4221055 : Nat := 118140960795 + 4221055 * 2 ^ 59
def prefixEnd_4221055 : Nat := 4983230072969 + 3 ^ 40 * 4221055 * 2
def baseEnd_4221055 : Nat := 2167430084064087836600227

theorem tailTrace_4221055 : CollatzResearch.WordTrace tailWord_4221055 prefixEnd_4221055 2167430084064087836600227 := by
  unfold tailWord_4221055
  simp only [CollatzResearch.WordTrace]
  refine ⟨153954523722846108645424619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102636349148564072430283079 153954523722846108645424619)
  ·
    refine ⟨230931785584269162968136929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153954523722846108645424619 230931785584269162968136929)
    ·
      refine ⟨173198839188201872226102697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230931785584269162968136929 173198839188201872226102697)
      ·
        refine ⟨129899129391151404169577023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173198839188201872226102697 129899129391151404169577023)
        ·
          refine ⟨194848694086727106254365535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129899129391151404169577023 194848694086727106254365535)
          ·
            refine ⟨292273041130090659381548303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194848694086727106254365535 292273041130090659381548303)
            ·
              refine ⟨438409561695135989072322455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292273041130090659381548303 438409561695135989072322455)
              ·
                refine ⟨657614342542703983608483683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438409561695135989072322455 657614342542703983608483683)
                ·
                  refine ⟨986421513814055975412725525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657614342542703983608483683 986421513814055975412725525)
                  ·
                    refine ⟨46238508460033873847471509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 986421513814055975412725525 46238508460033873847471509)
                    ·
                      refine ⟨2167430084064087836600227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46238508460033873847471509 2167430084064087836600227)
                      ·
                        rfl

theorem cell23_4221055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_4221055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221055 prefixEnd_4221055 := by exact prefixLift 4221055
  have htrace : WordTrace (prefixWord ++ tailWord_4221055) baseStart_4221055 baseEnd_4221055 := by
    simpa [prefixWord, tailWord_4221055, baseEnd_4221055] using wordTrace_append hprefix tailTrace_4221055
  have hstable : (prefixWord ++ tailWord_4221055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221055).length < 2 ^ (prefixWord ++ tailWord_4221055).sum := by decide
  have hdescent : baseEnd_4221055 < baseStart_4221055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221119 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 2, 4, 2]
def baseStart_4221119 : Nat := 118140960795 + 4221119 * 2 ^ 59
def prefixEnd_4221119 : Nat := 4983230072969 + 3 ^ 40 * 4221119 * 2
def baseEnd_4221119 : Nat := 2167462946825975586199933

theorem tailTrace_4221119 : CollatzResearch.WordTrace tailWord_4221119 prefixEnd_4221119 2167462946825975586199933 := by
  unfold tailWord_4221119
  simp only [CollatzResearch.WordTrace]
  refine ⟨153956857994614247575754411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102637905329742831717169607 153956857994614247575754411)
  ·
    refine ⟨230935286991921371363631617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153956857994614247575754411 230935286991921371363631617)
    ·
      refine ⟨173201465243941028522723713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230935286991921371363631617 173201465243941028522723713)
      ·
        refine ⟨129901098932955771392042785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173201465243941028522723713 129901098932955771392042785)
        ·
          refine ⟨97425824199716828544032089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129901098932955771392042785 97425824199716828544032089)
          ·
            refine ⟨73069368149787621408024067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97425824199716828544032089 73069368149787621408024067)
            ·
              refine ⟨109604052224681432112036101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73069368149787621408024067 109604052224681432112036101)
              ·
                refine ⟨20550759792127768521006769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109604052224681432112036101 20550759792127768521006769)
                ·
                  refine ⟨15413069844095826390755077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20550759792127768521006769 15413069844095826390755077)
                  ·
                    refine ⟨2889950595767967448266577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15413069844095826390755077 2889950595767967448266577)
                    ·
                      refine ⟨2167462946825975586199933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2889950595767967448266577 2167462946825975586199933)
                      ·
                        rfl

theorem cell23_4221119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 4, 2].length) (baseStart_4221119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221119 prefixEnd_4221119 := by exact prefixLift 4221119
  have htrace : WordTrace (prefixWord ++ tailWord_4221119) baseStart_4221119 baseEnd_4221119 := by
    simpa [prefixWord, tailWord_4221119, baseEnd_4221119] using wordTrace_append hprefix tailTrace_4221119
  have hstable : (prefixWord ++ tailWord_4221119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221119).length < 2 ^ (prefixWord ++ tailWord_4221119).sum := by decide
  have hdescent : baseEnd_4221119 < baseStart_4221119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221219 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 6, 4]
def baseStart_4221219 : Nat := 118140960795 + 4221219 * 2 ^ 59
def prefixEnd_4221219 : Nat := 4983230072969 + 3 ^ 40 * 4221219 * 2
def baseEnd_4221219 : Nat := 722504764963808398316491

theorem tailTrace_4221219 : CollatzResearch.WordTrace tailWord_4221219 prefixEnd_4221219 722504764963808398316491 := by
  unfold tailWord_4221219
  simp only [CollatzResearch.WordTrace]
  refine ⟨153960505294251964654394711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102640336862834643102929807 153960505294251964654394711)
  ·
    refine ⟨230940757941377946981592067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153960505294251964654394711 230940757941377946981592067)
    ·
      refine ⟨346411136912066920472388101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230940757941377946981592067 346411136912066920472388101)
      ·
        refine ⟨64952088171012547588572769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 346411136912066920472388101 64952088171012547588572769)
        ·
          refine ⟨48714066128259410691429577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64952088171012547588572769 48714066128259410691429577)
          ·
            refine ⟨36535549596194558018572183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48714066128259410691429577 36535549596194558018572183)
            ·
              refine ⟨54803324394291837027858275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36535549596194558018572183 54803324394291837027858275)
              ·
                refine ⟨82204986591437755541787413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54803324394291837027858275 82204986591437755541787413)
                ·
                  refine ⟨3853358746473644791021285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82204986591437755541787413 3853358746473644791021285)
                  ·
                    refine ⟨722504764963808398316491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3853358746473644791021285 722504764963808398316491)
                    ·
                      rfl

theorem cell23_4221219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 4].length) (baseStart_4221219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221219 prefixEnd_4221219 := by exact prefixLift 4221219
  have htrace : WordTrace (prefixWord ++ tailWord_4221219) baseStart_4221219 baseEnd_4221219 := by
    simpa [prefixWord, tailWord_4221219, baseEnd_4221219] using wordTrace_append hprefix tailTrace_4221219
  have hstable : (prefixWord ++ tailWord_4221219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221219).length < 2 ^ (prefixWord ++ tailWord_4221219).sum := by decide
  have hdescent : baseEnd_4221219 < baseStart_4221219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221220 : List Nat := [2, 3, 1, 3, 1, 2, 3, 3, 1, 1, 3]
def baseStart_4221220 : Nat := 118140960795 + 4221220 * 2 ^ 59
def prefixEnd_4221220 : Nat := 4983230072969 + 3 ^ 40 * 4221220 * 2
def baseEnd_4221220 : Nat := 2167514808372079691036969

theorem tailTrace_4221220 : CollatzResearch.WordTrace tailWord_4221220 prefixEnd_4221220 2167514808372079691036969 := by
  unfold tailWord_4221220
  simp only [CollatzResearch.WordTrace]
  refine ⟨76980270883624170912590557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102640361178165561216787409 76980270883624170912590557)
  ·
    refine ⟨28867601581359064092221459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76980270883624170912590557 28867601581359064092221459)
    ·
      refine ⟨43301402372038596138332189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28867601581359064092221459 43301402372038596138332189)
      ·
        refine ⟨16238025889514473551874571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43301402372038596138332189 16238025889514473551874571)
        ·
          refine ⟨24357038834271710327811857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16238025889514473551874571 24357038834271710327811857)
          ·
            refine ⟨18267779125703782745858893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24357038834271710327811857 18267779125703782745858893)
            ·
              refine ⟨6850417172138918529697085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18267779125703782745858893 6850417172138918529697085)
              ·
                refine ⟨2568906439552094448636407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6850417172138918529697085 2568906439552094448636407)
                ·
                  refine ⟨3853359659328141672954611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568906439552094448636407 3853359659328141672954611)
                  ·
                    refine ⟨5780039488992212509431917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3853359659328141672954611 5780039488992212509431917)
                    ·
                      refine ⟨2167514808372079691036969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5780039488992212509431917 2167514808372079691036969)
                      ·
                        rfl

theorem cell23_4221220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_4221220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221220 prefixEnd_4221220 := by exact prefixLift 4221220
  have htrace : WordTrace (prefixWord ++ tailWord_4221220) baseStart_4221220 baseEnd_4221220 := by
    simpa [prefixWord, tailWord_4221220, baseEnd_4221220] using wordTrace_append hprefix tailTrace_4221220
  have hstable : (prefixWord ++ tailWord_4221220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221220).length < 2 ^ (prefixWord ++ tailWord_4221220).sum := by decide
  have hdescent : baseEnd_4221220 < baseStart_4221220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221246 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_4221246 : Nat := 118140960795 + 4221246 * 2 ^ 59
def prefixEnd_4221246 : Nat := 4983230072969 + 3 ^ 40 * 4221246 * 2
def baseEnd_4221246 : Nat := 2167528158869096589311849

theorem tailTrace_4221246 : CollatzResearch.WordTrace tailWord_4221246 prefixEnd_4221246 2167528158869096589311849 := by
  unfold tailWord_4221246
  simp only [CollatzResearch.WordTrace]
  refine ⟨19245186258144268533203449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102640993376769432177085061 19245186258144268533203449)
  ·
    refine ⟨14433889693608201399902587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19245186258144268533203449 14433889693608201399902587)
    ·
      refine ⟨21650834540412302099853881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14433889693608201399902587 21650834540412302099853881)
      ·
        refine ⟨16238125905309226574890411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21650834540412302099853881 16238125905309226574890411)
        ·
          refine ⟨24357188857963839862335617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16238125905309226574890411 24357188857963839862335617)
          ·
            refine ⟨18267891643472879896751713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24357188857963839862335617 18267891643472879896751713)
            ·
              refine ⟨13700918732604659922563785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18267891643472879896751713 13700918732604659922563785)
              ·
                refine ⟨10275689049453494941922839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13700918732604659922563785 10275689049453494941922839)
                ·
                  refine ⟨15413533574180242412884259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10275689049453494941922839 15413533574180242412884259)
                  ·
                    refine ⟨23120300361270363619326389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15413533574180242412884259 23120300361270363619326389)
                    ·
                      refine ⟨2167528158869096589311849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23120300361270363619326389 2167528158869096589311849)
                      ·
                        rfl

theorem cell23_4221246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_4221246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221246 prefixEnd_4221246 := by exact prefixLift 4221246
  have htrace : WordTrace (prefixWord ++ tailWord_4221246) baseStart_4221246 baseEnd_4221246 := by
    simpa [prefixWord, tailWord_4221246, baseEnd_4221246] using wordTrace_append hprefix tailTrace_4221246
  have hstable : (prefixWord ++ tailWord_4221246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221246).length < 2 ^ (prefixWord ++ tailWord_4221246).sum := by decide
  have hdescent : baseEnd_4221246 < baseStart_4221246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221280 : List Nat := [2, 1, 1, 3, 5, 1, 3, 1, 1, 2, 3]
def baseStart_4221280 : Nat := 118140960795 + 4221280 * 2 ^ 59
def prefixEnd_4221280 : Nat := 4983230072969 + 3 ^ 40 * 4221280 * 2
def baseEnd_4221280 : Nat := 2167545617211349456286693

theorem tailTrace_4221280 : CollatzResearch.WordTrace tailWord_4221280 prefixEnd_4221280 2167545617211349456286693 := by
  unfold tailWord_4221280
  simp only [CollatzResearch.WordTrace]
  refine ⟨76981365073515486036182647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102641820098020648048243529 76981365073515486036182647)
  ·
    refine ⟨115472047610273229054273971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76981365073515486036182647 115472047610273229054273971)
    ·
      refine ⟨173208071415409843581410957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115472047610273229054273971 173208071415409843581410957)
      ·
        refine ⟨64953026780778691343029109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173208071415409843581410957 64953026780778691343029109)
        ·
          refine ⟨6089346260698002313408979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64953026780778691343029109 6089346260698002313408979)
          ·
            refine ⟨9134019391047003470113469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6089346260698002313408979 9134019391047003470113469)
            ·
              refine ⟨3425257271642626301292551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9134019391047003470113469 3425257271642626301292551)
              ·
                refine ⟨5137885907463939451938827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3425257271642626301292551 5137885907463939451938827)
                ·
                  refine ⟨7706828861195909177908241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5137885907463939451938827 7706828861195909177908241)
                  ·
                    refine ⟨5780121645896931883431181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7706828861195909177908241 5780121645896931883431181)
                    ·
                      refine ⟨2167545617211349456286693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5780121645896931883431181 2167545617211349456286693)
                      ·
                        rfl

theorem cell23_4221280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_4221280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221280 prefixEnd_4221280 := by exact prefixLift 4221280
  have htrace : WordTrace (prefixWord ++ tailWord_4221280) baseStart_4221280 baseEnd_4221280 := by
    simpa [prefixWord, tailWord_4221280, baseEnd_4221280] using wordTrace_append hprefix tailTrace_4221280
  have hstable : (prefixWord ++ tailWord_4221280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221280).length < 2 ^ (prefixWord ++ tailWord_4221280).sum := by decide
  have hdescent : baseEnd_4221280 < baseStart_4221280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221309 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_4221309 : Nat := 118140960795 + 4221309 * 2 ^ 59
def prefixEnd_4221309 : Nat := 4983230072969 + 3 ^ 40 * 4221309 * 2
def baseEnd_4221309 : Nat := 722520169383443280941353

theorem tailTrace_4221309 : CollatzResearch.WordTrace tailWord_4221309 prefixEnd_4221309 722520169383443280941353 := by
  unfold tailWord_4221309
  simp only [CollatzResearch.WordTrace]
  refine ⟨153963787863925910025170981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102642525242617273350113987 153963787863925910025170981)
  ·
    refine ⟨28868210224486108129719559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153963787863925910025170981 28868210224486108129719559)
    ·
      refine ⟨43302315336729162194579339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28868210224486108129719559 43302315336729162194579339)
      ·
        refine ⟨64953473005093743291869009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43302315336729162194579339 64953473005093743291869009)
        ·
          refine ⟨48715104753820307468901757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64953473005093743291869009 48715104753820307468901757)
          ·
            refine ⟨18268164282682615300838159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48715104753820307468901757 18268164282682615300838159)
            ·
              refine ⟨27402246424023922951257239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18268164282682615300838159 27402246424023922951257239)
              ·
                refine ⟨41103369636035884426885859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27402246424023922951257239 41103369636035884426885859)
                ·
                  refine ⟨61655054454053826640328789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41103369636035884426885859 61655054454053826640328789)
                  ·
                    refine ⟨722520169383443280941353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61655054454053826640328789 722520169383443280941353)
                    ·
                      rfl

theorem cell23_4221309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_4221309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221309 prefixEnd_4221309 := by exact prefixLift 4221309
  have htrace : WordTrace (prefixWord ++ tailWord_4221309) baseStart_4221309 baseEnd_4221309 := by
    simpa [prefixWord, tailWord_4221309, baseEnd_4221309] using wordTrace_append hprefix tailTrace_4221309
  have hstable : (prefixWord ++ tailWord_4221309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221309).length < 2 ^ (prefixWord ++ tailWord_4221309).sum := by decide
  have hdescent : baseEnd_4221309 < baseStart_4221309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221329 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_4221329 : Nat := 118140960795 + 4221329 * 2 ^ 59
def prefixEnd_4221329 : Nat := 4983230072969 + 3 ^ 40 * 4221329 * 2
def baseEnd_4221329 : Nat := 2167570777763419764573967

theorem tailTrace_4221329 : CollatzResearch.WordTrace tailWord_4221329 prefixEnd_4221329 2167570777763419764573967 := by
  unfold tailWord_4221329
  simp only [CollatzResearch.WordTrace]
  refine ⟨153964517323853453440899041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102643011549235635627266027 153964517323853453440899041)
  ·
    refine ⟨115473387992890090080674281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153964517323853453440899041 115473387992890090080674281)
    ·
      refine ⟨86605040994667567560505711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115473387992890090080674281 86605040994667567560505711)
      ·
        refine ⟨129907561492001351340758567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86605040994667567560505711 129907561492001351340758567)
        ·
          refine ⟨194861342238002027011137851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129907561492001351340758567 194861342238002027011137851)
          ·
            refine ⟨292292013357003040516706777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194861342238002027011137851 292292013357003040516706777)
            ·
              refine ⟨219219010017752280387530083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292292013357003040516706777 219219010017752280387530083)
              ·
                refine ⟨328828515026628420581295125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219219010017752280387530083 328828515026628420581295125)
                ·
                  refine ⟨15413836641873207214748209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 328828515026628420581295125 15413836641873207214748209)
                  ·
                    refine ⟨11560377481404905411061157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15413836641873207214748209 11560377481404905411061157)
                    ·
                      refine ⟨2167570777763419764573967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11560377481404905411061157 2167570777763419764573967)
                      ·
                        rfl

theorem cell23_4221329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_4221329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221329 prefixEnd_4221329 := by exact prefixLift 4221329
  have htrace : WordTrace (prefixWord ++ tailWord_4221329) baseStart_4221329 baseEnd_4221329 := by
    simpa [prefixWord, tailWord_4221329, baseEnd_4221329] using wordTrace_append hprefix tailTrace_4221329
  have hstable : (prefixWord ++ tailWord_4221329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221329).length < 2 ^ (prefixWord ++ tailWord_4221329).sum := by decide
  have hdescent : baseEnd_4221329 < baseStart_4221329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221333 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 4, 2, 2]
def baseStart_4221333 : Nat := 118140960795 + 4221333 * 2 ^ 59
def prefixEnd_4221333 : Nat := 4983230072969 + 3 ^ 40 * 4221333 * 2
def baseEnd_4221333 : Nat := 2167572831686037748923949

theorem tailTrace_4221333 : CollatzResearch.WordTrace tailWord_4221333 prefixEnd_4221333 2167572831686037748923949 := by
  unfold tailWord_4221333
  simp only [CollatzResearch.WordTrace]
  refine ⟨153964663215838962124044653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102643108810559308082696435 153964663215838962124044653)
  ·
    refine ⟨57736748705939610796516745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153964663215838962124044653 57736748705939610796516745)
    ·
      refine ⟨43302561529454708097387559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57736748705939610796516745 43302561529454708097387559)
      ·
        refine ⟨64953842294182062146081339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43302561529454708097387559 64953842294182062146081339)
        ·
          refine ⟨97430763441273093219122009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64953842294182062146081339 97430763441273093219122009)
          ·
            refine ⟨73073072580954819914341507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97430763441273093219122009 73073072580954819914341507)
            ·
              refine ⟨109609608871432229871512261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73073072580954819914341507 109609608871432229871512261)
              ·
                refine ⟨20551801663393543100908549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109609608871432229871512261 20551801663393543100908549)
                ·
                  refine ⟨3853462811886289331420353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20551801663393543100908549 3853462811886289331420353)
                  ·
                    refine ⟨2890097108914716998565265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3853462811886289331420353 2890097108914716998565265)
                    ·
                      refine ⟨2167572831686037748923949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2890097108914716998565265 2167572831686037748923949)
                      ·
                        rfl

theorem cell23_4221333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_4221333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221333 prefixEnd_4221333 := by exact prefixLift 4221333
  have htrace : WordTrace (prefixWord ++ tailWord_4221333) baseStart_4221333 baseEnd_4221333 := by
    simpa [prefixWord, tailWord_4221333, baseEnd_4221333] using wordTrace_append hprefix tailTrace_4221333
  have hstable : (prefixWord ++ tailWord_4221333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221333).length < 2 ^ (prefixWord ++ tailWord_4221333).sum := by decide
  have hdescent : baseEnd_4221333 < baseStart_4221333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221346 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_4221346 : Nat := 118140960795 + 4221346 * 2 ^ 59
def prefixEnd_4221346 : Nat := 4983230072969 + 3 ^ 40 * 4221346 * 2
def baseEnd_4221346 : Nat := 2167579506934546198061389

theorem tailTrace_4221346 : CollatzResearch.WordTrace tailWord_4221346 prefixEnd_4221346 2167579506934546198061389 := by
  unfold tailWord_4221346
  simp only [CollatzResearch.WordTrace]
  refine ⟨38491284341197966336066973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102643424909861243562845261 38491284341197966336066973)
  ·
    refine ⟨14434231627949237376025115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38491284341197966336066973 14434231627949237376025115)
    ·
      refine ⟨21651347441923856064037673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14434231627949237376025115 21651347441923856064037673)
      ·
        refine ⟨16238510581442892048028255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21651347441923856064037673 16238510581442892048028255)
        ·
          refine ⟨24357765872164338072042383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16238510581442892048028255 24357765872164338072042383)
          ·
            refine ⟨36536648808246507108063575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24357765872164338072042383 36536648808246507108063575)
            ·
              refine ⟨54804973212369760662095363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36536648808246507108063575 54804973212369760662095363)
              ·
                refine ⟨82207459818554640993143045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54804973212369760662095363 82207459818554640993143045)
                ·
                  refine ⟨15413898715978995186214321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82207459818554640993143045 15413898715978995186214321)
                  ·
                    refine ⟨11560424036984246389660741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15413898715978995186214321 11560424036984246389660741)
                    ·
                      refine ⟨2167579506934546198061389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11560424036984246389660741 2167579506934546198061389)
                      ·
                        rfl

theorem cell23_4221346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_4221346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221346 prefixEnd_4221346 := by exact prefixLift 4221346
  have htrace : WordTrace (prefixWord ++ tailWord_4221346) baseStart_4221346 baseEnd_4221346 := by
    simpa [prefixWord, tailWord_4221346, baseEnd_4221346] using wordTrace_append hprefix tailTrace_4221346
  have hstable : (prefixWord ++ tailWord_4221346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221346).length < 2 ^ (prefixWord ++ tailWord_4221346).sum := by decide
  have hdescent : baseEnd_4221346 < baseStart_4221346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221367 : List Nat := [1, 1, 3, 1, 3, 4, 3, 1, 2, 2, 2]
def baseStart_4221367 : Nat := 118140960795 + 4221367 * 2 ^ 59
def prefixEnd_4221367 : Nat := 4983230072969 + 3 ^ 40 * 4221367 * 2
def baseEnd_4221367 : Nat := 2167590290028290615898793

theorem tailTrace_4221367 : CollatzResearch.WordTrace tailWord_4221367 prefixEnd_4221367 2167590290028290615898793 := by
  unfold tailWord_4221367
  simp only [CollatzResearch.WordTrace]
  refine ⟨153965903297715785930782355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102643935531810523953854903 153965903297715785930782355)
  ·
    refine ⟨230948854946573678896173533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153965903297715785930782355 230948854946573678896173533)
    ·
      refine ⟨86605820604965129586065075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230948854946573678896173533 86605820604965129586065075)
      ·
        refine ⟨129908730907447694379097613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86605820604965129586065075 129908730907447694379097613)
        ·
          refine ⟨48715774090292885392161605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129908730907447694379097613 48715774090292885392161605)
          ·
            refine ⟨9134207641929916011030301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48715774090292885392161605 9134207641929916011030301)
            ·
              refine ⟨3425327865723718504136363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9134207641929916011030301 3425327865723718504136363)
              ·
                refine ⟨5137991798585577756204545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3425327865723718504136363 5137991798585577756204545)
                ·
                  refine ⟨3853493848939183317153409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5137991798585577756204545 3853493848939183317153409)
                  ·
                    refine ⟨2890120386704387487865057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3853493848939183317153409 2890120386704387487865057)
                    ·
                      refine ⟨2167590290028290615898793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2890120386704387487865057 2167590290028290615898793)
                      ·
                        rfl

theorem cell23_4221367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 2, 2, 2].length) (baseStart_4221367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221367 prefixEnd_4221367 := by exact prefixLift 4221367
  have htrace : WordTrace (prefixWord ++ tailWord_4221367) baseStart_4221367 baseEnd_4221367 := by
    simpa [prefixWord, tailWord_4221367, baseEnd_4221367] using wordTrace_append hprefix tailTrace_4221367
  have hstable : (prefixWord ++ tailWord_4221367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221367).length < 2 ^ (prefixWord ++ tailWord_4221367).sum := by decide
  have hdescent : baseEnd_4221367 < baseStart_4221367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221379 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 5]
def baseStart_4221379 : Nat := 118140960795 + 4221379 * 2 ^ 59
def prefixEnd_4221379 : Nat := 4983230072969 + 3 ^ 40 * 4221379 * 2
def baseEnd_4221379 : Nat := 2167596451796144568948737

theorem tailTrace_4221379 : CollatzResearch.WordTrace tailWord_4221379 prefixEnd_4221379 2167596451796144568948737 := by
  unfold tailWord_4221379
  simp only [CollatzResearch.WordTrace]
  refine ⟨153966340973672311980219191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102644227315781541320146127 153966340973672311980219191)
  ·
    refine ⟨230949511460508467970328787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153966340973672311980219191 230949511460508467970328787)
    ·
      refine ⟨346424267190762701955493181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230949511460508467970328787 346424267190762701955493181)
      ·
        refine ⟨129909100196536013233309943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346424267190762701955493181 129909100196536013233309943)
        ·
          refine ⟨194863650294804019849964915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129909100196536013233309943 194863650294804019849964915)
          ·
            refine ⟨292295475442206029774947373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194863650294804019849964915 292295475442206029774947373)
            ·
              refine ⟨109610803290827261165605265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 292295475442206029774947373 109610803290827261165605265)
              ·
                refine ⟨82208102468120445874203949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109610803290827261165605265 82208102468120445874203949)
                ·
                  refine ⟨30828038425545167202826481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82208102468120445874203949 30828038425545167202826481)
                  ·
                    refine ⟨23121028819158875402119861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30828038425545167202826481 23121028819158875402119861)
                    ·
                      refine ⟨2167596451796144568948737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23121028819158875402119861 2167596451796144568948737)
                      ·
                        rfl

theorem cell23_4221379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_4221379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221379 prefixEnd_4221379 := by exact prefixLift 4221379
  have htrace : WordTrace (prefixWord ++ tailWord_4221379) baseStart_4221379 baseEnd_4221379 := by
    simpa [prefixWord, tailWord_4221379, baseEnd_4221379] using wordTrace_append hprefix tailTrace_4221379
  have hstable : (prefixWord ++ tailWord_4221379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221379).length < 2 ^ (prefixWord ++ tailWord_4221379).sum := by decide
  have hdescent : baseEnd_4221379 < baseStart_4221379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221386 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 2, 5]
def baseStart_4221386 : Nat := 118140960795 + 4221386 * 2 ^ 59
def prefixEnd_4221386 : Nat := 4983230072969 + 3 ^ 40 * 4221386 * 2
def baseEnd_4221386 : Nat := 722533348720242013853735

theorem tailTrace_4221386 : CollatzResearch.WordTrace tailWord_4221386 prefixEnd_4221386 722533348720242013853735 := by
  unfold tailWord_4221386
  simp only [CollatzResearch.WordTrace]
  refine ⟨38491649071161738043931003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102644397523097968117149341 38491649071161738043931003)
  ·
    refine ⟨57737473606742607065896505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38491649071161738043931003 57737473606742607065896505)
    ·
      refine ⟨43303105205056955299422379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57737473606742607065896505 43303105205056955299422379)
      ·
        refine ⟨64954657807585432949133569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43303105205056955299422379 64954657807585432949133569)
        ·
          refine ⟨48715993355689074711850177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64954657807585432949133569 48715993355689074711850177)
          ·
            refine ⟨36536995016766806033887633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48715993355689074711850177 36536995016766806033887633)
            ·
              refine ⟨27402746262575104525415725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36536995016766806033887633 27402746262575104525415725)
              ·
                refine ⟨10276029848465664197030897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27402746262575104525415725 10276029848465664197030897)
                ·
                  refine ⟨7707022386349248147773173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10276029848465664197030897 7707022386349248147773173)
                  ·
                    refine ⟨722533348720242013853735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7707022386349248147773173 722533348720242013853735)
                    ·
                      rfl

theorem cell23_4221386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_4221386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221386 prefixEnd_4221386 := by exact prefixLift 4221386
  have htrace : WordTrace (prefixWord ++ tailWord_4221386) baseStart_4221386 baseEnd_4221386 := by
    simpa [prefixWord, tailWord_4221386, baseEnd_4221386] using wordTrace_append hprefix tailTrace_4221386
  have hstable : (prefixWord ++ tailWord_4221386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221386).length < 2 ^ (prefixWord ++ tailWord_4221386).sum := by decide
  have hdescent : baseEnd_4221386 < baseStart_4221386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221413 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 1, 2, 5]
def baseStart_4221413 : Nat := 118140960795 + 4221413 * 2 ^ 59
def prefixEnd_4221413 : Nat := 4983230072969 + 3 ^ 40 * 4221413 * 2
def baseEnd_4221413 : Nat := 2167613910138397435923581

theorem tailTrace_4221413 : CollatzResearch.WordTrace tailWord_4221413 prefixEnd_4221413 2167613910138397435923581 := by
  unfold tailWord_4221413
  simp only [CollatzResearch.WordTrace]
  refine ⟨153967581055549135786956893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102645054037032757191304595 153967581055549135786956893)
  ·
    refine ⟨57737842895830925920108835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153967581055549135786956893 57737842895830925920108835)
    ·
      refine ⟨86606764343746388880163253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57737842895830925920108835 86606764343746388880163253)
      ·
        refine ⟨8119384157226223957515305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86606764343746388880163253 8119384157226223957515305)
        ·
          refine ⟨6089538117919667968136479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8119384157226223957515305 6089538117919667968136479)
          ·
            refine ⟨9134307176879501952204719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6089538117919667968136479 9134307176879501952204719)
            ·
              refine ⟨13701460765319252928307079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9134307176879501952204719 13701460765319252928307079)
              ·
                refine ⟨20552191147978879392460619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13701460765319252928307079 20552191147978879392460619)
                ·
                  refine ⟨30828286721968319088690929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20552191147978879392460619 30828286721968319088690929)
                  ·
                    refine ⟨23121215041476239316518197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30828286721968319088690929 23121215041476239316518197)
                    ·
                      refine ⟨2167613910138397435923581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23121215041476239316518197 2167613910138397435923581)
                      ·
                        rfl

theorem cell23_4221413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_4221413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221413 prefixEnd_4221413 := by exact prefixLift 4221413
  have htrace : WordTrace (prefixWord ++ tailWord_4221413) baseStart_4221413 baseEnd_4221413 := by
    simpa [prefixWord, tailWord_4221413, baseEnd_4221413] using wordTrace_append hprefix tailTrace_4221413
  have hstable : (prefixWord ++ tailWord_4221413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221413).length < 2 ^ (prefixWord ++ tailWord_4221413).sum := by decide
  have hdescent : baseEnd_4221413 < baseStart_4221413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221443 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 3]
def baseStart_4221443 : Nat := 118140960795 + 4221443 * 2 ^ 59
def prefixEnd_4221443 : Nat := 4983230072969 + 3 ^ 40 * 4221443 * 2
def baseEnd_4221443 : Nat := 2167629314558032318548443

theorem tailTrace_4221443 : CollatzResearch.WordTrace tailWord_4221443 prefixEnd_4221443 2167629314558032318548443 := by
  unfold tailWord_4221443
  simp only [CollatzResearch.WordTrace]
  refine ⟨153968675245440450910548983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102645783496960300607032655 153968675245440450910548983)
  ·
    refine ⟨230953012868160676365823475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153968675245440450910548983 230953012868160676365823475)
    ·
      refine ⟨346429519302241014548735213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230953012868160676365823475 346429519302241014548735213)
      ·
        refine ⟨129911069738340380455775705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346429519302241014548735213 129911069738340380455775705)
        ·
          refine ⟨97433302303755285341831779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129911069738340380455775705 97433302303755285341831779)
          ·
            refine ⟨146149953455632928012747669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97433302303755285341831779 146149953455632928012747669)
            ·
              refine ⟨6850779068232793500597547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 146149953455632928012747669 6850779068232793500597547)
              ·
                refine ⟨10276168602349190250896321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6850779068232793500597547 10276168602349190250896321)
                ·
                  refine ⟨7707126451761892688172241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10276168602349190250896321 7707126451761892688172241)
                  ·
                    refine ⟨5780344838821419516129181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7707126451761892688172241 5780344838821419516129181)
                    ·
                      refine ⟨2167629314558032318548443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5780344838821419516129181 2167629314558032318548443)
                      ·
                        rfl

theorem cell23_4221443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_4221443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221443 prefixEnd_4221443 := by exact prefixLift 4221443
  have htrace : WordTrace (prefixWord ++ tailWord_4221443) baseStart_4221443 baseEnd_4221443 := by
    simpa [prefixWord, tailWord_4221443, baseEnd_4221443] using wordTrace_append hprefix tailTrace_4221443
  have hstable : (prefixWord ++ tailWord_4221443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221443).length < 2 ^ (prefixWord ++ tailWord_4221443).sum := by decide
  have hdescent : baseEnd_4221443 < baseStart_4221443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221450 : List Nat := [3, 1, 2, 2, 2, 1, 2, 5, 1, 4]
def baseStart_4221450 : Nat := 118140960795 + 4221450 * 2 ^ 59
def prefixEnd_4221450 : Nat := 4983230072969 + 3 ^ 40 * 4221450 * 2
def baseEnd_4221450 : Nat := 722544302974204597053637

theorem tailTrace_4221450 : CollatzResearch.WordTrace tailWord_4221450 prefixEnd_4221450 722544302974204597053637 := by
  unfold tailWord_4221450
  simp only [CollatzResearch.WordTrace]
  refine ⟨38492232639103772776513451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102645953704276727404035869 38492232639103772776513451)
  ·
    refine ⟨57738348958655659164770177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38492232639103772776513451 57738348958655659164770177)
    ·
      refine ⟨43303761718991744373577633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57738348958655659164770177 43303761718991744373577633)
      ·
        refine ⟨32477821289243808280183225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43303761718991744373577633 32477821289243808280183225)
        ·
          refine ⟨24358365966932856210137419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32477821289243808280183225 24358365966932856210137419)
          ·
            refine ⟨36537548950399284315206129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24358365966932856210137419 36537548950399284315206129)
            ·
              refine ⟨27403161712799463236404597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36537548950399284315206129 27403161712799463236404597)
              ·
                refine ⟨2569046410574949678412931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27403161712799463236404597 2569046410574949678412931)
                ·
                  refine ⟨3853569615862424517619397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2569046410574949678412931 3853569615862424517619397)
                  ·
                    refine ⟨722544302974204597053637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3853569615862424517619397 722544302974204597053637)
                    ·
                      rfl

theorem cell23_4221450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_4221450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221450 prefixEnd_4221450 := by exact prefixLift 4221450
  have htrace : WordTrace (prefixWord ++ tailWord_4221450) baseStart_4221450 baseEnd_4221450 := by
    simpa [prefixWord, tailWord_4221450, baseEnd_4221450] using wordTrace_append hprefix tailTrace_4221450
  have hstable : (prefixWord ++ tailWord_4221450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221450).length < 2 ^ (prefixWord ++ tailWord_4221450).sum := by decide
  have hdescent : baseEnd_4221450 < baseStart_4221450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221483 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 4, 3, 2]
def baseStart_4221483 : Nat := 118140960795 + 4221483 * 2 ^ 59
def prefixEnd_4221483 : Nat := 4983230072969 + 3 ^ 40 * 4221483 * 2
def baseEnd_4221483 : Nat := 2167649853784212162048259

theorem tailTrace_4221483 : CollatzResearch.WordTrace tailWord_4221483 prefixEnd_4221483 2167649853784212162048259 := by
  unfold tailWord_4221483
  simp only [CollatzResearch.WordTrace]
  refine ⟨153970134165295537742005103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102646756110197025161336735 153970134165295537742005103)
  ·
    refine ⟨230955201247943306613007655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153970134165295537742005103 230955201247943306613007655)
    ·
      refine ⟨346432801871914959919511483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230955201247943306613007655 346432801871914959919511483)
      ·
        refine ⟨519649202807872439879267225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346432801871914959919511483 519649202807872439879267225)
        ·
          refine ⟨389736902105904329909450419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 519649202807872439879267225 389736902105904329909450419)
          ·
            refine ⟨584605353158856494864175629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389736902105904329909450419 584605353158856494864175629)
            ·
              refine ⟨219227007434571185574065861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 584605353158856494864175629 219227007434571185574065861)
              ·
                refine ⟨41105063893982097295137349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 219227007434571185574065861 41105063893982097295137349)
                ·
                  refine ⟨7707199480121643242838253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41105063893982097295137349 7707199480121643242838253)
                  ·
                    refine ⟨2890199805045616216064345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7707199480121643242838253 2890199805045616216064345)
                    ·
                      refine ⟨2167649853784212162048259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2890199805045616216064345 2167649853784212162048259)
                      ·
                        rfl

theorem cell23_4221483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 3, 2].length) (baseStart_4221483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221483 prefixEnd_4221483 := by exact prefixLift 4221483
  have htrace : WordTrace (prefixWord ++ tailWord_4221483) baseStart_4221483 baseEnd_4221483 := by
    simpa [prefixWord, tailWord_4221483, baseEnd_4221483] using wordTrace_append hprefix tailTrace_4221483
  have hstable : (prefixWord ++ tailWord_4221483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221483).length < 2 ^ (prefixWord ++ tailWord_4221483).sum := by decide
  have hdescent : baseEnd_4221483 < baseStart_4221483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221493 : List Nat := [1, 3, 3, 1, 1, 2, 2, 4, 1, 5]
def baseStart_4221493 : Nat := 118140960795 + 4221493 * 2 ^ 59
def prefixEnd_4221493 : Nat := 4983230072969 + 3 ^ 40 * 4221493 * 2
def baseEnd_4221493 : Nat := 722551662863585707641071

theorem tailTrace_4221493 : CollatzResearch.WordTrace tailWord_4221493 prefixEnd_4221493 722551662863585707641071 := by
  unfold tailWord_4221493
  simp only [CollatzResearch.WordTrace]
  refine ⟨153970498895259309449869133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102646999263506206299912755 153970498895259309449869133)
  ·
    refine ⟨57738937085722241043700925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153970498895259309449869133 57738937085722241043700925)
    ·
      refine ⟨21652101407145840391387847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57738937085722241043700925 21652101407145840391387847)
      ·
        refine ⟨32478152110718760587081771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21652101407145840391387847 32478152110718760587081771)
        ·
          refine ⟨48717228166078140880622657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32478152110718760587081771 48717228166078140880622657)
          ·
            refine ⟨36537921124558605660466993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48717228166078140880622657 36537921124558605660466993)
            ·
              refine ⟨27403440843418954245350245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36537921124558605660466993 27403440843418954245350245)
              ·
                refine ⟨5138145158141053921003171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27403440843418954245350245 5138145158141053921003171)
                ·
                  refine ⟨7707217737211580881504757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5138145158141053921003171 7707217737211580881504757)
                  ·
                    refine ⟨722551662863585707641071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7707217737211580881504757 722551662863585707641071)
                    ·
                      rfl

theorem cell23_4221493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_4221493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221493 prefixEnd_4221493 := by exact prefixLift 4221493
  have htrace : WordTrace (prefixWord ++ tailWord_4221493) baseStart_4221493 baseEnd_4221493 := by
    simpa [prefixWord, tailWord_4221493, baseEnd_4221493] using wordTrace_append hprefix tailTrace_4221493
  have hstable : (prefixWord ++ tailWord_4221493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221493).length < 2 ^ (prefixWord ++ tailWord_4221493).sum := by decide
  have hdescent : baseEnd_4221493 < baseStart_4221493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221500 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 1, 5, 2]
def baseStart_4221500 : Nat := 118140960795 + 4221500 * 2 ^ 59
def prefixEnd_4221500 : Nat := 4983230072969 + 3 ^ 40 * 4221500 * 2
def baseEnd_4221500 : Nat := 2167658582955338595535681

theorem tailTrace_4221500 : CollatzResearch.WordTrace tailWord_4221500 prefixEnd_4221500 2167658582955338595535681 := by
  unfold tailWord_4221500
  simp only [CollatzResearch.WordTrace]
  refine ⟨76985377103116974822686977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102647169470822633096915969 76985377103116974822686977)
  ·
    refine ⟨57739032827337731117015233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76985377103116974822686977 57739032827337731117015233)
    ·
      refine ⟨43304274620503298337761425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57739032827337731117015233 43304274620503298337761425)
      ·
        refine ⟨32478205965377473753321069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43304274620503298337761425 32478205965377473753321069)
        ·
          refine ⟨12179327237016552657495401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32478205965377473753321069 12179327237016552657495401)
          ·
            refine ⟨9134495427762414493121551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12179327237016552657495401 9134495427762414493121551)
            ·
              refine ⟨13701743141643621739682327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9134495427762414493121551 13701743141643621739682327)
              ·
                refine ⟨20552614712465432609523491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13701743141643621739682327 20552614712465432609523491)
                ·
                  refine ⟨30828922068698148914285237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20552614712465432609523491 30828922068698148914285237)
                  ·
                    refine ⟨2890211443940451460714241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30828922068698148914285237 2890211443940451460714241)
                    ·
                      refine ⟨2167658582955338595535681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2890211443940451460714241 2167658582955338595535681)
                      ·
                        rfl

theorem cell23_4221500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_4221500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221500 prefixEnd_4221500 := by exact prefixLift 4221500
  have htrace : WordTrace (prefixWord ++ tailWord_4221500) baseStart_4221500 baseEnd_4221500 := by
    simpa [prefixWord, tailWord_4221500, baseEnd_4221500] using wordTrace_append hprefix tailTrace_4221500
  have hstable : (prefixWord ++ tailWord_4221500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221500).length < 2 ^ (prefixWord ++ tailWord_4221500).sum := by decide
  have hdescent : baseEnd_4221500 < baseStart_4221500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221558 : List Nat := [5, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3]
def baseStart_4221558 : Nat := 118140960795 + 4221558 * 2 ^ 59
def prefixEnd_4221558 : Nat := 4983230072969 + 3 ^ 40 * 4221558 * 2
def baseEnd_4221558 : Nat := 2167688364833299368610415

theorem tailTrace_4221558 : CollatzResearch.WordTrace tailWord_4221558 prefixEnd_4221558 2167688364833299368610415 := by
  unfold tailWord_4221558
  simp only [CollatzResearch.WordTrace]
  refine ⟨9623304352501489096936583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102648579760015883700656885 9623304352501489096936583)
  ·
    refine ⟨14434956528752233645404875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9623304352501489096936583 14434956528752233645404875)
    ·
      refine ⟨21652434793128350468107313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14434956528752233645404875 21652434793128350468107313)
      ·
        refine ⟨16239326094846262851080485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21652434793128350468107313 16239326094846262851080485)
        ·
          refine ⟨3044873642783674284577591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16239326094846262851080485 3044873642783674284577591)
          ·
            refine ⟨4567310464175511426866387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3044873642783674284577591 4567310464175511426866387)
            ·
              refine ⟨6850965696263267140299581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4567310464175511426866387 6850965696263267140299581)
              ·
                refine ⟨2569112136098725177612343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6850965696263267140299581 2569112136098725177612343)
                ·
                  refine ⟨3853668204148087766418515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2569112136098725177612343 3853668204148087766418515)
                  ·
                    refine ⟨5780502306222131649627773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3853668204148087766418515 5780502306222131649627773)
                    ·
                      refine ⟨2167688364833299368610415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5780502306222131649627773 2167688364833299368610415)
                      ·
                        rfl

theorem cell23_4221558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_4221558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221558 prefixEnd_4221558 := by exact prefixLift 4221558
  have htrace : WordTrace (prefixWord ++ tailWord_4221558) baseStart_4221558 baseEnd_4221558 := by
    simpa [prefixWord, tailWord_4221558, baseEnd_4221558] using wordTrace_append hprefix tailTrace_4221558
  have hstable : (prefixWord ++ tailWord_4221558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221558).length < 2 ^ (prefixWord ++ tailWord_4221558).sum := by decide
  have hdescent : baseEnd_4221558 < baseStart_4221558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221564 : List Nat := [2, 2, 2, 1, 1, 2, 5, 3, 1, 2, 2]
def baseStart_4221564 : Nat := 118140960795 + 4221564 * 2 ^ 59
def prefixEnd_4221564 : Nat := 4983230072969 + 3 ^ 40 * 4221564 * 2
def baseEnd_4221564 : Nat := 2167691445717226345135387

theorem tailTrace_4221564 : CollatzResearch.WordTrace tailWord_4221564 prefixEnd_4221564 2167691445717226345135387 := by
  unfold tailWord_4221564
  simp only [CollatzResearch.WordTrace]
  refine ⟨76986544239001044287851873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102648725652001392383802497 76986544239001044287851873)
  ·
    refine ⟨57739908179250783215888905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76986544239001044287851873 57739908179250783215888905)
    ·
      refine ⟨43304931134438087411916679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57739908179250783215888905 43304931134438087411916679)
      ·
        refine ⟨64957396701657131117875019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43304931134438087411916679 64957396701657131117875019)
        ·
          refine ⟨97436095052485696676812529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64957396701657131117875019 97436095052485696676812529)
          ·
            refine ⟨73077071289364272507609397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97436095052485696676812529 73077071289364272507609397)
            ·
              refine ⟨6850975433377900547588381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73077071289364272507609397 6850975433377900547588381)
              ·
                refine ⟨2569115787516712705345643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6850975433377900547588381 2569115787516712705345643)
                ·
                  refine ⟨3853673681275069058018465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2569115787516712705345643 3853673681275069058018465)
                  ·
                    refine ⟨2890255260956301793513849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3853673681275069058018465 2890255260956301793513849)
                    ·
                      refine ⟨2167691445717226345135387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2890255260956301793513849 2167691445717226345135387)
                      ·
                        rfl

theorem cell23_4221564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_4221564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221564 prefixEnd_4221564 := by exact prefixLift 4221564
  have htrace : WordTrace (prefixWord ++ tailWord_4221564) baseStart_4221564 baseEnd_4221564 := by
    simpa [prefixWord, tailWord_4221564, baseEnd_4221564] using wordTrace_append hprefix tailTrace_4221564
  have hstable : (prefixWord ++ tailWord_4221564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221564).length < 2 ^ (prefixWord ++ tailWord_4221564).sum := by decide
  have hdescent : baseEnd_4221564 < baseStart_4221564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221660 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 9]
def baseStart_4221660 : Nat := 118140960795 + 4221660 * 2 ^ 59
def prefixEnd_4221660 : Nat := 4983230072969 + 3 ^ 40 * 4221660 * 2
def baseEnd_4221660 : Nat := 240860082206673107726105

theorem tailTrace_4221660 : CollatzResearch.WordTrace tailWord_4221660 prefixEnd_4221660 240860082206673107726105 := by
  unfold tailWord_4221660
  simp only [CollatzResearch.WordTrace]
  refine ⟨76988294942827148485599217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102651059923769531314132289 76988294942827148485599217)
  ·
    refine ⟨57741221207120361364199413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76988294942827148485599217 57741221207120361364199413)
    ·
      refine ⟨5413239488167533877893695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57741221207120361364199413 5413239488167533877893695)
      ·
        refine ⟨8119859232251300816840543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5413239488167533877893695 8119859232251300816840543)
        ·
          refine ⟨12179788848376951225260815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8119859232251300816840543 12179788848376951225260815)
          ·
            refine ⟨18269683272565426837891223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12179788848376951225260815 18269683272565426837891223)
            ·
              refine ⟨27404524908848140256836835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18269683272565426837891223 27404524908848140256836835)
              ·
                refine ⟨41106787363272210385255253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27404524908848140256836835 41106787363272210385255253)
                ·
                  refine ⟨240860082206673107726105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41106787363272210385255253 240860082206673107726105)
                  ·
                    rfl

theorem cell23_4221660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 9].length) (baseStart_4221660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221660 prefixEnd_4221660 := by exact prefixLift 4221660
  have htrace : WordTrace (prefixWord ++ tailWord_4221660) baseStart_4221660 baseEnd_4221660 := by
    simpa [prefixWord, tailWord_4221660, baseEnd_4221660] using wordTrace_append hprefix tailTrace_4221660
  have hstable : (prefixWord ++ tailWord_4221660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221660).length < 2 ^ (prefixWord ++ tailWord_4221660).sum := by decide
  have hdescent : baseEnd_4221660 < baseStart_4221660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221677 : List Nat := [1, 5, 1, 2, 1, 1, 4, 3, 5]
def baseStart_4221677 : Nat := 118140960795 + 4221677 * 2 ^ 59
def prefixEnd_4221677 : Nat := 4983230072969 + 3 ^ 40 * 4221677 * 2
def baseEnd_4221677 : Nat := 240861052114576044780263

theorem tailTrace_4221677 : CollatzResearch.WordTrace tailWord_4221677 prefixEnd_4221677 240861052114576044780263 := by
  unfold tailWord_4221677
  simp only [CollatzResearch.WordTrace]
  refine ⟨153977209926592708874567285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102651473284395139249711523 153977209926592708874567285)
  ·
    refine ⟨14435363430618066456990683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153977209926592708874567285 14435363430618066456990683)
    ·
      refine ⟨21653045145927099685486025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14435363430618066456990683 21653045145927099685486025)
      ·
        refine ⟨16239783859445324764114519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21653045145927099685486025 16239783859445324764114519)
        ·
          refine ⟨24359675789167987146171779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16239783859445324764114519 24359675789167987146171779)
          ·
            refine ⟨36539513683751980719257669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24359675789167987146171779 36539513683751980719257669)
            ·
              refine ⟨6851158815703496384860813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36539513683751980719257669 6851158815703496384860813)
              ·
                refine ⟨2569184555888811144322805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6851158815703496384860813 2569184555888811144322805)
                ·
                  refine ⟨240861052114576044780263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2569184555888811144322805 240861052114576044780263)
                  ·
                    rfl

theorem cell23_4221677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_4221677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221677 prefixEnd_4221677 := by exact prefixLift 4221677
  have htrace : WordTrace (prefixWord ++ tailWord_4221677) baseStart_4221677 baseEnd_4221677 := by
    simpa [prefixWord, tailWord_4221677, baseEnd_4221677] using wordTrace_append hprefix tailTrace_4221677
  have hstable : (prefixWord ++ tailWord_4221677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221677).length < 2 ^ (prefixWord ++ tailWord_4221677).sum := by decide
  have hdescent : baseEnd_4221677 < baseStart_4221677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4221733 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 10]
def baseStart_4221733 : Nat := 118140960795 + 4221733 * 2 ^ 59
def prefixEnd_4221733 : Nat := 4983230072969 + 3 ^ 40 * 4221733 * 2
def baseEnd_4221733 : Nat := 240864247105315131546901

theorem tailTrace_4221733 : CollatzResearch.WordTrace tailWord_4221733 prefixEnd_4221733 240864247105315131546901 := by
  unfold tailWord_4221733
  simp only [CollatzResearch.WordTrace]
  refine ⟨153979252414389830438605853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102652834942926553625737235 153979252414389830438605853)
  ·
    refine ⟨57742219655396186414477195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153979252414389830438605853 57742219655396186414477195)
    ·
      refine ⟨86613329483094279621715793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57742219655396186414477195 86613329483094279621715793)
      ·
        refine ⟨64959997112320709716286845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86613329483094279621715793 64959997112320709716286845)
        ·
          refine ⟨24359998917120266143607567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64959997112320709716286845 24359998917120266143607567)
          ·
            refine ⟨36539998375680399215411351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24359998917120266143607567 36539998375680399215411351)
            ·
              refine ⟨54809997563520598823117027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36539998375680399215411351 54809997563520598823117027)
              ·
                refine ⟨82214996345280898234675541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54809997563520598823117027 82214996345280898234675541)
                ·
                  refine ⟨240864247105315131546901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 82214996345280898234675541 240864247105315131546901)
                  ·
                    rfl

theorem cell23_4221733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_4221733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4221733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4221733 prefixEnd_4221733 := by exact prefixLift 4221733
  have htrace : WordTrace (prefixWord ++ tailWord_4221733) baseStart_4221733 baseEnd_4221733 := by
    simpa [prefixWord, tailWord_4221733, baseEnd_4221733] using wordTrace_append hprefix tailTrace_4221733
  have hstable : (prefixWord ++ tailWord_4221733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4221733).length < 2 ^ (prefixWord ++ tailWord_4221733).sum := by decide
  have hdescent : baseEnd_4221733 < baseStart_4221733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4221733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
