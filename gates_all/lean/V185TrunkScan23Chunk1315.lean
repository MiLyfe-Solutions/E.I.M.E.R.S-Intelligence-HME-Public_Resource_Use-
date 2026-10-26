import V185TrunkScan23Chunk1314

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7787908 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_7787908 : Nat := 118140960795 + 7787908 * 2 ^ 59
def prefixEnd_7787908 : Nat := 4983230072969 + 3 ^ 40 * 7787908 * 2
def baseEnd_7787908 : Nat := 3998940096995421007834069

theorem tailTrace_7787908 : CollatzResearch.WordTrace tailWord_7787908 prefixEnd_7787908 3998940096995421007834069 := by
  unfold tailWord_7787908
  simp only [CollatzResearch.WordTrace]
  refine ⟨142024170134873429819662189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189365560179831239759549585 142024170134873429819662189)
  ·
    refine ⟨53259063800577536182373321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142024170134873429819662189 53259063800577536182373321)
    ·
      refine ⟨39944297850433152136779991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53259063800577536182373321 39944297850433152136779991)
      ·
        refine ⟨59916446775649728205169987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39944297850433152136779991 59916446775649728205169987)
        ·
          refine ⟨89874670163474592307754981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59916446775649728205169987 89874670163474592307754981)
          ·
            refine ⟨16851500655651486057704059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89874670163474592307754981 16851500655651486057704059)
            ·
              refine ⟨25277250983477229086556089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16851500655651486057704059 25277250983477229086556089)
              ·
                refine ⟨18957938237607921814917067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25277250983477229086556089 18957938237607921814917067)
                ·
                  refine ⟨28436907356411882722375601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18957938237607921814917067 28436907356411882722375601)
                  ·
                    refine ⟨21327680517308912041781701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28436907356411882722375601 21327680517308912041781701)
                    ·
                      refine ⟨3998940096995421007834069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21327680517308912041781701 3998940096995421007834069)
                      ·
                        rfl

theorem cell23_7787908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_7787908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787908 prefixEnd_7787908 := by exact prefixLift 7787908
  have htrace : WordTrace (prefixWord ++ tailWord_7787908) baseStart_7787908 baseEnd_7787908 := by
    simpa [prefixWord, tailWord_7787908, baseEnd_7787908] using wordTrace_append hprefix tailTrace_7787908
  have hstable : (prefixWord ++ tailWord_7787908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787908).length < 2 ^ (prefixWord ++ tailWord_7787908).sum := by decide
  have hdescent : baseEnd_7787908 < baseStart_7787908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787915 : List Nat := [1, 1, 1, 1, 4, 3, 5, 1, 1, 2, 3]
def baseStart_7787915 : Nat := 118140960795 + 7787915 * 2 ^ 59
def prefixEnd_7787915 : Nat := 4983230072969 + 3 ^ 40 * 7787915 * 2
def baseEnd_7787915 : Nat := 3998943691360002480446537

theorem tailTrace_7787915 : CollatzResearch.WordTrace tailWord_7787915 prefixEnd_7787915 3998943691360002480446537 := by
  unfold tailWord_7787915
  simp only [CollatzResearch.WordTrace]
  refine ⟨284048595580721499834829199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189365730387147666556552799 284048595580721499834829199)
  ·
    refine ⟨426072893371082249752243799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284048595580721499834829199 426072893371082249752243799)
    ·
      refine ⟨639109340056623374628365699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426072893371082249752243799 639109340056623374628365699)
      ·
        refine ⟨958664010084935061942548549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639109340056623374628365699 958664010084935061942548549)
        ·
          refine ⟨179749501890925324114227853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 958664010084935061942548549 179749501890925324114227853)
          ·
            refine ⟨67406063209096996542835445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179749501890925324114227853 67406063209096996542835445)
            ·
              refine ⟨6319318425852843425890823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67406063209096996542835445 6319318425852843425890823)
              ·
                refine ⟨9478977638779265138836235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6319318425852843425890823 9478977638779265138836235)
                ·
                  refine ⟨14218466458168897708254353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9478977638779265138836235 14218466458168897708254353)
                  ·
                    refine ⟨10663849843626673281190765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14218466458168897708254353 10663849843626673281190765)
                    ·
                      refine ⟨3998943691360002480446537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10663849843626673281190765 3998943691360002480446537)
                      ·
                        rfl

theorem cell23_7787915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 1, 2, 3].length) (baseStart_7787915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787915 prefixEnd_7787915 := by exact prefixLift 7787915
  have htrace : WordTrace (prefixWord ++ tailWord_7787915) baseStart_7787915 baseEnd_7787915 := by
    simpa [prefixWord, tailWord_7787915, baseEnd_7787915] using wordTrace_append hprefix tailTrace_7787915
  have hstable : (prefixWord ++ tailWord_7787915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787915).length < 2 ^ (prefixWord ++ tailWord_7787915).sum := by decide
  have hdescent : baseEnd_7787915 < baseStart_7787915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787918 : List Nat := [4, 1, 1, 4, 3, 10]
def baseStart_7787918 : Nat := 118140960795 + 7787918 * 2 ^ 59
def prefixEnd_7787918 : Nat := 4983230072969 + 3 ^ 40 * 7787918 * 2
def baseEnd_7787918 : Nat := 16456564739925785879461

theorem tailTrace_7787918 : CollatzResearch.WordTrace tailWord_7787918 prefixEnd_7787918 16456564739925785879461 := by
  unfold tailWord_7787918
  simp only [CollatzResearch.WordTrace]
  refine ⟨35506088124963828918398551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189365803333140420898125605 35506088124963828918398551)
  ·
    refine ⟨53259132187445743377597827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35506088124963828918398551 53259132187445743377597827)
    ·
      refine ⟨79888698281168615066396741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53259132187445743377597827 79888698281168615066396741)
      ·
        refine ⟨14979130927719115324949389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79888698281168615066396741 14979130927719115324949389)
        ·
          refine ⟨5617174097894668246856021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14979130927719115324949389 5617174097894668246856021)
          ·
            refine ⟨16456564739925785879461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5617174097894668246856021 16456564739925785879461)
            ·
              rfl

theorem cell23_7787918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 10].length) (baseStart_7787918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787918 prefixEnd_7787918 := by exact prefixLift 7787918
  have htrace : WordTrace (prefixWord ++ tailWord_7787918) baseStart_7787918 baseEnd_7787918 := by
    simpa [prefixWord, tailWord_7787918, baseEnd_7787918] using wordTrace_append hprefix tailTrace_7787918
  have hstable : (prefixWord ++ tailWord_7787918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787918).length < 2 ^ (prefixWord ++ tailWord_7787918).sum := by decide
  have hdescent : baseEnd_7787918 < baseStart_7787918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787929 : List Nat := [1, 2, 1, 2, 1, 5, 4, 2, 1, 2, 2]
def baseStart_7787929 : Nat := 118140960795 + 7787929 * 2 ^ 59
def prefixEnd_7787929 : Nat := 4983230072969 + 3 ^ 40 * 7787929 * 2
def baseEnd_7787929 : Nat := 3998950880089165425671473

theorem tailTrace_7787929 : CollatzResearch.WordTrace tailWord_7787929 prefixEnd_7787929 3998950880089165425671473 := by
  unfold tailWord_7787929
  simp only [CollatzResearch.WordTrace]
  refine ⟨284049106202670780225838841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189366070801780520150559227 284049106202670780225838841)
  ·
    refine ⟨213036829652003085169379131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284049106202670780225838841 213036829652003085169379131)
    ·
      refine ⟨319555244478004627754068697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213036829652003085169379131 319555244478004627754068697)
      ·
        refine ⟨239666433358503470815551523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319555244478004627754068697 239666433358503470815551523)
        ·
          refine ⟨359499650037755206223327285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239666433358503470815551523 359499650037755206223327285)
          ·
            refine ⟨33703092191039550583436933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 359499650037755206223327285 33703092191039550583436933)
            ·
              refine ⟨6319329785819915734394425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33703092191039550583436933 6319329785819915734394425)
              ·
                refine ⟨4739497339364936800795819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6319329785819915734394425 4739497339364936800795819)
                ·
                  refine ⟨7109246009047405201193729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4739497339364936800795819 7109246009047405201193729)
                  ·
                    refine ⟨5331934506785553900895297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7109246009047405201193729 5331934506785553900895297)
                    ·
                      refine ⟨3998950880089165425671473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5331934506785553900895297 3998950880089165425671473)
                      ·
                        rfl

theorem cell23_7787929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 1, 2, 2].length) (baseStart_7787929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787929 prefixEnd_7787929 := by exact prefixLift 7787929
  have htrace : WordTrace (prefixWord ++ tailWord_7787929) baseStart_7787929 baseEnd_7787929 := by
    simpa [prefixWord, tailWord_7787929, baseEnd_7787929] using wordTrace_append hprefix tailTrace_7787929
  have hstable : (prefixWord ++ tailWord_7787929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787929).length < 2 ^ (prefixWord ++ tailWord_7787929).sum := by decide
  have hdescent : baseEnd_7787929 < baseStart_7787929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787971 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 5]
def baseStart_7787971 : Nat := 118140960795 + 7787971 * 2 ^ 59
def prefixEnd_7787971 : Nat := 4983230072969 + 3 ^ 40 * 7787971 * 2
def baseEnd_7787971 : Nat := 3998972446276654261346279

theorem tailTrace_7787971 : CollatzResearch.WordTrace tailWord_7787971 prefixEnd_7787971 3998972446276654261346279 := by
  unfold tailWord_7787971
  simp only [CollatzResearch.WordTrace]
  refine ⟨284050638068518621398867767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189367092045679080932578511 284050638068518621398867767)
  ·
    refine ⟨426075957102777932098301651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284050638068518621398867767 426075957102777932098301651)
    ·
      refine ⟨639113935654166898147452477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426075957102777932098301651 639113935654166898147452477)
      ·
        refine ⟨239667725870312586805294679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639113935654166898147452477 239667725870312586805294679)
        ·
          refine ⟨359501588805468880207942019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239667725870312586805294679 359501588805468880207942019)
          ·
            refine ⟨539252383208203320311913029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359501588805468880207942019 539252383208203320311913029)
            ·
              refine ⟨101109821851538122558483693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 539252383208203320311913029 101109821851538122558483693)
              ·
                refine ⟨37916183194326795959431385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101109821851538122558483693 37916183194326795959431385)
                ·
                  refine ⟨28437137395745096969573539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37916183194326795959431385 28437137395745096969573539)
                  ·
                    refine ⟨42655706093617645454360309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28437137395745096969573539 42655706093617645454360309)
                    ·
                      refine ⟨3998972446276654261346279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42655706093617645454360309 3998972446276654261346279)
                      ·
                        rfl

theorem cell23_7787971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_7787971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787971 prefixEnd_7787971 := by exact prefixLift 7787971
  have htrace : WordTrace (prefixWord ++ tailWord_7787971) baseStart_7787971 baseEnd_7787971 := by
    simpa [prefixWord, tailWord_7787971, baseEnd_7787971] using wordTrace_append hprefix tailTrace_7787971
  have hstable : (prefixWord ++ tailWord_7787971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787971).length < 2 ^ (prefixWord ++ tailWord_7787971).sum := by decide
  have hdescent : baseEnd_7787971 < baseStart_7787971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788042 : List Nat := [3, 1, 2, 2, 2, 3, 3, 2, 5]
def baseStart_7788042 : Nat := 118140960795 + 7788042 * 2 ^ 59
def prefixEnd_7788042 : Nat := 4983230072969 + 3 ^ 40 * 7788042 * 2
def baseEnd_7788042 : Nat := 444334322600347053728717

theorem tailTrace_7788042 : CollatzResearch.WordTrace tailWord_7788042 prefixEnd_7788042 444334322600347053728717 := by
  unfold tailWord_7788042
  simp only [CollatzResearch.WordTrace]
  refine ⟨71013306912815350131175595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189368818434174267016468253 71013306912815350131175595)
  ·
    refine ⟨106519960369223025196763393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71013306912815350131175595 106519960369223025196763393)
    ·
      refine ⟨79889970276917268897572545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106519960369223025196763393 79889970276917268897572545)
      ·
        refine ⟨59917477707687951673179409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79889970276917268897572545 59917477707687951673179409)
        ·
          refine ⟨44938108280765963754884557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59917477707687951673179409 44938108280765963754884557)
          ·
            refine ⟨16851790605287236408081709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44938108280765963754884557 16851790605287236408081709)
            ·
              refine ⟨6319421476982713653030641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16851790605287236408081709 6319421476982713653030641)
              ·
                refine ⟨4739566107737035239772981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6319421476982713653030641 4739566107737035239772981)
                ·
                  refine ⟨444334322600347053728717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4739566107737035239772981 444334322600347053728717)
                  ·
                    rfl

theorem cell23_7788042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 5].length) (baseStart_7788042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788042 prefixEnd_7788042 := by exact prefixLift 7788042
  have htrace : WordTrace (prefixWord ++ tailWord_7788042) baseStart_7788042 baseEnd_7788042 := by
    simpa [prefixWord, tailWord_7788042, baseEnd_7788042] using wordTrace_append hprefix tailTrace_7788042
  have hstable : (prefixWord ++ tailWord_7788042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788042).length < 2 ^ (prefixWord ++ tailWord_7788042).sum := by decide
  have hdescent : baseEnd_7788042 < baseStart_7788042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788058 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4]
def baseStart_7788058 : Nat := 118140960795 + 7788058 * 2 ^ 59
def prefixEnd_7788058 : Nat := 4983230072969 + 3 ^ 40 * 7788058 * 2
def baseEnd_7788058 : Nat := 3999017119093595420958379

theorem tailTrace_7788058 : CollatzResearch.WordTrace tailWord_7788058 prefixEnd_7788058 3999017119093595420958379 := by
  unfold tailWord_7788058
  simp only [CollatzResearch.WordTrace]
  refine ⟨71013452804800858814321207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189369207479468956838189885 71013452804800858814321207)
  ·
    refine ⟨106520179207201288221481811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71013452804800858814321207 106520179207201288221481811)
    ·
      refine ⟨159780268810801932332222717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106520179207201288221481811 159780268810801932332222717)
      ·
        refine ⟨59917600804050724624583519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159780268810801932332222717 59917600804050724624583519)
        ·
          refine ⟨89876401206076086936875279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59917600804050724624583519 89876401206076086936875279)
          ·
            refine ⟨134814601809114130405312919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89876401206076086936875279 134814601809114130405312919)
            ·
              refine ⟨202221902713671195607969379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134814601809114130405312919 202221902713671195607969379)
              ·
                refine ⟨303332854070506793411954069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202221902713671195607969379 303332854070506793411954069)
                ·
                  refine ⟨14218727534555005941185347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 303332854070506793411954069 14218727534555005941185347)
                  ·
                    refine ⟨21328091301832508911778021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14218727534555005941185347 21328091301832508911778021)
                    ·
                      refine ⟨3999017119093595420958379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21328091301832508911778021 3999017119093595420958379)
                      ·
                        rfl

theorem cell23_7788058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_7788058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788058 prefixEnd_7788058 := by exact prefixLift 7788058
  have htrace : WordTrace (prefixWord ++ tailWord_7788058) baseStart_7788058 baseEnd_7788058 := by
    simpa [prefixWord, tailWord_7788058, baseEnd_7788058] using wordTrace_append hprefix tailTrace_7788058
  have hstable : (prefixWord ++ tailWord_7788058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788058).length < 2 ^ (prefixWord ++ tailWord_7788058).sum := by decide
  have hdescent : baseEnd_7788058 < baseStart_7788058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788072 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 2, 5]
def baseStart_7788072 : Nat := 118140960795 + 7788072 * 2 ^ 59
def prefixEnd_7788072 : Nat := 4983230072969 + 3 ^ 40 * 7788072 * 2
def baseEnd_7788072 : Nat := 1333008102607586122061105

theorem tailTrace_7788072 : CollatzResearch.WordTrace tailWord_7788072 prefixEnd_7788072 1333008102607586122061105 := by
  unfold tailWord_7788072
  simp only [CollatzResearch.WordTrace]
  refine ⟨142027160920576357824147235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189369547894101810432196313 142027160920576357824147235)
  ·
    refine ⟨213040741380864536736220853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142027160920576357824147235 213040741380864536736220853)
    ·
      refine ⟨19972569504456050319020705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213040741380864536736220853 19972569504456050319020705)
      ·
        refine ⟨14979427128342037739265529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19972569504456050319020705 14979427128342037739265529)
        ·
          refine ⟨11234570346256528304449147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14979427128342037739265529 11234570346256528304449147)
          ·
            refine ⟨16851855519384792456673721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11234570346256528304449147 16851855519384792456673721)
            ·
              refine ⟨12638891639538594342505291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16851855519384792456673721 12638891639538594342505291)
              ·
                refine ⟨18958337459307891513757937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12638891639538594342505291 18958337459307891513757937)
                ·
                  refine ⟨14218753094480918635318453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18958337459307891513757937 14218753094480918635318453)
                  ·
                    refine ⟨1333008102607586122061105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14218753094480918635318453 1333008102607586122061105)
                    ·
                      rfl

theorem cell23_7788072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_7788072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788072 prefixEnd_7788072 := by exact prefixLift 7788072
  have htrace : WordTrace (prefixWord ++ tailWord_7788072) baseStart_7788072 baseEnd_7788072 := by
    simpa [prefixWord, tailWord_7788072, baseEnd_7788072] using wordTrace_append hprefix tailTrace_7788072
  have hstable : (prefixWord ++ tailWord_7788072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788072).length < 2 ^ (prefixWord ++ tailWord_7788072).sum := by decide
  have hdescent : baseEnd_7788072 < baseStart_7788072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788091 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 9]
def baseStart_7788091 : Nat := 118140960795 + 7788091 * 2 ^ 59
def prefixEnd_7788091 : Nat := 4983230072969 + 3 ^ 40 * 7788091 * 2
def baseEnd_7788091 : Nat := 3999034063955193791845727

theorem tailTrace_7788091 : CollatzResearch.WordTrace tailWord_7788091 prefixEnd_7788091 3999034063955193791845727 := by
  unfold tailWord_7788091
  simp only [CollatzResearch.WordTrace]
  refine ⟨284055014828083881893236127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189370009885389254595490751 284055014828083881893236127)
  ·
    refine ⟨426082522242125822839854191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284055014828083881893236127 426082522242125822839854191)
    ·
      refine ⟨639123783363188734259781287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426082522242125822839854191 639123783363188734259781287)
      ·
        refine ⟨958685675044783101389671931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639123783363188734259781287 958685675044783101389671931)
        ·
          refine ⟨1438028512567174652084507897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958685675044783101389671931 1438028512567174652084507897)
          ·
            refine ⟨1078521384425380989063380923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1438028512567174652084507897 1078521384425380989063380923)
            ·
              refine ⟨1617782076638071483595071385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078521384425380989063380923 1617782076638071483595071385)
              ·
                refine ⟨1213336557478553612696303539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1617782076638071483595071385 1213336557478553612696303539)
                ·
                  refine ⟨1820004836217830419044455309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213336557478553612696303539 1820004836217830419044455309)
                  ·
                    refine ⟨682501813581686407141670741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1820004836217830419044455309 682501813581686407141670741)
                    ·
                      refine ⟨3999034063955193791845727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 682501813581686407141670741 3999034063955193791845727)
                      ·
                        rfl

theorem cell23_7788091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_7788091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788091 prefixEnd_7788091 := by exact prefixLift 7788091
  have htrace : WordTrace (prefixWord ++ tailWord_7788091) baseStart_7788091 baseEnd_7788091 := by
    simpa [prefixWord, tailWord_7788091, baseEnd_7788091] using wordTrace_append hprefix tailTrace_7788091
  have hstable : (prefixWord ++ tailWord_7788091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788091).length < 2 ^ (prefixWord ++ tailWord_7788091).sum := by decide
  have hdescent : baseEnd_7788091 < baseStart_7788091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788095 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 3]
def baseStart_7788095 : Nat := 118140960795 + 7788095 * 2 ^ 59
def prefixEnd_7788095 : Nat := 4983230072969 + 3 ^ 40 * 7788095 * 2
def baseEnd_7788095 : Nat := 3999036117877811776195709

theorem tailTrace_7788095 : CollatzResearch.WordTrace tailWord_7788095 prefixEnd_7788095 3999036117877811776195709 := by
  unfold tailWord_7788095
  simp only [CollatzResearch.WordTrace]
  refine ⟨284055160720069390576381739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189370107146712927050921159 284055160720069390576381739)
  ·
    refine ⟨426082741080104085864572609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284055160720069390576381739 426082741080104085864572609)
    ·
      refine ⟨319562055810078064398429457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426082741080104085864572609 319562055810078064398429457)
      ·
        refine ⟨239671541857558548298822093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319562055810078064398429457 239671541857558548298822093)
        ·
          refine ⟨89876828196584455612058285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239671541857558548298822093 89876828196584455612058285)
          ·
            refine ⟨33703810573719170854521857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89876828196584455612058285 33703810573719170854521857)
            ·
              refine ⟨25277857930289378140891393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33703810573719170854521857 25277857930289378140891393)
              ·
                refine ⟨18958393447717033605668545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25277857930289378140891393 18958393447717033605668545)
                ·
                  refine ⟨14218795085787775204251409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18958393447717033605668545 14218795085787775204251409)
                  ·
                    refine ⟨10664096314340831403188557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14218795085787775204251409 10664096314340831403188557)
                    ·
                      refine ⟨3999036117877811776195709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10664096314340831403188557 3999036117877811776195709)
                      ·
                        rfl

theorem cell23_7788095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_7788095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788095 prefixEnd_7788095 := by exact prefixLift 7788095
  have htrace : WordTrace (prefixWord ++ tailWord_7788095) baseStart_7788095 baseEnd_7788095 := by
    simpa [prefixWord, tailWord_7788095, baseEnd_7788095] using wordTrace_append hprefix tailTrace_7788095
  have hstable : (prefixWord ++ tailWord_7788095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788095).length < 2 ^ (prefixWord ++ tailWord_7788095).sum := by decide
  have hdescent : baseEnd_7788095 < baseStart_7788095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788109 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_7788109 : Nat := 118140960795 + 7788109 * 2 ^ 59
def prefixEnd_7788109 : Nat := 4983230072969 + 3 ^ 40 * 7788109 * 2
def baseEnd_7788109 : Nat := 3999043306606974721420645

theorem tailTrace_7788109 : CollatzResearch.WordTrace tailWord_7788109 prefixEnd_7788109 3999043306606974721420645 := by
  unfold tailWord_7788109
  simp only [CollatzResearch.WordTrace]
  refine ⟨284055671342018670967391381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189370447561345780644927587 284055671342018670967391381)
  ·
    refine ⟨13315109594157125201596471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 284055671342018670967391381 13315109594157125201596471)
    ·
      refine ⟨19972664391235687802394707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13315109594157125201596471 19972664391235687802394707)
      ·
        refine ⟨29958996586853531703592061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19972664391235687802394707 29958996586853531703592061)
        ·
          refine ⟨11234623720070074388847023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29958996586853531703592061 11234623720070074388847023)
          ·
            refine ⟨16851935580105111583270535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11234623720070074388847023 16851935580105111583270535)
            ·
              refine ⟨25277903370157667374905803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16851935580105111583270535 25277903370157667374905803)
              ·
                refine ⟨37916855055236501062358705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25277903370157667374905803 37916855055236501062358705)
                ·
                  refine ⟨28437641291427375796769029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37916855055236501062358705 28437641291427375796769029)
                  ·
                    refine ⟨5332057742142632961894193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28437641291427375796769029 5332057742142632961894193)
                    ·
                      refine ⟨3999043306606974721420645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5332057742142632961894193 3999043306606974721420645)
                      ·
                        rfl

theorem cell23_7788109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_7788109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788109 prefixEnd_7788109 := by exact prefixLift 7788109
  have htrace : WordTrace (prefixWord ++ tailWord_7788109) baseStart_7788109 baseEnd_7788109 := by
    simpa [prefixWord, tailWord_7788109, baseEnd_7788109] using wordTrace_append hprefix tailTrace_7788109
  have hstable : (prefixWord ++ tailWord_7788109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788109).length < 2 ^ (prefixWord ++ tailWord_7788109).sum := by decide
  have hdescent : baseEnd_7788109 < baseStart_7788109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788236 : List Nat := [2, 2, 1, 5, 2, 2, 1, 2, 1, 2, 3]
def baseStart_7788236 : Nat := 118140960795 + 7788236 * 2 ^ 59
def prefixEnd_7788236 : Nat := 4983230072969 + 3 ^ 40 * 7788236 * 2
def baseEnd_7788236 : Nat := 3999108518650095724532561

theorem tailTrace_7788236 : CollatzResearch.WordTrace tailWord_7788236 prefixEnd_7788236 3999108518650095724532561 := by
  unfold tailWord_7788236
  simp only [CollatzResearch.WordTrace]
  refine ⟨142030151706279285828632281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189373535608372381104843041 142030151706279285828632281)
  ·
    refine ⟨106522613779709464371474211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142030151706279285828632281 106522613779709464371474211)
    ·
      refine ⟨159783920669564196557211317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106522613779709464371474211 159783920669564196557211317)
      ·
        refine ⟨14979742562771643427238561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159783920669564196557211317 14979742562771643427238561)
        ·
          refine ⟨11234806922078732570428921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14979742562771643427238561 11234806922078732570428921)
          ·
            refine ⟨8426105191559049427821691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11234806922078732570428921 8426105191559049427821691)
            ·
              refine ⟨12639157787338574141732537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8426105191559049427821691 12639157787338574141732537)
              ·
                refine ⟨9479368340503930606299403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12639157787338574141732537 9479368340503930606299403)
                ·
                  refine ⟨14219052510755895909449105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9479368340503930606299403 14219052510755895909449105)
                  ·
                    refine ⟨10664289383066921932086829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14219052510755895909449105 10664289383066921932086829)
                    ·
                      refine ⟨3999108518650095724532561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10664289383066921932086829 3999108518650095724532561)
                      ·
                        rfl

theorem cell23_7788236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_7788236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788236 prefixEnd_7788236 := by exact prefixLift 7788236
  have htrace : WordTrace (prefixWord ++ tailWord_7788236) baseStart_7788236 baseEnd_7788236 := by
    simpa [prefixWord, tailWord_7788236, baseEnd_7788236] using wordTrace_append hprefix tailTrace_7788236
  have hstable : (prefixWord ++ tailWord_7788236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788236).length < 2 ^ (prefixWord ++ tailWord_7788236).sum := by decide
  have hdescent : baseEnd_7788236 < baseStart_7788236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788246 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_7788246 : Nat := 118140960795 + 7788246 * 2 ^ 59
def prefixEnd_7788246 : Nat := 4983230072969 + 3 ^ 40 * 7788246 * 2
def baseEnd_7788246 : Nat := 3999113653456640685407515

theorem tailTrace_7788246 : CollatzResearch.WordTrace tailWord_7788246 prefixEnd_7788246 3999113653456640685407515 := by
  unfold tailWord_7788246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17753791758907646460320537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189373778761681562243419061 17753791758907646460320537)
  ·
    refine ⟨13315343819180734845240403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17753791758907646460320537 13315343819180734845240403)
    ·
      refine ⟨19973015728771102267860605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13315343819180734845240403 19973015728771102267860605)
      ·
        refine ⟨7489880898289163350447727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19973015728771102267860605 7489880898289163350447727)
        ·
          refine ⟨11234821347433745025671591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7489880898289163350447727 11234821347433745025671591)
          ·
            refine ⟨16852232021150617538507387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11234821347433745025671591 16852232021150617538507387)
            ·
              refine ⟨25278348031725926307761081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16852232021150617538507387 25278348031725926307761081)
              ·
                refine ⟨18958761023794444730820811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25278348031725926307761081 18958761023794444730820811)
                ·
                  refine ⟨28438141535691667096231217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18958761023794444730820811 28438141535691667096231217)
                  ·
                    refine ⟨21328606151768750322173413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28438141535691667096231217 21328606151768750322173413)
                    ·
                      refine ⟨3999113653456640685407515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21328606151768750322173413 3999113653456640685407515)
                      ·
                        rfl

theorem cell23_7788246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_7788246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788246 prefixEnd_7788246 := by exact prefixLift 7788246
  have htrace : WordTrace (prefixWord ++ tailWord_7788246) baseStart_7788246 baseEnd_7788246 := by
    simpa [prefixWord, tailWord_7788246, baseEnd_7788246] using wordTrace_append hprefix tailTrace_7788246
  have hstable : (prefixWord ++ tailWord_7788246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788246).length < 2 ^ (prefixWord ++ tailWord_7788246).sum := by decide
  have hdescent : baseEnd_7788246 < baseStart_7788246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788253 : List Nat := [1, 4, 3, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7788253 : Nat := 118140960795 + 7788253 * 2 ^ 59
def prefixEnd_7788253 : Nat := 4983230072969 + 3 ^ 40 * 7788253 * 2
def baseEnd_7788253 : Nat := 3999117247821222158019983

theorem tailTrace_7788253 : CollatzResearch.WordTrace tailWord_7788253 prefixEnd_7788253 3999117247821222158019983 := by
  unfold tailWord_7788253
  simp only [CollatzResearch.WordTrace]
  refine ⟨284060923453496983560633413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189373948968997989040422275 284060923453496983560633413)
  ·
    refine ⟨53261423147530684417618765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284060923453496983560633413 53261423147530684417618765)
    ·
      refine ⟨19973033680324006656607037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53261423147530684417618765 19973033680324006656607037)
      ·
        refine ⟨7489887630121502496227639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19973033680324006656607037 7489887630121502496227639)
        ·
          refine ⟨11234831445182253744341459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7489887630121502496227639 11234831445182253744341459)
          ·
            refine ⟨16852247167773380616512189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11234831445182253744341459 16852247167773380616512189)
            ·
              refine ⟨6319592687915017731192071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16852247167773380616512189 6319592687915017731192071)
              ·
                refine ⟨9479389031872526596788107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6319592687915017731192071 9479389031872526596788107)
                ·
                  refine ⟨14219083547808789895182161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9479389031872526596788107 14219083547808789895182161)
                  ·
                    refine ⟨10664312660856592421386621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14219083547808789895182161 10664312660856592421386621)
                    ·
                      refine ⟨3999117247821222158019983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10664312660856592421386621 3999117247821222158019983)
                      ·
                        rfl

theorem cell23_7788253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7788253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788253 prefixEnd_7788253 := by exact prefixLift 7788253
  have htrace : WordTrace (prefixWord ++ tailWord_7788253) baseStart_7788253 baseEnd_7788253 := by
    simpa [prefixWord, tailWord_7788253, baseEnd_7788253] using wordTrace_append hprefix tailTrace_7788253
  have hstable : (prefixWord ++ tailWord_7788253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788253).length < 2 ^ (prefixWord ++ tailWord_7788253).sum := by decide
  have hdescent : baseEnd_7788253 < baseStart_7788253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788275 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 3]
def baseStart_7788275 : Nat := 118140960795 + 7788275 * 2 ^ 59
def prefixEnd_7788275 : Nat := 4983230072969 + 3 ^ 40 * 7788275 * 2
def baseEnd_7788275 : Nat := 3999128544395621071944881

theorem tailTrace_7788275 : CollatzResearch.WordTrace tailWord_7788275 prefixEnd_7788275 3999128544395621071944881 := by
  unfold tailWord_7788275
  simp only [CollatzResearch.WordTrace]
  refine ⟨284061725859417281317934279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189374483906278187545289519 284061725859417281317934279)
  ·
    refine ⟨426092588789125921976901419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284061725859417281317934279 426092588789125921976901419)
    ·
      refine ⟨639138883183688882965352129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426092588789125921976901419 639138883183688882965352129)
      ·
        refine ⟨479354162387766662224014097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639138883183688882965352129 479354162387766662224014097)
        ·
          refine ⟨359515621790824996668010573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479354162387766662224014097 359515621790824996668010573)
          ·
            refine ⟨134818358171559373750503965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359515621790824996668010573 134818358171559373750503965)
            ·
              refine ⟨50556884314334765156438987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134818358171559373750503965 50556884314334765156438987)
              ·
                refine ⟨75835326471502147734658481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50556884314334765156438987 75835326471502147734658481)
                ·
                  refine ⟨56876494853626610800993861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75835326471502147734658481 56876494853626610800993861)
                  ·
                    refine ⟨10664342785054989525186349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56876494853626610800993861 10664342785054989525186349)
                    ·
                      refine ⟨3999128544395621071944881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10664342785054989525186349 3999128544395621071944881)
                      ·
                        rfl

theorem cell23_7788275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 3].length) (baseStart_7788275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788275 prefixEnd_7788275 := by exact prefixLift 7788275
  have htrace : WordTrace (prefixWord ++ tailWord_7788275) baseStart_7788275 baseEnd_7788275 := by
    simpa [prefixWord, tailWord_7788275, baseEnd_7788275] using wordTrace_append hprefix tailTrace_7788275
  have hstable : (prefixWord ++ tailWord_7788275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788275).length < 2 ^ (prefixWord ++ tailWord_7788275).sum := by decide
  have hdescent : baseEnd_7788275 < baseStart_7788275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788305 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 3]
def baseStart_7788305 : Nat := 118140960795 + 7788305 * 2 ^ 59
def prefixEnd_7788305 : Nat := 4983230072969 + 3 ^ 40 * 7788305 * 2
def baseEnd_7788305 : Nat := 3999143948815255954569743

theorem tailTrace_7788305 : CollatzResearch.WordTrace tailWord_7788305 prefixEnd_7788305 3999143948815255954569743 := by
  unfold tailWord_7788305
  simp only [CollatzResearch.WordTrace]
  refine ⟨284062820049308596441526369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189375213366205730961017579 284062820049308596441526369)
  ·
    refine ⟨213047115036981447331144777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284062820049308596441526369 213047115036981447331144777)
    ·
      refine ⟨159785336277736085498358583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213047115036981447331144777 159785336277736085498358583)
      ·
        refine ⟨239678004416604128247537875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159785336277736085498358583 239678004416604128247537875)
        ·
          refine ⟨359517006624906192371306813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239678004416604128247537875 359517006624906192371306813)
          ·
            refine ⟨134818877484339822139240055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359517006624906192371306813 134818877484339822139240055)
            ·
              refine ⟨202228316226509733208860083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134818877484339822139240055 202228316226509733208860083)
              ·
                refine ⟨303342474339764599813290125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202228316226509733208860083 303342474339764599813290125)
                ·
                  refine ⟨113753427877411724929983797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303342474339764599813290125 113753427877411724929983797)
                  ·
                    refine ⟨10664383863507349212185981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113753427877411724929983797 10664383863507349212185981)
                    ·
                      refine ⟨3999143948815255954569743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10664383863507349212185981 3999143948815255954569743)
                      ·
                        rfl

theorem cell23_7788305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_7788305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788305 prefixEnd_7788305 := by exact prefixLift 7788305
  have htrace : WordTrace (prefixWord ++ tailWord_7788305) baseStart_7788305 baseEnd_7788305 := by
    simpa [prefixWord, tailWord_7788305, baseEnd_7788305] using wordTrace_append hprefix tailTrace_7788305
  have hstable : (prefixWord ++ tailWord_7788305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788305).length < 2 ^ (prefixWord ++ tailWord_7788305).sum := by decide
  have hdescent : baseEnd_7788305 < baseStart_7788305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788306 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_7788306 : Nat := 118140960795 + 7788306 * 2 ^ 59
def prefixEnd_7788306 : Nat := 4983230072969 + 3 ^ 40 * 7788306 * 2
def baseEnd_7788306 : Nat := 3999144462295910450657239

theorem tailTrace_7788306 : CollatzResearch.WordTrace tailWord_7788306 prefixEnd_7788306 3999144462295910450657239 := by
  unfold tailWord_7788306
  simp only [CollatzResearch.WordTrace]
  refine ⟨71015714130576243403078193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189375237681536649074875181 71015714130576243403078193)
  ·
    refine ⟨53261785597932182552308645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71015714130576243403078193 53261785597932182552308645)
    ·
      refine ⟨9986584799612284228557871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53261785597932182552308645 9986584799612284228557871)
      ·
        refine ⟨14979877199418426342836807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9986584799612284228557871 14979877199418426342836807)
        ·
          refine ⟨22469815799127639514255211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14979877199418426342836807 22469815799127639514255211)
          ·
            refine ⟨33704723698691459271382817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22469815799127639514255211 33704723698691459271382817)
            ·
              refine ⟨25278542774018594453537113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33704723698691459271382817 25278542774018594453537113)
              ·
                refine ⟨18958907080513945840152835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25278542774018594453537113 18958907080513945840152835)
                ·
                  refine ⟨28438360620770918760229253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18958907080513945840152835 28438360620770918760229253)
                  ·
                    refine ⟨5332192616394547267542985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28438360620770918760229253 5332192616394547267542985)
                    ·
                      refine ⟨3999144462295910450657239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5332192616394547267542985 3999144462295910450657239)
                      ·
                        rfl

theorem cell23_7788306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_7788306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788306 prefixEnd_7788306 := by exact prefixLift 7788306
  have htrace : WordTrace (prefixWord ++ tailWord_7788306) baseStart_7788306 baseEnd_7788306 := by
    simpa [prefixWord, tailWord_7788306, baseEnd_7788306] using wordTrace_append hprefix tailTrace_7788306
  have hstable : (prefixWord ++ tailWord_7788306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788306).length < 2 ^ (prefixWord ++ tailWord_7788306).sum := by decide
  have hdescent : baseEnd_7788306 < baseStart_7788306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788312 : List Nat := [2, 1, 2, 3, 1, 1, 3, 5, 5]
def baseStart_7788312 : Nat := 118140960795 + 7788312 * 2 ^ 59
def prefixEnd_7788312 : Nat := 4983230072969 + 3 ^ 40 * 7788312 * 2
def baseEnd_7788312 : Nat := 444349727019981936353579

theorem tailTrace_7788312 : CollatzResearch.WordTrace tailWord_7788312 prefixEnd_7788312 444349727019981936353579 := by
  unfold tailWord_7788312
  simp only [CollatzResearch.WordTrace]
  refine ⟨142031537680141618318515595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189375383573522157758020793 142031537680141618318515595)
  ·
    refine ⟨213047306520212427477773393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142031537680141618318515595 213047306520212427477773393)
    ·
      refine ⟨159785479890159320608330045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213047306520212427477773393 159785479890159320608330045)
      ·
        refine ⟨59919554958809745228123767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159785479890159320608330045 59919554958809745228123767)
        ·
          refine ⟨89879332438214617842185651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59919554958809745228123767 89879332438214617842185651)
          ·
            refine ⟨134818998657321926763278477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89879332438214617842185651 134818998657321926763278477)
            ·
              refine ⟨50557124496495722536229429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134818998657321926763278477 50557124496495722536229429)
              ·
                refine ⟨4739730421546473987771509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50557124496495722536229429 4739730421546473987771509)
                ·
                  refine ⟨444349727019981936353579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4739730421546473987771509 444349727019981936353579)
                  ·
                    rfl

theorem cell23_7788312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 5].length) (baseStart_7788312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788312 prefixEnd_7788312 := by exact prefixLift 7788312
  have htrace : WordTrace (prefixWord ++ tailWord_7788312) baseStart_7788312 baseEnd_7788312 := by
    simpa [prefixWord, tailWord_7788312, baseEnd_7788312] using wordTrace_append hprefix tailTrace_7788312
  have hstable : (prefixWord ++ tailWord_7788312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788312).length < 2 ^ (prefixWord ++ tailWord_7788312).sum := by decide
  have hdescent : baseEnd_7788312 < baseStart_7788312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788322 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_7788322 : Nat := 118140960795 + 7788322 * 2 ^ 59
def prefixEnd_7788322 : Nat := 4983230072969 + 3 ^ 40 * 7788322 * 2
def baseEnd_7788322 : Nat := 3999152677986382388057165

theorem tailTrace_7788322 : CollatzResearch.WordTrace tailWord_7788322 prefixEnd_7788322 3999152677986382388057165 := by
  unfold tailWord_7788322
  simp only [CollatzResearch.WordTrace]
  refine ⟨71015860022561752086223805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189375626726831338896596813 71015860022561752086223805)
  ·
    refine ⟨26630947508460657032333927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71015860022561752086223805 26630947508460657032333927)
    ·
      refine ⟨39946421262690985548500891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26630947508460657032333927 39946421262690985548500891)
      ·
        refine ⟨59919631894036478322751337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39946421262690985548500891 59919631894036478322751337)
        ·
          refine ⟨44939723920527358742063503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59919631894036478322751337 44939723920527358742063503)
          ·
            refine ⟨67409585880791038113095255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44939723920527358742063503 67409585880791038113095255)
            ·
              refine ⟨101114378821186557169642883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67409585880791038113095255 101114378821186557169642883)
              ·
                refine ⟨151671568231779835754464325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101114378821186557169642883 151671568231779835754464325)
                ·
                  refine ⟨28438419043458719203962061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151671568231779835754464325 28438419043458719203962061)
                  ·
                    refine ⟨10664407141297019701485773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28438419043458719203962061 10664407141297019701485773)
                    ·
                      refine ⟨3999152677986382388057165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10664407141297019701485773 3999152677986382388057165)
                      ·
                        rfl

theorem cell23_7788322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_7788322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788322 prefixEnd_7788322 := by exact prefixLift 7788322
  have htrace : WordTrace (prefixWord ++ tailWord_7788322) baseStart_7788322 baseEnd_7788322 := by
    simpa [prefixWord, tailWord_7788322, baseEnd_7788322] using wordTrace_append hprefix tailTrace_7788322
  have hstable : (prefixWord ++ tailWord_7788322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788322).length < 2 ^ (prefixWord ++ tailWord_7788322).sum := by decide
  have hdescent : baseEnd_7788322 < baseStart_7788322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788340 : List Nat := [2, 5, 1, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_7788340 : Nat := 118140960795 + 7788340 * 2 ^ 59
def prefixEnd_7788340 : Nat := 4983230072969 + 3 ^ 40 * 7788340 * 2
def baseEnd_7788340 : Nat := 3999161920638163317632083

theorem tailTrace_7788340 : CollatzResearch.WordTrace tailWord_7788340 prefixEnd_7788340 3999161920638163317632083 := by
  unfold tailWord_7788340
  simp only [CollatzResearch.WordTrace]
  refine ⟨142032048302090898709525237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189376064402787864946033649 142032048302090898709525237)
  ·
    refine ⟨13315504528321021754017991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142032048302090898709525237 13315504528321021754017991)
    ·
      refine ⟨19973256792481532631026987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13315504528321021754017991 19973256792481532631026987)
      ·
        refine ⟨29959885188722298946540481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19973256792481532631026987 29959885188722298946540481)
        ·
          refine ⟨22469913891541724209905361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29959885188722298946540481 22469913891541724209905361)
          ·
            refine ⟨16852435418656293157429021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22469913891541724209905361 16852435418656293157429021)
            ·
              refine ⟨6319663281996109934035883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16852435418656293157429021 6319663281996109934035883)
              ·
                refine ⟨9479494922994164901053825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6319663281996109934035883 9479494922994164901053825)
                ·
                  refine ⟨7109621192245623675790369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9479494922994164901053825 7109621192245623675790369)
                  ·
                    refine ⟨5332215894184217756842777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7109621192245623675790369 5332215894184217756842777)
                    ·
                      refine ⟨3999161920638163317632083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5332215894184217756842777 3999161920638163317632083)
                      ·
                        rfl

theorem cell23_7788340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_7788340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788340 prefixEnd_7788340 := by exact prefixLift 7788340
  have htrace : WordTrace (prefixWord ++ tailWord_7788340) baseStart_7788340 baseEnd_7788340 := by
    simpa [prefixWord, tailWord_7788340, baseEnd_7788340] using wordTrace_append hprefix tailTrace_7788340
  have hstable : (prefixWord ++ tailWord_7788340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788340).length < 2 ^ (prefixWord ++ tailWord_7788340).sum := by decide
  have hdescent : baseEnd_7788340 < baseStart_7788340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788362 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_7788362 : Nat := 118140960795 + 7788362 * 2 ^ 59
def prefixEnd_7788362 : Nat := 4983230072969 + 3 ^ 40 * 7788362 * 2
def baseEnd_7788362 : Nat := 3999173217212562231556981

theorem tailTrace_7788362 : CollatzResearch.WordTrace tailWord_7788362 prefixEnd_7788362 3999173217212562231556981 := by
  unfold tailWord_7788362
  simp only [CollatzResearch.WordTrace]
  refine ⟨71016224752525523794087835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189376599340068063450900893 71016224752525523794087835)
  ·
    refine ⟨106524337128788285691131753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71016224752525523794087835 106524337128788285691131753)
    ·
      refine ⟨79893252846591214268348815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106524337128788285691131753 79893252846591214268348815)
      ·
        refine ⟨119839879269886821402523223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79893252846591214268348815 119839879269886821402523223)
        ·
          refine ⟨179759818904830232103784835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119839879269886821402523223 179759818904830232103784835)
          ·
            refine ⟨269639728357245348155677253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179759818904830232103784835 269639728357245348155677253)
            ·
              refine ⟨50557449066983502779189485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269639728357245348155677253 50557449066983502779189485)
              ·
                refine ⟨18959043400118813542196057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50557449066983502779189485 18959043400118813542196057)
                ·
                  refine ⟨14219282550089110156647043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18959043400118813542196057 14219282550089110156647043)
                  ·
                    refine ⟨21328923825133665234970565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14219282550089110156647043 21328923825133665234970565)
                    ·
                      refine ⟨3999173217212562231556981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21328923825133665234970565 3999173217212562231556981)
                      ·
                        rfl

theorem cell23_7788362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_7788362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788362 prefixEnd_7788362 := by exact prefixLift 7788362
  have htrace : WordTrace (prefixWord ++ tailWord_7788362) baseStart_7788362 baseEnd_7788362 := by
    simpa [prefixWord, tailWord_7788362, baseEnd_7788362] using wordTrace_append hprefix tailTrace_7788362
  have hstable : (prefixWord ++ tailWord_7788362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788362).length < 2 ^ (prefixWord ++ tailWord_7788362).sum := by decide
  have hdescent : baseEnd_7788362 < baseStart_7788362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788385 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 8]
def baseStart_7788385 : Nat := 118140960795 + 7788385 * 2 ^ 59
def prefixEnd_7788385 : Nat := 4983230072969 + 3 ^ 40 * 7788385 * 2
def baseEnd_7788385 : Nat := 444353891918623960174375

theorem tailTrace_7788385 : CollatzResearch.WordTrace tailWord_7788385 prefixEnd_7788385 444353891918623960174375 := by
  unfold tailWord_7788385
  simp only [CollatzResearch.WordTrace]
  refine ⟨284065737889018770104438609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189377158592679180069625739 284065737889018770104438609)
  ·
    refine ⟨213049303416764077578328957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284065737889018770104438609 213049303416764077578328957)
    ·
      refine ⟨79893488781286529091873359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213049303416764077578328957 79893488781286529091873359)
      ·
        refine ⟨119840233171929793637810039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79893488781286529091873359 119840233171929793637810039)
        ·
          refine ⟨179760349757894690456715059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119840233171929793637810039 179760349757894690456715059)
          ·
            refine ⟨269640524636842035685072589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179760349757894690456715059 269640524636842035685072589)
            ·
              refine ⟨101115196738815763381902221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269640524636842035685072589 101115196738815763381902221)
              ·
                refine ⟨37918198777055911268213333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101115196738815763381902221 37918198777055911268213333)
                ·
                  refine ⟨444353891918623960174375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37918198777055911268213333 444353891918623960174375)
                  ·
                    rfl

theorem cell23_7788385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 8].length) (baseStart_7788385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788385 prefixEnd_7788385 := by exact prefixLift 7788385
  have htrace : WordTrace (prefixWord ++ tailWord_7788385) baseStart_7788385 baseEnd_7788385 := by
    simpa [prefixWord, tailWord_7788385, baseEnd_7788385] using wordTrace_append hprefix tailTrace_7788385
  have hstable : (prefixWord ++ tailWord_7788385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788385).length < 2 ^ (prefixWord ++ tailWord_7788385).sum := by decide
  have hdescent : baseEnd_7788385 < baseStart_7788385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788469 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_7788469 : Nat := 118140960795 + 7788469 * 2 ^ 59
def prefixEnd_7788469 : Nat := 4983230072969 + 3 ^ 40 * 7788469 * 2
def baseEnd_7788469 : Nat := 3999228159642593312918989

theorem tailTrace_7788469 : CollatzResearch.WordTrace tailWord_7788469 prefixEnd_7788469 3999228159642593312918989 := by
  unfold tailWord_7788469
  simp only [CollatzResearch.WordTrace]
  refine ⟨284068801620714452450496461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189379201080476301633664307 284068801620714452450496461)
  ·
    refine ⟨106525800607767919668936173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284068801620714452450496461 106525800607767919668936173)
    ·
      refine ⟨39947175227912969875851065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106525800607767919668936173 39947175227912969875851065)
      ·
        refine ⟨29960381420934727406888299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39947175227912969875851065 29960381420934727406888299)
        ·
          refine ⟨44940572131402091110332449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29960381420934727406888299 44940572131402091110332449)
          ·
            refine ⟨33705429098551568332749337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44940572131402091110332449 33705429098551568332749337)
            ·
              refine ⟨25279071823913676249562003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33705429098551568332749337 25279071823913676249562003)
              ·
                refine ⟨37918607735870514374343005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25279071823913676249562003 37918607735870514374343005)
                ·
                  refine ⟨14219477900951442890378627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37918607735870514374343005 14219477900951442890378627)
                  ·
                    refine ⟨21329216851427164335567941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14219477900951442890378627 21329216851427164335567941)
                    ·
                      refine ⟨3999228159642593312918989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21329216851427164335567941 3999228159642593312918989)
                      ·
                        rfl

theorem cell23_7788469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_7788469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788469 prefixEnd_7788469 := by exact prefixLift 7788469
  have htrace : WordTrace (prefixWord ++ tailWord_7788469) baseStart_7788469 baseEnd_7788469 := by
    simpa [prefixWord, tailWord_7788469, baseEnd_7788469] using wordTrace_append hprefix tailTrace_7788469
  have hstable : (prefixWord ++ tailWord_7788469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788469).length < 2 ^ (prefixWord ++ tailWord_7788469).sum := by decide
  have hdescent : baseEnd_7788469 < baseStart_7788469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788489 : List Nat := [1, 2, 1, 1, 2, 1, 2, 7, 1, 2, 3]
def baseStart_7788489 : Nat := 118140960795 + 7788489 * 2 ^ 59
def prefixEnd_7788489 : Nat := 4983230072969 + 3 ^ 40 * 7788489 * 2
def baseEnd_7788489 : Nat := 3999238429255683234668897

theorem tailTrace_7788489 : CollatzResearch.WordTrace tailWord_7788489 prefixEnd_7788489 3999238429255683234668897 := by
  unfold tailWord_7788489
  simp only [CollatzResearch.WordTrace]
  refine ⟨284069531080641995866224521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189379687387094663910816347 284069531080641995866224521)
  ·
    refine ⟨213052148310481496899668391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284069531080641995866224521 213052148310481496899668391)
    ·
      refine ⟨319578222465722245349502587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213052148310481496899668391 319578222465722245349502587)
      ·
        refine ⟨479367333698583368024253881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319578222465722245349502587 479367333698583368024253881)
        ·
          refine ⟨359525500273937526018190411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479367333698583368024253881 359525500273937526018190411)
          ·
            refine ⟨539288250410906289027285617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359525500273937526018190411 539288250410906289027285617)
            ·
              refine ⟨404466187808179716770464213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539288250410906289027285617 404466187808179716770464213)
              ·
                refine ⟨9479676276754212111807755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 404466187808179716770464213 9479676276754212111807755)
                ·
                  refine ⟨14219514415131318167711633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9479676276754212111807755 14219514415131318167711633)
                  ·
                    refine ⟨10664635811348488625783725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14219514415131318167711633 10664635811348488625783725)
                    ·
                      refine ⟨3999238429255683234668897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10664635811348488625783725 3999238429255683234668897)
                      ·
                        rfl

theorem cell23_7788489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 2, 3].length) (baseStart_7788489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788489 prefixEnd_7788489 := by exact prefixLift 7788489
  have htrace : WordTrace (prefixWord ++ tailWord_7788489) baseStart_7788489 baseEnd_7788489 := by
    simpa [prefixWord, tailWord_7788489, baseEnd_7788489] using wordTrace_append hprefix tailTrace_7788489
  have hstable : (prefixWord ++ tailWord_7788489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788489).length < 2 ^ (prefixWord ++ tailWord_7788489).sum := by decide
  have hdescent : baseEnd_7788489 < baseStart_7788489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788492 : List Nat := [2, 2, 1, 4, 1, 3, 10]
def baseStart_7788492 : Nat := 118140960795 + 7788492 * 2 ^ 59
def prefixEnd_7788492 : Nat := 4983230072969 + 3 ^ 40 * 7788492 * 2
def baseEnd_7788492 : Nat := 49373332959230206455943

theorem tailTrace_7788492 : CollatzResearch.WordTrace tailWord_7788492 prefixEnd_7788492 49373332959230206455943 := by
  unfold tailWord_7788492
  simp only [CollatzResearch.WordTrace]
  refine ⟨142034820249815563689291865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189379760333087418252389153 142034820249815563689291865)
  ·
    refine ⟨106526115187361672766968899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142034820249815563689291865 106526115187361672766968899)
    ·
      refine ⟨159789172781042509150453349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106526115187361672766968899 159789172781042509150453349)
      ·
        refine ⟨29960469896445470465710003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159789172781042509150453349 29960469896445470465710003)
        ·
          refine ⟨44940704844668205698565005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29960469896445470465710003 44940704844668205698565005)
          ·
            refine ⟨16852764316750577136961877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44940704844668205698565005 16852764316750577136961877)
            ·
              refine ⟨49373332959230206455943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16852764316750577136961877 49373332959230206455943)
              ·
                rfl

theorem cell23_7788492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 10].length) (baseStart_7788492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788492 prefixEnd_7788492 := by exact prefixLift 7788492
  have htrace : WordTrace (prefixWord ++ tailWord_7788492) baseStart_7788492 baseEnd_7788492 := by
    simpa [prefixWord, tailWord_7788492, baseEnd_7788492] using wordTrace_append hprefix tailTrace_7788492
  have hstable : (prefixWord ++ tailWord_7788492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788492).length < 2 ^ (prefixWord ++ tailWord_7788492).sum := by decide
  have hdescent : baseEnd_7788492 < baseStart_7788492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788503 : List Nat := [1, 1, 3, 2, 1, 1, 3, 6, 1, 2, 2]
def baseStart_7788503 : Nat := 118140960795 + 7788503 * 2 ^ 59
def prefixEnd_7788503 : Nat := 4983230072969 + 3 ^ 40 * 7788503 * 2
def baseEnd_7788503 : Nat := 3999245617984846179893833

theorem tailTrace_7788503 : CollatzResearch.WordTrace tailWord_7788503 prefixEnd_7788503 3999245617984846179893833 := by
  unfold tailWord_7788503
  simp only [CollatzResearch.WordTrace]
  refine ⟨284070041702591276257234163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189380027801727517504822775 284070041702591276257234163)
  ·
    refine ⟨426105062553886914385851245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284070041702591276257234163 426105062553886914385851245)
    ·
      refine ⟨159789398457707592894694217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426105062553886914385851245 159789398457707592894694217)
      ·
        refine ⟨119842048843280694671020663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159789398457707592894694217 119842048843280694671020663)
        ·
          refine ⟨179763073264921042006530995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119842048843280694671020663 179763073264921042006530995)
          ·
            refine ⟨269644609897381563009796493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179763073264921042006530995 269644609897381563009796493)
            ·
              refine ⟨101116728711518086128673685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269644609897381563009796493 101116728711518086128673685)
              ·
                refine ⟨4739846658352410287281579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101116728711518086128673685 4739846658352410287281579)
                ·
                  refine ⟨7109769987528615430922369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4739846658352410287281579 7109769987528615430922369)
                  ·
                    refine ⟨5332327490646461573191777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7109769987528615430922369 5332327490646461573191777)
                    ·
                      refine ⟨3999245617984846179893833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5332327490646461573191777 3999245617984846179893833)
                      ·
                        rfl

theorem cell23_7788503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_7788503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788503 prefixEnd_7788503 := by exact prefixLift 7788503
  have htrace : WordTrace (prefixWord ++ tailWord_7788503) baseStart_7788503 baseEnd_7788503 := by
    simpa [prefixWord, tailWord_7788503, baseEnd_7788503] using wordTrace_append hprefix tailTrace_7788503
  have hstable : (prefixWord ++ tailWord_7788503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788503).length < 2 ^ (prefixWord ++ tailWord_7788503).sum := by decide
  have hdescent : baseEnd_7788503 < baseStart_7788503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788526 : List Nat := [4, 1, 2, 1, 3, 3, 2, 7]
def baseStart_7788526 : Nat := 118140960795 + 7788526 * 2 ^ 59
def prefixEnd_7788526 : Nat := 4983230072969 + 3 ^ 40 * 7788526 * 2
def baseEnd_7788526 : Nat := 148120645482959244070601

theorem tailTrace_7788526 : CollatzResearch.WordTrace tailWord_7788526 prefixEnd_7788526 148120645482959244070601 := by
  unfold tailWord_7788526
  simp only [CollatzResearch.WordTrace]
  refine ⟨35508860072688493898165179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189380587054338634123547621 35508860072688493898165179)
  ·
    refine ⟨53263290109032740847247769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35508860072688493898165179 53263290109032740847247769)
    ·
      refine ⟨39947467581774555635435827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53263290109032740847247769 39947467581774555635435827)
      ·
        refine ⟨59921201372661833453153741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39947467581774555635435827 59921201372661833453153741)
        ·
          refine ⟨22470450514748187544932653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59921201372661833453153741 22470450514748187544932653)
          ·
            refine ⟨8426418943030570329349745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22470450514748187544932653 8426418943030570329349745)
            ·
              refine ⟨6319814207272927747012309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8426418943030570329349745 6319814207272927747012309)
              ·
                refine ⟨148120645482959244070601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6319814207272927747012309 148120645482959244070601)
                ·
                  rfl

theorem cell23_7788526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_7788526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788526 prefixEnd_7788526 := by exact prefixLift 7788526
  have htrace : WordTrace (prefixWord ++ tailWord_7788526) baseStart_7788526 baseEnd_7788526 := by
    simpa [prefixWord, tailWord_7788526, baseEnd_7788526] using wordTrace_append hprefix tailTrace_7788526
  have hstable : (prefixWord ++ tailWord_7788526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788526).length < 2 ^ (prefixWord ++ tailWord_7788526).sum := by decide
  have hdescent : baseEnd_7788526 < baseStart_7788526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788564 : List Nat := [2, 4, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_7788564 : Nat := 118140960795 + 7788564 * 2 ^ 59
def prefixEnd_7788564 : Nat := 4983230072969 + 3 ^ 40 * 7788564 * 2
def baseEnd_7788564 : Nat := 1333092313434923480410351

theorem tailTrace_7788564 : CollatzResearch.WordTrace tailWord_7788564 prefixEnd_7788564 1333092313434923480410351 := by
  unfold tailWord_7788564
  simp only [CollatzResearch.WordTrace]
  refine ⟨142036133277685141837602373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189381511036913522450136497 142036133277685141837602373)
  ·
    refine ⟨26631774989565964094550445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142036133277685141837602373 26631774989565964094550445)
    ·
      refine ⟨9986915621087236535456417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26631774989565964094550445 9986915621087236535456417)
      ·
        refine ⟨7490186715815427401592313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9986915621087236535456417 7490186715815427401592313)
        ·
          refine ⟨5617640036861570551194235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7490186715815427401592313 5617640036861570551194235)
          ·
            refine ⟨8426460055292355826791353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5617640036861570551194235 8426460055292355826791353)
            ·
              refine ⟨6319845041469266870093515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8426460055292355826791353 6319845041469266870093515)
              ·
                refine ⟨9479767562203900305140273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6319845041469266870093515 9479767562203900305140273)
                ·
                  refine ⟨7109825671652925228855205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9479767562203900305140273 7109825671652925228855205)
                  ·
                    refine ⟨1333092313434923480410351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7109825671652925228855205 1333092313434923480410351)
                    ·
                      rfl

theorem cell23_7788564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_7788564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788564 prefixEnd_7788564 := by exact prefixLift 7788564
  have htrace : WordTrace (prefixWord ++ tailWord_7788564) baseStart_7788564 baseEnd_7788564 := by
    simpa [prefixWord, tailWord_7788564, baseEnd_7788564] using wordTrace_append hprefix tailTrace_7788564
  have hstable : (prefixWord ++ tailWord_7788564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788564).length < 2 ^ (prefixWord ++ tailWord_7788564).sum := by decide
  have hdescent : baseEnd_7788564 < baseStart_7788564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788570 : List Nat := [3, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3]
def baseStart_7788570 : Nat := 118140960795 + 7788570 * 2 ^ 59
def prefixEnd_7788570 : Nat := 4983230072969 + 3 ^ 40 * 7788570 * 2
def baseEnd_7788570 : Nat := 3999280021188697417756025

theorem tailTrace_7788570 : CollatzResearch.WordTrace tailWord_7788570 prefixEnd_7788570 3999280021188697417756025 := by
  unfold tailWord_7788570
  simp only [CollatzResearch.WordTrace]
  refine ⟨71018121348337136674980791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189381656928899031133282109 71018121348337136674980791)
  ·
    refine ⟨106527182022505705012471187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71018121348337136674980791 106527182022505705012471187)
    ·
      refine ⟨159790773033758557518706781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106527182022505705012471187 159790773033758557518706781)
      ·
        refine ⟨59921539887659459069515043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159790773033758557518706781 59921539887659459069515043)
        ·
          refine ⟨89882309831489188604272565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59921539887659459069515043 89882309831489188604272565)
          ·
            refine ⟨8426466546702111431650553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89882309831489188604272565 8426466546702111431650553)
            ·
              refine ⟨6319849910026583573737915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8426466546702111431650553 6319849910026583573737915)
              ·
                refine ⟨9479774865039875360606873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6319849910026583573737915 9479774865039875360606873)
                ·
                  refine ⟨7109831148779906520455155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9479774865039875360606873 7109831148779906520455155)
                  ·
                    refine ⟨10664746723169859780682733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7109831148779906520455155 10664746723169859780682733)
                    ·
                      refine ⟨3999280021188697417756025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10664746723169859780682733 3999280021188697417756025)
                      ·
                        rfl

theorem cell23_7788570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_7788570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788570 prefixEnd_7788570 := by exact prefixLift 7788570
  have htrace : WordTrace (prefixWord ++ tailWord_7788570) baseStart_7788570 baseEnd_7788570 := by
    simpa [prefixWord, tailWord_7788570, baseEnd_7788570] using wordTrace_append hprefix tailTrace_7788570
  have hstable : (prefixWord ++ tailWord_7788570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788570).length < 2 ^ (prefixWord ++ tailWord_7788570).sum := by decide
  have hdescent : baseEnd_7788570 < baseStart_7788570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788649 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 1, 3, 4]
def baseStart_7788649 : Nat := 118140960795 + 7788649 * 2 ^ 59
def prefixEnd_7788649 : Nat := 4983230072969 + 3 ^ 40 * 7788649 * 2
def baseEnd_7788649 : Nat := 3999320586160402608668161

theorem tailTrace_7788649 : CollatzResearch.WordTrace tailWord_7788649 prefixEnd_7788649 3999320586160402608668161 := by
  unfold tailWord_7788649
  simp only [CollatzResearch.WordTrace]
  refine ⟨284075366760062343192049001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189383577840041562128032667 284075366760062343192049001)
  ·
    refine ⟨213056525070046757394036751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284075366760062343192049001 213056525070046757394036751)
    ·
      refine ⟨319584787605070136091055127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213056525070046757394036751 319584787605070136091055127)
      ·
        refine ⟨479377181407605204136582691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319584787605070136091055127 479377181407605204136582691)
        ·
          refine ⟨719065772111407806204874037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479377181407605204136582691 719065772111407806204874037)
          ·
            refine ⟨67412416135444481831706941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 719065772111407806204874037 67412416135444481831706941)
            ·
              refine ⟨25279656050791680686890103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67412416135444481831706941 25279656050791680686890103)
              ·
                refine ⟨37919484076187521030335155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25279656050791680686890103 37919484076187521030335155)
                ·
                  refine ⟨56879226114281281545502733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37919484076187521030335155 56879226114281281545502733)
                  ·
                    refine ⟨21329709792855480579563525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56879226114281281545502733 21329709792855480579563525)
                    ·
                      refine ⟨3999320586160402608668161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21329709792855480579563525 3999320586160402608668161)
                      ·
                        rfl

theorem cell23_7788649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_7788649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788649 prefixEnd_7788649 := by exact prefixLift 7788649
  have htrace : WordTrace (prefixWord ++ tailWord_7788649) baseStart_7788649 baseEnd_7788649 := by
    simpa [prefixWord, tailWord_7788649, baseEnd_7788649] using wordTrace_append hprefix tailTrace_7788649
  have hstable : (prefixWord ++ tailWord_7788649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788649).length < 2 ^ (prefixWord ++ tailWord_7788649).sum := by decide
  have hdescent : baseEnd_7788649 < baseStart_7788649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788699 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 3]
def baseStart_7788699 : Nat := 118140960795 + 7788699 * 2 ^ 59
def prefixEnd_7788699 : Nat := 4983230072969 + 3 ^ 40 * 7788699 * 2
def baseEnd_7788699 : Nat := 3999346260193127413042931

theorem tailTrace_7788699 : CollatzResearch.WordTrace tailWord_7788699 prefixEnd_7788699 3999346260193127413042931 := by
  unfold tailWord_7788699
  simp only [CollatzResearch.WordTrace]
  refine ⟨284077190409881201731369151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189384793606587467820912767 284077190409881201731369151)
  ·
    refine ⟨426115785614821802597053727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284077190409881201731369151 426115785614821802597053727)
    ·
      refine ⟨639173678422232703895580591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426115785614821802597053727 639173678422232703895580591)
      ·
        refine ⟨958760517633349055843370887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639173678422232703895580591 958760517633349055843370887)
        ·
          refine ⟨1438140776450023583765056331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958760517633349055843370887 1438140776450023583765056331)
          ·
            refine ⟨2157211164675035375647584497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438140776450023583765056331 2157211164675035375647584497)
            ·
              refine ⟨1617908373506276531735688373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2157211164675035375647584497 1617908373506276531735688373)
              ·
                refine ⟨151678910016213424850220785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1617908373506276531735688373 151678910016213424850220785)
                ·
                  refine ⟨113759182512160068637665589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151678910016213424850220785 113759182512160068637665589)
                  ·
                    refine ⟨10664923360515006434781149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113759182512160068637665589 10664923360515006434781149)
                    ·
                      refine ⟨3999346260193127413042931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10664923360515006434781149 3999346260193127413042931)
                      ·
                        rfl

theorem cell23_7788699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 3].length) (baseStart_7788699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788699 prefixEnd_7788699 := by exact prefixLift 7788699
  have htrace : WordTrace (prefixWord ++ tailWord_7788699) baseStart_7788699 baseEnd_7788699 := by
    simpa [prefixWord, tailWord_7788699, baseEnd_7788699] using wordTrace_append hprefix tailTrace_7788699
  have hstable : (prefixWord ++ tailWord_7788699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788699).length < 2 ^ (prefixWord ++ tailWord_7788699).sum := by decide
  have hdescent : baseEnd_7788699 < baseStart_7788699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788706 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 8]
def baseStart_7788706 : Nat := 118140960795 + 7788706 * 2 ^ 59
def prefixEnd_7788706 : Nat := 4983230072969 + 3 ^ 40 * 7788706 * 2
def baseEnd_7788706 : Nat := 444372206061967653961711

theorem tailTrace_7788706 : CollatzResearch.WordTrace tailWord_7788706 prefixEnd_7788706 444372206061967653961711 := by
  unfold tailWord_7788706
  simp only [CollatzResearch.WordTrace]
  refine ⟨71019361430213960481718493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189384963813903894617915981 71019361430213960481718493)
  ·
    refine ⟨26632260536330235180644435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71019361430213960481718493 26632260536330235180644435)
    ·
      refine ⟨39948390804495352770966653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26632260536330235180644435 39948390804495352770966653)
      ·
        refine ⟨14980646551685757289112495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39948390804495352770966653 14980646551685757289112495)
        ·
          refine ⟨22470969827528635933668743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14980646551685757289112495 22470969827528635933668743)
          ·
            refine ⟨33706454741292953900503115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22470969827528635933668743 33706454741292953900503115)
            ·
              refine ⟨50559682111939430850754673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33706454741292953900503115 50559682111939430850754673)
              ·
                refine ⟨37919761583954573138066005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50559682111939430850754673 37919761583954573138066005)
                ·
                  refine ⟨444372206061967653961711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37919761583954573138066005 444372206061967653961711)
                  ·
                    rfl

theorem cell23_7788706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_7788706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788706 prefixEnd_7788706 := by exact prefixLift 7788706
  have htrace : WordTrace (prefixWord ++ tailWord_7788706) baseStart_7788706 baseEnd_7788706 := by
    simpa [prefixWord, tailWord_7788706, baseEnd_7788706] using wordTrace_append hprefix tailTrace_7788706
  have hstable : (prefixWord ++ tailWord_7788706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788706).length < 2 ^ (prefixWord ++ tailWord_7788706).sum := by decide
  have hdescent : baseEnd_7788706 < baseStart_7788706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788719 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 5, 5]
def baseStart_7788719 : Nat := 118140960795 + 7788719 * 2 ^ 59
def prefixEnd_7788719 : Nat := 4983230072969 + 3 ^ 40 * 7788719 * 2
def baseEnd_7788719 : Nat := 1333118843268739111597613

theorem tailTrace_7788719 : CollatzResearch.WordTrace tailWord_7788719 prefixEnd_7788719 1333118843268739111597613 := by
  unfold tailWord_7788719
  simp only [CollatzResearch.WordTrace]
  refine ⟨284077919869808745147097211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189385279913205830098064807 284077919869808745147097211)
  ·
    refine ⟨426116879804713117720645817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284077919869808745147097211 426116879804713117720645817)
    ·
      refine ⟨319587659853534838290484363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426116879804713117720645817 319587659853534838290484363)
      ·
        refine ⟨479381489780302257435726545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319587659853534838290484363 479381489780302257435726545)
        ·
          refine ⟨359536117335226693076794909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479381489780302257435726545 359536117335226693076794909)
          ·
            refine ⟨134826044000710009903798091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359536117335226693076794909 134826044000710009903798091)
            ·
              refine ⟨202239066001065014855697137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134826044000710009903798091 202239066001065014855697137)
              ·
                refine ⟨151679299500798761141772853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202239066001065014855697137 151679299500798761141772853)
                ·
                  refine ⟨14219934328199883857041205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151679299500798761141772853 14219934328199883857041205)
                  ·
                    refine ⟨1333118843268739111597613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14219934328199883857041205 1333118843268739111597613)
                    ·
                      rfl

theorem cell23_7788719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 5].length) (baseStart_7788719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788719 prefixEnd_7788719 := by exact prefixLift 7788719
  have htrace : WordTrace (prefixWord ++ tailWord_7788719) baseStart_7788719 baseEnd_7788719 := by
    simpa [prefixWord, tailWord_7788719, baseEnd_7788719] using wordTrace_append hprefix tailTrace_7788719
  have hstable : (prefixWord ++ tailWord_7788719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788719).length < 2 ^ (prefixWord ++ tailWord_7788719).sum := by decide
  have hdescent : baseEnd_7788719 < baseStart_7788719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788740 : List Nat := [2, 3, 3, 1, 2, 3, 2, 1, 6]
def baseStart_7788740 : Nat := 118140960795 + 7788740 * 2 ^ 59
def prefixEnd_7788740 : Nat := 4983230072969 + 3 ^ 40 * 7788740 * 2
def baseEnd_7788740 : Nat := 444374145877773528070027

theorem tailTrace_7788740 : CollatzResearch.WordTrace tailWord_7788740 prefixEnd_7788740 444374145877773528070027 := by
  unfold tailWord_7788740
  simp only [CollatzResearch.WordTrace]
  refine ⟨142039342901366332866805837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189385790535155110489074449 142039342901366332866805837)
  ·
    refine ⟨53264753588012374825052189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142039342901366332866805837 53264753588012374825052189)
    ·
      refine ⟨19974282595504640559394571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53264753588012374825052189 19974282595504640559394571)
      ·
        refine ⟨29961423893256960839091857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19974282595504640559394571 29961423893256960839091857)
        ·
          refine ⟨22471067919942720629318893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29961423893256960839091857 22471067919942720629318893)
          ·
            refine ⟨8426650469978520235994585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22471067919942720629318893 8426650469978520235994585)
            ·
              refine ⟨6319987852483890176995939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8426650469978520235994585 6319987852483890176995939)
              ·
                refine ⟨9479981778725835265493909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6319987852483890176995939 9479981778725835265493909)
                ·
                  refine ⟨444374145877773528070027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9479981778725835265493909 444374145877773528070027)
                  ·
                    rfl

theorem cell23_7788740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_7788740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788740 prefixEnd_7788740 := by exact prefixLift 7788740
  have htrace : WordTrace (prefixWord ++ tailWord_7788740) baseStart_7788740 baseEnd_7788740 := by
    simpa [prefixWord, tailWord_7788740, baseEnd_7788740] using wordTrace_append hprefix tailTrace_7788740
  have hstable : (prefixWord ++ tailWord_7788740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788740).length < 2 ^ (prefixWord ++ tailWord_7788740).sum := by decide
  have hdescent : baseEnd_7788740 < baseStart_7788740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788760 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 2, 3, 2]
def baseStart_7788760 : Nat := 118140960795 + 7788760 * 2 ^ 59
def prefixEnd_7788760 : Nat := 4983230072969 + 3 ^ 40 * 7788760 * 2
def baseEnd_7788760 : Nat := 3999377582513051674380151

theorem tailTrace_7788760 : CollatzResearch.WordTrace tailWord_7788760 prefixEnd_7788760 3999377582513051674380151 := by
  unfold tailWord_7788760
  simp only [CollatzResearch.WordTrace]
  refine ⟨142039707631330104574669867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189386276841773472766226489 142039707631330104574669867)
  ·
    refine ⟨213059561446995156862004801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142039707631330104574669867 213059561446995156862004801)
    ·
      refine ⟨159794671085246367646503601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213059561446995156862004801 159794671085246367646503601)
      ·
        refine ⟨119846003313934775734877701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159794671085246367646503601 119846003313934775734877701)
        ·
          refine ⟨22471125621362770450289569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119846003313934775734877701 22471125621362770450289569)
          ·
            refine ⟨16853344216022077837717177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22471125621362770450289569 16853344216022077837717177)
            ·
              refine ⟨12640008162016558378287883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16853344216022077837717177 12640008162016558378287883)
              ·
                refine ⟨18960012243024837567431825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12640008162016558378287883 18960012243024837567431825)
                ·
                  refine ⟨14220009182268628175573869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18960012243024837567431825 14220009182268628175573869)
                  ·
                    refine ⟨5332503443350735565840201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14220009182268628175573869 5332503443350735565840201)
                    ·
                      refine ⟨3999377582513051674380151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5332503443350735565840201 3999377582513051674380151)
                      ·
                        rfl

theorem cell23_7788760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_7788760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788760 prefixEnd_7788760 := by exact prefixLift 7788760
  have htrace : WordTrace (prefixWord ++ tailWord_7788760) baseStart_7788760 baseEnd_7788760 := by
    simpa [prefixWord, tailWord_7788760, baseEnd_7788760] using wordTrace_append hprefix tailTrace_7788760
  have hstable : (prefixWord ++ tailWord_7788760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788760).length < 2 ^ (prefixWord ++ tailWord_7788760).sum := by decide
  have hdescent : baseEnd_7788760 < baseStart_7788760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788783 : List Nat := [1, 1, 2, 1, 6, 1, 1, 4, 2, 4]
def baseStart_7788783 : Nat := 118140960795 + 7788783 * 2 ^ 59
def prefixEnd_7788783 : Nat := 4983230072969 + 3 ^ 40 * 7788783 * 2
def baseEnd_7788783 : Nat := 1333129797522701694797515

theorem tailTrace_7788783 : CollatzResearch.WordTrace tailWord_7788783 prefixEnd_7788783 1333129797522701694797515 := by
  unfold tailWord_7788783
  simp only [CollatzResearch.WordTrace]
  refine ⟨284080254141576884077427003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189386836094384589384951335 284080254141576884077427003)
  ·
    refine ⟨426120381212365326116140505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284080254141576884077427003 426120381212365326116140505)
    ·
      refine ⟨319590285909273994587105379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426120381212365326116140505 319590285909273994587105379)
      ·
        refine ⟨479385428863910991880658069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319590285909273994587105379 479385428863910991880658069)
        ·
          refine ⟨22471191977995827744405847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 479385428863910991880658069 22471191977995827744405847)
          ·
            refine ⟨33706787966993741616608771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22471191977995827744405847 33706787966993741616608771)
            ·
              refine ⟨50560181950490612424913157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33706787966993741616608771 50560181950490612424913157)
              ·
                refine ⟨9480034115716989829671217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50560181950490612424913157 9480034115716989829671217)
                ·
                  refine ⟨7110025586787742372253413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9480034115716989829671217 7110025586787742372253413)
                  ·
                    refine ⟨1333129797522701694797515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7110025586787742372253413 1333129797522701694797515)
                    ·
                      rfl

theorem cell23_7788783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 4].length) (baseStart_7788783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788783 prefixEnd_7788783 := by exact prefixLift 7788783
  have htrace : WordTrace (prefixWord ++ tailWord_7788783) baseStart_7788783 baseEnd_7788783 := by
    simpa [prefixWord, tailWord_7788783, baseEnd_7788783] using wordTrace_append hprefix tailTrace_7788783
  have hstable : (prefixWord ++ tailWord_7788783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788783).length < 2 ^ (prefixWord ++ tailWord_7788783).sum := by decide
  have hdescent : baseEnd_7788783 < baseStart_7788783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788796 : List Nat := [2, 2, 2, 1, 4, 1, 3, 8]
def baseStart_7788796 : Nat := 118140960795 + 7788796 * 2 ^ 59
def prefixEnd_7788796 : Nat := 4983230072969 + 3 ^ 40 * 7788796 * 2
def baseEnd_7788796 : Nat := 148125780289504204945555

theorem tailTrace_7788796 : CollatzResearch.WordTrace tailWord_7788796 prefixEnd_7788796 148125780289504204945555 := by
  unfold tailWord_7788796
  simp only [CollatzResearch.WordTrace]
  refine ⟨142040364145264893648825121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189387152193686524865100161 142040364145264893648825121)
  ·
    refine ⟨106530273108948670236618841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142040364145264893648825121 106530273108948670236618841)
    ·
      refine ⟨79897704831711502677464131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106530273108948670236618841 79897704831711502677464131)
      ·
        refine ⟨119846557247567254016196197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79897704831711502677464131 119846557247567254016196197)
        ·
          refine ⟨22471229483918860128036787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119846557247567254016196197 22471229483918860128036787)
          ·
            refine ⟨33706844225878290192055181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22471229483918860128036787 33706844225878290192055181)
            ·
              refine ⟨12640066584704358822020693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33706844225878290192055181 12640066584704358822020693)
              ·
                refine ⟨148125780289504204945555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12640066584704358822020693 148125780289504204945555)
                ·
                  rfl

theorem cell23_7788796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 8].length) (baseStart_7788796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788796 prefixEnd_7788796 := by exact prefixLift 7788796
  have htrace : WordTrace (prefixWord ++ tailWord_7788796) baseStart_7788796 baseEnd_7788796 := by
    simpa [prefixWord, tailWord_7788796, baseEnd_7788796] using wordTrace_append hprefix tailTrace_7788796
  have hstable : (prefixWord ++ tailWord_7788796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788796).length < 2 ^ (prefixWord ++ tailWord_7788796).sum := by decide
  have hdescent : baseEnd_7788796 < baseStart_7788796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788823 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 3]
def baseStart_7788823 : Nat := 118140960795 + 7788823 * 2 ^ 59
def prefixEnd_7788823 : Nat := 4983230072969 + 3 ^ 40 * 7788823 * 2
def baseEnd_7788823 : Nat := 3999409931794284927892361

theorem tailTrace_7788823 : CollatzResearch.WordTrace tailWord_7788823 prefixEnd_7788823 3999409931794284927892361 := by
  unfold tailWord_7788823
  simp only [CollatzResearch.WordTrace]
  refine ⟨284081713061431970908883123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189387808707621313939255415 284081713061431970908883123)
  ·
    refine ⟨426122569592147956363324685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284081713061431970908883123 426122569592147956363324685)
    ·
      refine ⟨159795963597055483636246757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426122569592147956363324685 159795963597055483636246757)
      ·
        refine ⟨29961743174447903181796267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159795963597055483636246757 29961743174447903181796267)
        ·
          refine ⟨44942614761671854772694401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29961743174447903181796267 44942614761671854772694401)
          ·
            refine ⟨33706961071253891079520801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44942614761671854772694401 33706961071253891079520801)
            ·
              refine ⟨25280220803440418309640601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33706961071253891079520801 25280220803440418309640601)
              ·
                refine ⟨18960165602580313732230451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25280220803440418309640601 18960165602580313732230451)
                ·
                  refine ⟨28440248403870470598345677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18960165602580313732230451 28440248403870470598345677)
                  ·
                    refine ⟨10665093151451426474379629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28440248403870470598345677 10665093151451426474379629)
                    ·
                      refine ⟨3999409931794284927892361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10665093151451426474379629 3999409931794284927892361)
                      ·
                        rfl

theorem cell23_7788823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_7788823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788823 prefixEnd_7788823 := by exact prefixLift 7788823
  have htrace : WordTrace (prefixWord ++ tailWord_7788823) baseStart_7788823 baseEnd_7788823 := by
    simpa [prefixWord, tailWord_7788823, baseEnd_7788823] using wordTrace_append hprefix tailTrace_7788823
  have hstable : (prefixWord ++ tailWord_7788823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788823).length < 2 ^ (prefixWord ++ tailWord_7788823).sum := by decide
  have hdescent : baseEnd_7788823 < baseStart_7788823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788856 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 2, 6]
def baseStart_7788856 : Nat := 118140960795 + 7788856 * 2 ^ 59
def prefixEnd_7788856 : Nat := 4983230072969 + 3 ^ 40 * 7788856 * 2
def baseEnd_7788856 : Nat := 1333142292218627766259903

theorem tailTrace_7788856 : CollatzResearch.WordTrace tailWord_7788856 prefixEnd_7788856 1333142292218627766259903 := by
  unfold tailWord_7788856
  simp only [CollatzResearch.WordTrace]
  refine ⟨142041458335156208772417211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189388611113541611696556281 142041458335156208772417211)
  ·
    refine ⟨213062187502734313158625817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142041458335156208772417211 213062187502734313158625817)
    ·
      refine ⟨159796640627050734868969363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213062187502734313158625817 159796640627050734868969363)
      ·
        refine ⟨239694960940576102303454045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159796640627050734868969363 239694960940576102303454045)
        ·
          refine ⟨89885610352716038363795267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239694960940576102303454045 89885610352716038363795267)
          ·
            refine ⟨134828415529074057545692901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89885610352716038363795267 134828415529074057545692901)
            ·
              refine ⟨25280327911701385789817419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134828415529074057545692901 25280327911701385789817419)
              ·
                refine ⟨37920491867552078684726129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25280327911701385789817419 37920491867552078684726129)
                ·
                  refine ⟨28440368900664059013544597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37920491867552078684726129 28440368900664059013544597)
                  ·
                    refine ⟨1333142292218627766259903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28440368900664059013544597 1333142292218627766259903)
                    ·
                      rfl

theorem cell23_7788856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_7788856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788856 prefixEnd_7788856 := by exact prefixLift 7788856
  have htrace : WordTrace (prefixWord ++ tailWord_7788856) baseStart_7788856 baseEnd_7788856 := by
    simpa [prefixWord, tailWord_7788856, baseEnd_7788856] using wordTrace_append hprefix tailTrace_7788856
  have hstable : (prefixWord ++ tailWord_7788856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788856).length < 2 ^ (prefixWord ++ tailWord_7788856).sum := by decide
  have hdescent : baseEnd_7788856 < baseStart_7788856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788880 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 4, 2, 2]
def baseStart_7788880 : Nat := 118140960795 + 7788880 * 2 ^ 59
def prefixEnd_7788880 : Nat := 4983230072969 + 3 ^ 40 * 7788880 * 2
def baseEnd_7788880 : Nat := 3999439200191591204879599

theorem tailTrace_7788880 : CollatzResearch.WordTrace tailWord_7788880 prefixEnd_7788880 3999439200191591204879599 := by
  unfold tailWord_7788880
  simp only [CollatzResearch.WordTrace]
  refine ⟨142041896011112734821854047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189389194681483646429138729 142041896011112734821854047)
  ·
    refine ⟨213062844016669102232781071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142041896011112734821854047 213062844016669102232781071)
    ·
      refine ⟨319594266025003653349171607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213062844016669102232781071 319594266025003653349171607)
      ·
        refine ⟨479391399037505480023757411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319594266025003653349171607 479391399037505480023757411)
        ·
          refine ⟨719087098556258220035636117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479391399037505480023757411 719087098556258220035636117)
          ·
            refine ⟨33707207744824604064170443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 719087098556258220035636117 33707207744824604064170443)
            ·
              refine ⟨50560811617236906096255665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33707207744824604064170443 50560811617236906096255665)
              ·
                refine ⟨37920608712927679572191749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50560811617236906096255665 37920608712927679572191749)
                ·
                  refine ⟨7110114133673939919785953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37920608712927679572191749 7110114133673939919785953)
                  ·
                    refine ⟨5332585600255454939839465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7110114133673939919785953 5332585600255454939839465)
                    ·
                      refine ⟨3999439200191591204879599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5332585600255454939839465 3999439200191591204879599)
                      ·
                        rfl

theorem cell23_7788880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 4, 2, 2].length) (baseStart_7788880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788880 prefixEnd_7788880 := by exact prefixLift 7788880
  have htrace : WordTrace (prefixWord ++ tailWord_7788880) baseStart_7788880 baseEnd_7788880 := by
    simpa [prefixWord, tailWord_7788880, baseEnd_7788880] using wordTrace_append hprefix tailTrace_7788880
  have hstable : (prefixWord ++ tailWord_7788880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788880).length < 2 ^ (prefixWord ++ tailWord_7788880).sum := by decide
  have hdescent : baseEnd_7788880 < baseStart_7788880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788903 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 7]
def baseStart_7788903 : Nat := 118140960795 + 7788903 * 2 ^ 59
def prefixEnd_7788903 : Nat := 4983230072969 + 3 ^ 40 * 7788903 * 2
def baseEnd_7788903 : Nat := 444383445582960512765777

theorem tailTrace_7788903 : CollatzResearch.WordTrace tailWord_7788903 prefixEnd_7788903 444383445582960512765777 := by
  unfold tailWord_7788903
  simp only [CollatzResearch.WordTrace]
  refine ⟨284084630901142144571795363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189389753934094763047863575 284084630901142144571795363)
  ·
    refine ⟨426126946351713216857693045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284084630901142144571795363 426126946351713216857693045)
    ·
      refine ⟨39949401220473114080408723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 426126946351713216857693045 39949401220473114080408723)
      ·
        refine ⟨59924101830709671120613085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39949401220473114080408723 59924101830709671120613085)
        ·
          refine ⟨22471538186516126670229907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59924101830709671120613085 22471538186516126670229907)
          ·
            refine ⟨33707307279774190005344861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22471538186516126670229907 33707307279774190005344861)
            ·
              refine ⟨12640240229915321252004323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33707307279774190005344861 12640240229915321252004323)
              ·
                refine ⟨18960360344872981878006485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12640240229915321252004323 18960360344872981878006485)
                ·
                  refine ⟨444383445582960512765777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18960360344872981878006485 444383445582960512765777)
                  ·
                    rfl

theorem cell23_7788903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 7].length) (baseStart_7788903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788903 prefixEnd_7788903 := by exact prefixLift 7788903
  have htrace : WordTrace (prefixWord ++ tailWord_7788903) baseStart_7788903 baseEnd_7788903 := by
    simpa [prefixWord, tailWord_7788903, baseEnd_7788903] using wordTrace_append hprefix tailTrace_7788903
  have hstable : (prefixWord ++ tailWord_7788903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788903).length < 2 ^ (prefixWord ++ tailWord_7788903).sum := by decide
  have hdescent : baseEnd_7788903 < baseStart_7788903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788914 : List Nat := [3, 2, 1, 2, 1, 3, 4, 1, 2, 2, 2]
def baseStart_7788914 : Nat := 118140960795 + 7788914 * 2 ^ 59
def prefixEnd_7788914 : Nat := 4983230072969 + 3 ^ 40 * 7788914 * 2
def baseEnd_7788914 : Nat := 3999456658533844071854443

theorem tailTrace_7788914 : CollatzResearch.WordTrace tailWord_7788914 prefixEnd_7788914 3999456658533844071854443 := by
  unfold tailWord_7788914
  simp only [CollatzResearch.WordTrace]
  refine ⟨71021258026025573362611449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189390021402734862300297197 71021258026025573362611449)
  ·
    refine ⟨53265943519519180021958587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71021258026025573362611449 53265943519519180021958587)
    ·
      refine ⟨79898915279278770032937881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53265943519519180021958587 79898915279278770032937881)
      ·
        refine ⟨59924186459459077524703411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79898915279278770032937881 59924186459459077524703411)
        ·
          refine ⟨89886279689188616287055117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59924186459459077524703411 89886279689188616287055117)
          ·
            refine ⟨33707354883445731107645669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89886279689188616287055117 33707354883445731107645669)
            ·
              refine ⟨6320129040646074582683563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33707354883445731107645669 6320129040646074582683563)
              ·
                refine ⟨9480193560969111874025345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6320129040646074582683563 9480193560969111874025345)
                ·
                  refine ⟨7110145170726833905519009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9480193560969111874025345 7110145170726833905519009)
                  ·
                    refine ⟨5332608878045125429139257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7110145170726833905519009 5332608878045125429139257)
                    ·
                      refine ⟨3999456658533844071854443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5332608878045125429139257 3999456658533844071854443)
                      ·
                        rfl

theorem cell23_7788914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_7788914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788914 prefixEnd_7788914 := by exact prefixLift 7788914
  have htrace : WordTrace (prefixWord ++ tailWord_7788914) baseStart_7788914 baseEnd_7788914 := by
    simpa [prefixWord, tailWord_7788914, baseEnd_7788914] using wordTrace_append hprefix tailTrace_7788914
  have hstable : (prefixWord ++ tailWord_7788914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788914).length < 2 ^ (prefixWord ++ tailWord_7788914).sum := by decide
  have hdescent : baseEnd_7788914 < baseStart_7788914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788918 : List Nat := [5, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_7788918 : Nat := 118140960795 + 7788918 * 2 ^ 59
def prefixEnd_7788918 : Nat := 4983230072969 + 3 ^ 40 * 7788918 * 2
def baseEnd_7788918 : Nat := 3999458712456462056204425

theorem tailTrace_7788918 : CollatzResearch.WordTrace tailWord_7788918 prefixEnd_7788918 3999458712456462056204425 := by
  unfold tailWord_7788918
  simp only [CollatzResearch.WordTrace]
  refine ⟨17755323624755487633349463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189390118664058534755727605 17755323624755487633349463)
  ·
    refine ⟨26632985437133231450024195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17755323624755487633349463 26632985437133231450024195)
    ·
      refine ⟨39949478155699847175036293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26632985437133231450024195 39949478155699847175036293)
      ·
        refine ⟨7490527154193721345319305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39949478155699847175036293 7490527154193721345319305)
        ·
          refine ⟨5617895365645291008989479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7490527154193721345319305 5617895365645291008989479)
          ·
            refine ⟨8426843048467936513484219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5617895365645291008989479 8426843048467936513484219)
            ·
              refine ⟨12640264572701904770226329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8426843048467936513484219 12640264572701904770226329)
              ·
                refine ⟨9480198429526428577669747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12640264572701904770226329 9480198429526428577669747)
                ·
                  refine ⟨14220297644289642866504621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9480198429526428577669747 14220297644289642866504621)
                  ·
                    refine ⟨5332611616608616074939233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14220297644289642866504621 5332611616608616074939233)
                    ·
                      refine ⟨3999458712456462056204425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5332611616608616074939233 3999458712456462056204425)
                      ·
                        rfl

theorem cell23_7788918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_7788918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788918 prefixEnd_7788918 := by exact prefixLift 7788918
  have htrace : WordTrace (prefixWord ++ tailWord_7788918) baseStart_7788918 baseEnd_7788918 := by
    simpa [prefixWord, tailWord_7788918, baseEnd_7788918] using wordTrace_append hprefix tailTrace_7788918
  have hstable : (prefixWord ++ tailWord_7788918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788918).length < 2 ^ (prefixWord ++ tailWord_7788918).sum := by decide
  have hdescent : baseEnd_7788918 < baseStart_7788918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7788953 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 2, 1, 4]
def baseStart_7788953 : Nat := 118140960795 + 7788953 * 2 ^ 59
def prefixEnd_7788953 : Nat := 4983230072969 + 3 ^ 40 * 7788953 * 2
def baseEnd_7788953 : Nat := 3999476684279369419266763

theorem tailTrace_7788953 : CollatzResearch.WordTrace tailWord_7788953 prefixEnd_7788953 3999476684279369419266763 := by
  unfold tailWord_7788953
  simp only [CollatzResearch.WordTrace]
  refine ⟨284086454550961003111115513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189390969700640668740743675 284086454550961003111115513)
  ·
    refine ⟨213064840913220752333336635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284086454550961003111115513 213064840913220752333336635)
    ·
      refine ⟨319597261369831128500004953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213064840913220752333336635 319597261369831128500004953)
      ·
        refine ⟨239697946027373346375003715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319597261369831128500004953 239697946027373346375003715)
        ·
          refine ⟨359546919041060019562505573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239697946027373346375003715 359546919041060019562505573)
          ·
            refine ⟨67415047320198753667969795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 359546919041060019562505573 67415047320198753667969795)
            ·
              refine ⟨101122570980298130501954693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67415047320198753667969795 101122570980298130501954693)
              ·
                refine ⟨18960482058805899469116505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101122570980298130501954693 18960482058805899469116505)
                ·
                  refine ⟨14220361544104424601837379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18960482058805899469116505 14220361544104424601837379)
                  ·
                    refine ⟨21330542316156636902756069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14220361544104424601837379 21330542316156636902756069)
                    ·
                      refine ⟨3999476684279369419266763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21330542316156636902756069 3999476684279369419266763)
                      ·
                        rfl

theorem cell23_7788953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_7788953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7788953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7788953 prefixEnd_7788953 := by exact prefixLift 7788953
  have htrace : WordTrace (prefixWord ++ tailWord_7788953) baseStart_7788953 baseEnd_7788953 := by
    simpa [prefixWord, tailWord_7788953, baseEnd_7788953] using wordTrace_append hprefix tailTrace_7788953
  have hstable : (prefixWord ++ tailWord_7788953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7788953).length < 2 ^ (prefixWord ++ tailWord_7788953).sum := by decide
  have hdescent : baseEnd_7788953 < baseStart_7788953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7788953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789013 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_7789013 : Nat := 118140960795 + 7789013 * 2 ^ 59
def prefixEnd_7789013 : Nat := 4983230072969 + 3 ^ 40 * 7789013 * 2
def baseEnd_7789013 : Nat := 3999507493118639184516487

theorem tailTrace_7789013 : CollatzResearch.WordTrace tailWord_7789013 prefixEnd_7789013 3999507493118639184516487 := by
  unfold tailWord_7789013
  simp only [CollatzResearch.WordTrace]
  refine ⟨284088642930743633358299693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189392428620495755572199795 284088642930743633358299693)
  ·
    refine ⟨106533241099028862509362385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284088642930743633358299693 106533241099028862509362385)
    ·
      refine ⟨79899930824271646882021789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106533241099028862509362385 79899930824271646882021789)
      ·
        refine ⟨29962474059101867580758171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79899930824271646882021789 29962474059101867580758171)
        ·
          refine ⟨44943711088652801371137257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29962474059101867580758171 44943711088652801371137257)
          ·
            refine ⟨33707783316489601028352943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44943711088652801371137257 33707783316489601028352943)
            ·
              refine ⟨50561674974734401542529415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33707783316489601028352943 50561674974734401542529415)
              ·
                refine ⟨75842512462101602313794123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50561674974734401542529415 75842512462101602313794123)
                ·
                  refine ⟨113763768693152403470691185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75842512462101602313794123 113763768693152403470691185)
                  ·
                    refine ⟨85322826519864302603018389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113763768693152403470691185 85322826519864302603018389)
                    ·
                      refine ⟨3999507493118639184516487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85322826519864302603018389 3999507493118639184516487)
                      ·
                        rfl

theorem cell23_7789013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_7789013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789013 prefixEnd_7789013 := by exact prefixLift 7789013
  have htrace : WordTrace (prefixWord ++ tailWord_7789013) baseStart_7789013 baseEnd_7789013 := by
    simpa [prefixWord, tailWord_7789013, baseEnd_7789013] using wordTrace_append hprefix tailTrace_7789013
  have hstable : (prefixWord ++ tailWord_7789013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789013).length < 2 ^ (prefixWord ++ tailWord_7789013).sum := by decide
  have hdescent : baseEnd_7789013 < baseStart_7789013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789014 : List Nat := [5, 2, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_7789014 : Nat := 118140960795 + 7789014 * 2 ^ 59
def prefixEnd_7789014 : Nat := 4983230072969 + 3 ^ 40 * 7789014 * 2
def baseEnd_7789014 : Nat := 1333169335533097893534661

theorem tailTrace_7789014 : CollatzResearch.WordTrace tailWord_7789014 prefixEnd_7789014 1333169335533097893534661 := by
  unfold tailWord_7789014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17755542462733750658067881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189392452935826673686057397 17755542462733750658067881)
  ·
    refine ⟨13316656847050312993550911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17755542462733750658067881 13316656847050312993550911)
    ·
      refine ⟨19974985270575469490326367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13316656847050312993550911 19974985270575469490326367)
      ·
        refine ⟨29962477905863204235489551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19974985270575469490326367 29962477905863204235489551)
        ·
          refine ⟨44943716858794806353234327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29962477905863204235489551 44943716858794806353234327)
          ·
            refine ⟨67415575288192209529851491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44943716858794806353234327 67415575288192209529851491)
            ·
              refine ⟨101123362932288314294777237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67415575288192209529851491 101123362932288314294777237)
              ·
                refine ⟨4740157637451014732567683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101123362932288314294777237 4740157637451014732567683)
                ·
                  refine ⟨7110236456176522098851525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4740157637451014732567683 7110236456176522098851525)
                  ·
                    refine ⟨1333169335533097893534661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7110236456176522098851525 1333169335533097893534661)
                    ·
                      rfl

theorem cell23_7789014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_7789014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789014 prefixEnd_7789014 := by exact prefixLift 7789014
  have htrace : WordTrace (prefixWord ++ tailWord_7789014) baseStart_7789014 baseEnd_7789014 := by
    simpa [prefixWord, tailWord_7789014, baseEnd_7789014] using wordTrace_append hprefix tailTrace_7789014
  have hstable : (prefixWord ++ tailWord_7789014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789014).length < 2 ^ (prefixWord ++ tailWord_7789014).sum := by decide
  have hdescent : baseEnd_7789014 < baseStart_7789014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789027 : List Nat := [1, 1, 1, 6, 3, 1, 3, 1, 6]
def baseStart_7789027 : Nat := 118140960795 + 7789027 * 2 ^ 59
def prefixEnd_7789027 : Nat := 4983230072969 + 3 ^ 40 * 7789027 * 2
def baseEnd_7789027 : Nat := 444390520205311347749047

theorem tailTrace_7789027 : CollatzResearch.WordTrace tailWord_7789027 prefixEnd_7789027 444390520205311347749047 := by
  unfold tailWord_7789027
  simp only [CollatzResearch.WordTrace]
  refine ⟨284089153552692913749309335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189392769035128609166206223 284089153552692913749309335)
  ·
    refine ⟨426133730329039370623964003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284089153552692913749309335 426133730329039370623964003)
    ·
      refine ⟨639200595493559055935946005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426133730329039370623964003 639200595493559055935946005)
      ·
        refine ⟨29962527913760580746997469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 639200595493559055935946005 29962527913760580746997469)
        ·
          refine ⟨11235947967660217780124051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29962527913760580746997469 11235947967660217780124051)
          ·
            refine ⟨16853921951490326670186077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11235947967660217780124051 16853921951490326670186077)
            ·
              refine ⟨6320220731808872501319779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16853921951490326670186077 6320220731808872501319779)
              ·
                refine ⟨9480331097713308751979669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6320220731808872501319779 9480331097713308751979669)
                ·
                  refine ⟨444390520205311347749047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9480331097713308751979669 444390520205311347749047)
                  ·
                    rfl

theorem cell23_7789027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 6].length) (baseStart_7789027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789027 prefixEnd_7789027 := by exact prefixLift 7789027
  have htrace : WordTrace (prefixWord ++ tailWord_7789027) baseStart_7789027 baseEnd_7789027 := by
    simpa [prefixWord, tailWord_7789027, baseEnd_7789027] using wordTrace_append hprefix tailTrace_7789027
  have hstable : (prefixWord ++ tailWord_7789027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789027).length < 2 ^ (prefixWord ++ tailWord_7789027).sum := by decide
  have hdescent : baseEnd_7789027 < baseStart_7789027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789040 : List Nat := [2, 1, 1, 1, 3, 3, 4, 2, 1, 5]
def baseStart_7789040 : Nat := 118140960795 + 7789040 * 2 ^ 59
def prefixEnd_7789040 : Nat := 4983230072969 + 3 ^ 40 * 7789040 * 2
def baseEnd_7789040 : Nat := 1333173785698770192959621

theorem tailTrace_7789040 : CollatzResearch.WordTrace tailWord_7789040 prefixEnd_7789040 1333173785698770192959621 := by
  unfold tailWord_7789040
  simp only [CollatzResearch.WordTrace]
  refine ⟨142044813850822908484766287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189393085134430544646355049 142044813850822908484766287)
  ·
    refine ⟨213067220776234362727149431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142044813850822908484766287 213067220776234362727149431)
    ·
      refine ⟨319600831164351544090724147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213067220776234362727149431 319600831164351544090724147)
      ·
        refine ⟨479401246746527316136086221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319600831164351544090724147 479401246746527316136086221)
        ·
          refine ⟨179775467529947743551032333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479401246746527316136086221 179775467529947743551032333)
          ·
            refine ⟨67415800323730403831637125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179775467529947743551032333 67415800323730403831637125)
            ·
              refine ⟨12640462560699450718431961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67415800323730403831637125 12640462560699450718431961)
              ·
                refine ⟨9480346920524588038823971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12640462560699450718431961 9480346920524588038823971)
                ·
                  refine ⟨14220520380786882058235957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9480346920524588038823971 14220520380786882058235957)
                  ·
                    refine ⟨1333173785698770192959621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14220520380786882058235957 1333173785698770192959621)
                    ·
                      rfl

theorem cell23_7789040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 1, 5].length) (baseStart_7789040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789040 prefixEnd_7789040 := by exact prefixLift 7789040
  have htrace : WordTrace (prefixWord ++ tailWord_7789040) baseStart_7789040 baseEnd_7789040 := by
    simpa [prefixWord, tailWord_7789040, baseEnd_7789040] using wordTrace_append hprefix tailTrace_7789040
  have hstable : (prefixWord ++ tailWord_7789040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789040).length < 2 ^ (prefixWord ++ tailWord_7789040).sum := by decide
  have hdescent : baseEnd_7789040 < baseStart_7789040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789053 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_7789053 : Nat := 118140960795 + 7789053 * 2 ^ 59
def prefixEnd_7789053 : Nat := 4983230072969 + 3 ^ 40 * 7789053 * 2
def baseEnd_7789053 : Nat := 1333176010781606342672101

theorem tailTrace_7789053 : CollatzResearch.WordTrace tailWord_7789053 prefixEnd_7789053 1333176010781606342672101 := by
  unfold tailWord_7789053
  simp only [CollatzResearch.WordTrace]
  refine ⟨284090101850598720189755813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189393401233732480126503875 284090101850598720189755813)
  ·
    refine ⟨53266894096987260035579215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284090101850598720189755813 53266894096987260035579215)
    ·
      refine ⟨79900341145480890053368823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53266894096987260035579215 79900341145480890053368823)
      ·
        refine ⟨119850511718221335080053235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79900341145480890053368823 119850511718221335080053235)
        ·
          refine ⟨179775767577332002620079853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119850511718221335080053235 179775767577332002620079853)
          ·
            refine ⟨67415912841499500982529945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179775767577332002620079853 67415912841499500982529945)
            ·
              refine ⟨50561934631124625736897459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67415912841499500982529945 50561934631124625736897459)
              ·
                refine ⟨75842901946686938605346189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50561934631124625736897459 75842901946686938605346189)
                ·
                  refine ⟨28441088230007601977004821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75842901946686938605346189 28441088230007601977004821)
                  ·
                    refine ⟨1333176010781606342672101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28441088230007601977004821 1333176010781606342672101)
                    ·
                      rfl

theorem cell23_7789053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_7789053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789053 prefixEnd_7789053 := by exact prefixLift 7789053
  have htrace : WordTrace (prefixWord ++ tailWord_7789053) baseStart_7789053 baseEnd_7789053 := by
    simpa [prefixWord, tailWord_7789053, baseEnd_7789053] using wordTrace_append hprefix tailTrace_7789053
  have hstable : (prefixWord ++ tailWord_7789053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789053).length < 2 ^ (prefixWord ++ tailWord_7789053).sum := by decide
  have hdescent : baseEnd_7789053 < baseStart_7789053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789073 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_7789073 : Nat := 118140960795 + 7789073 * 2 ^ 59
def prefixEnd_7789073 : Nat := 4983230072969 + 3 ^ 40 * 7789073 * 2
def baseEnd_7789073 : Nat := 3999538301957908949766211

theorem tailTrace_7789073 : CollatzResearch.WordTrace tailWord_7789073 prefixEnd_7789073 3999538301957908949766211 := by
  unfold tailWord_7789073
  simp only [CollatzResearch.WordTrace]
  refine ⟨284090831310526263605483873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189393887540350842403655915 284090831310526263605483873)
  ·
    refine ⟨213068123482894697704112905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284090831310526263605483873 213068123482894697704112905)
    ·
      refine ⟨159801092612171023278084679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213068123482894697704112905 159801092612171023278084679)
      ·
        refine ⟨239701638918256534917127019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159801092612171023278084679 239701638918256534917127019)
        ·
          refine ⟨359552458377384802375690529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239701638918256534917127019 359552458377384802375690529)
          ·
            refine ⟨269664343783038601781767897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359552458377384802375690529 269664343783038601781767897)
            ·
              refine ⟨202248257837278951336325923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269664343783038601781767897 202248257837278951336325923)
              ·
                refine ⟨303372386755918427004488885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202248257837278951336325923 303372386755918427004488885)
                ·
                  refine ⟨28441161258367352531670833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 303372386755918427004488885 28441161258367352531670833)
                  ·
                    refine ⟨21330870943775514398753125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28441161258367352531670833 21330870943775514398753125)
                    ·
                      refine ⟨3999538301957908949766211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21330870943775514398753125 3999538301957908949766211)
                      ·
                        rfl

theorem cell23_7789073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_7789073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789073 prefixEnd_7789073 := by exact prefixLift 7789073
  have htrace : WordTrace (prefixWord ++ tailWord_7789073) baseStart_7789073 baseEnd_7789073 := by
    simpa [prefixWord, tailWord_7789073, baseEnd_7789073] using wordTrace_append hprefix tailTrace_7789073
  have hstable : (prefixWord ++ tailWord_7789073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789073).length < 2 ^ (prefixWord ++ tailWord_7789073).sum := by decide
  have hdescent : baseEnd_7789073 < baseStart_7789073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789080 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 1, 1, 5]
def baseStart_7789080 : Nat := 118140960795 + 7789080 * 2 ^ 59
def prefixEnd_7789080 : Nat := 4983230072969 + 3 ^ 40 * 7789080 * 2
def baseEnd_7789080 : Nat := 3999541896322490422378679

theorem tailTrace_7789080 : CollatzResearch.WordTrace tailWord_7789080 prefixEnd_7789080 3999541896322490422378679 := by
  unfold tailWord_7789080
  simp only [CollatzResearch.WordTrace]
  refine ⟨142045543310750451900494347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189394057747667269200659129 142045543310750451900494347)
  ·
    refine ⟨213068314966125677850741521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142045543310750451900494347 213068314966125677850741521)
    ·
      refine ⟨159801236224594258388056141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213068314966125677850741521 159801236224594258388056141)
      ·
        refine ⟨59925463584222846895521053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159801236224594258388056141 59925463584222846895521053)
        ·
          refine ⟨22472048844083567585820395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59925463584222846895521053 22472048844083567585820395)
          ·
            refine ⟨33708073266125351378730593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22472048844083567585820395 33708073266125351378730593)
            ·
              refine ⟨25281054949594013534047945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33708073266125351378730593 25281054949594013534047945)
              ·
                refine ⟨18960791212195510150535959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25281054949594013534047945 18960791212195510150535959)
                ·
                  refine ⟨28441186818293265225803939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18960791212195510150535959 28441186818293265225803939)
                  ·
                    refine ⟨42661780227439897838705909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28441186818293265225803939 42661780227439897838705909)
                    ·
                      refine ⟨3999541896322490422378679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42661780227439897838705909 3999541896322490422378679)
                      ·
                        rfl

theorem cell23_7789080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_7789080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789080 prefixEnd_7789080 := by exact prefixLift 7789080
  have htrace : WordTrace (prefixWord ++ tailWord_7789080) baseStart_7789080 baseEnd_7789080 := by
    simpa [prefixWord, tailWord_7789080, baseEnd_7789080] using wordTrace_append hprefix tailTrace_7789080
  have hstable : (prefixWord ++ tailWord_7789080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789080).length < 2 ^ (prefixWord ++ tailWord_7789080).sum := by decide
  have hdescent : baseEnd_7789080 < baseStart_7789080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789090 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_7789090 : Nat := 118140960795 + 7789090 * 2 ^ 59
def prefixEnd_7789090 : Nat := 4983230072969 + 3 ^ 40 * 7789090 * 2
def baseEnd_7789090 : Nat := 3999547031129035383253633

theorem tailTrace_7789090 : CollatzResearch.WordTrace tailWord_7789090 prefixEnd_7789090 3999547031129035383253633 := by
  unfold tailWord_7789090
  simp only [CollatzResearch.WordTrace]
  refine ⟨71022862837866168877213181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189394300900976450339235149 71022862837866168877213181)
  ·
    refine ⟨26633573564199813328954943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71022862837866168877213181 26633573564199813328954943)
    ·
      refine ⟨39950360346299719993432415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26633573564199813328954943 39950360346299719993432415)
      ·
        refine ⟨59925540519449579990148623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39950360346299719993432415 59925540519449579990148623)
        ·
          refine ⟨89888310779174369985222935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59925540519449579990148623 89888310779174369985222935)
          ·
            refine ⟨134832466168761554977834403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89888310779174369985222935 134832466168761554977834403)
            ·
              refine ⟨202248699253142332466751605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134832466168761554977834403 202248699253142332466751605)
              ·
                refine ⟨18960815554982093668757963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202248699253142332466751605 18960815554982093668757963)
                ·
                  refine ⟨28441223332473140503136945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18960815554982093668757963 28441223332473140503136945)
                  ·
                    refine ⟨21330917499354855377352709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28441223332473140503136945 21330917499354855377352709)
                    ·
                      refine ⟨3999547031129035383253633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21330917499354855377352709 3999547031129035383253633)
                      ·
                        rfl

theorem cell23_7789090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_7789090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789090 prefixEnd_7789090 := by exact prefixLift 7789090
  have htrace : WordTrace (prefixWord ++ tailWord_7789090) baseStart_7789090 baseEnd_7789090 := by
    simpa [prefixWord, tailWord_7789090, baseEnd_7789090] using wordTrace_append hprefix tailTrace_7789090
  have hstable : (prefixWord ++ tailWord_7789090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789090).length < 2 ^ (prefixWord ++ tailWord_7789090).sum := by decide
  have hdescent : baseEnd_7789090 < baseStart_7789090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789114 : List Nat := [3, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3]
def baseStart_7789114 : Nat := 118140960795 + 7789114 * 2 ^ 59
def prefixEnd_7789114 : Nat := 4983230072969 + 3 ^ 40 * 7789114 * 2
def baseEnd_7789114 : Nat := 3999559354664743289353523

theorem tailTrace_7789114 : CollatzResearch.WordTrace tailWord_7789114 prefixEnd_7789114 3999559354664743289353523 := by
  unfold tailWord_7789114
  simp only [CollatzResearch.WordTrace]
  refine ⟨71023081675844431901931599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189394884468918485071817597 71023081675844431901931599)
  ·
    refine ⟨106534622513766647852897399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71023081675844431901931599 106534622513766647852897399)
    ·
      refine ⟨159801933770649971779346099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106534622513766647852897399 159801933770649971779346099)
      ·
        refine ⟨239702900655974957669019149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159801933770649971779346099 239702900655974957669019149)
        ·
          refine ⟨89888587745990609125882181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239702900655974957669019149 89888587745990609125882181)
          ·
            refine ⟨16854110202373239211102909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89888587745990609125882181 16854110202373239211102909)
            ·
              refine ⟨6320291325889964704163591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16854110202373239211102909 6320291325889964704163591)
              ·
                refine ⟨9480436988834947056245387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6320291325889964704163591 9480436988834947056245387)
                ·
                  refine ⟨14220655483252420584368081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9480436988834947056245387 14220655483252420584368081)
                  ·
                    refine ⟨10665491612439315438276061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14220655483252420584368081 10665491612439315438276061)
                    ·
                      refine ⟨3999559354664743289353523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10665491612439315438276061 3999559354664743289353523)
                      ·
                        rfl

theorem cell23_7789114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3].length) (baseStart_7789114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789114 prefixEnd_7789114 := by exact prefixLift 7789114
  have htrace : WordTrace (prefixWord ++ tailWord_7789114) baseStart_7789114 baseEnd_7789114 := by
    simpa [prefixWord, tailWord_7789114, baseEnd_7789114] using wordTrace_append hprefix tailTrace_7789114
  have hstable : (prefixWord ++ tailWord_7789114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789114).length < 2 ^ (prefixWord ++ tailWord_7789114).sum := by decide
  have hdescent : baseEnd_7789114 < baseStart_7789114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789123 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 5]
def baseStart_7789123 : Nat := 118140960795 + 7789123 * 2 ^ 59
def prefixEnd_7789123 : Nat := 4983230072969 + 3 ^ 40 * 7789123 * 2
def baseEnd_7789123 : Nat := 3999563975990633754140981

theorem tailTrace_7789123 : CollatzResearch.WordTrace tailWord_7789123 prefixEnd_7789123 3999563975990633754140981 := by
  unfold tailWord_7789123
  simp only [CollatzResearch.WordTrace]
  refine ⟨284092654960345122144804023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189395103306896748096536015 284092654960345122144804023)
  ·
    refine ⟨426138982440517683217206035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284092654960345122144804023 426138982440517683217206035)
    ·
      refine ⟨639208473660776524825809053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426138982440517683217206035 639208473660776524825809053)
      ·
        refine ⟨239703177622791196809678395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639208473660776524825809053 239703177622791196809678395)
        ·
          refine ⟨359554766434186795214517593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239703177622791196809678395 359554766434186795214517593)
          ·
            refine ⟨269666074825640096410888195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359554766434186795214517593 269666074825640096410888195)
            ·
              refine ⟨404499112238460144616332293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269666074825640096410888195 404499112238460144616332293)
              ·
                refine ⟨75843583544711277115562305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 404499112238460144616332293 75843583544711277115562305)
                ·
                  refine ⟨56882687658533457836671729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75843583544711277115562305 56882687658533457836671729)
                  ·
                    refine ⟨42662015743900093377503797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56882687658533457836671729 42662015743900093377503797)
                    ·
                      refine ⟨3999563975990633754140981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42662015743900093377503797 3999563975990633754140981)
                      ·
                        rfl

theorem cell23_7789123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_7789123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789123 prefixEnd_7789123 := by exact prefixLift 7789123
  have htrace : WordTrace (prefixWord ++ tailWord_7789123) baseStart_7789123 baseEnd_7789123 := by
    simpa [prefixWord, tailWord_7789123, baseEnd_7789123] using wordTrace_append hprefix tailTrace_7789123
  have hstable : (prefixWord ++ tailWord_7789123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789123).length < 2 ^ (prefixWord ++ tailWord_7789123).sum := by decide
  have hdescent : baseEnd_7789123 < baseStart_7789123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789137 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 3, 3, 2]
def baseStart_7789137 : Nat := 118140960795 + 7789137 * 2 ^ 59
def prefixEnd_7789137 : Nat := 4983230072969 + 3 ^ 40 * 7789137 * 2
def baseEnd_7789137 : Nat := 3999571164719796699365917

theorem tailTrace_7789137 : CollatzResearch.WordTrace tailWord_7789137 prefixEnd_7789137 3999571164719796699365917 := by
  unfold tailWord_7789137
  simp only [CollatzResearch.WordTrace]
  refine ⟨284093165582294402535813665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189395443721529601690542443 284093165582294402535813665)
  ·
    refine ⟨213069874186720801901860249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284093165582294402535813665 213069874186720801901860249)
    ·
      refine ⟨159802405640040601426395187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213069874186720801901860249 159802405640040601426395187)
      ·
        refine ⟨239703608460060902139592781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159802405640040601426395187 239703608460060902139592781)
        ·
          refine ⟨89888853172522838302347293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239703608460060902139592781 89888853172522838302347293)
          ·
            refine ⟨33708319939696064363380235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89888853172522838302347293 33708319939696064363380235)
            ·
              refine ⟨50562479909544096545070353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33708319939696064363380235 50562479909544096545070353)
              ·
                refine ⟨37921859932158072408802765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50562479909544096545070353 37921859932158072408802765)
                ·
                  refine ⟨14220697474559277153301037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37921859932158072408802765 14220697474559277153301037)
                  ·
                    refine ⟨5332761552959728932487889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14220697474559277153301037 5332761552959728932487889)
                    ·
                      refine ⟨3999571164719796699365917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5332761552959728932487889 3999571164719796699365917)
                      ·
                        rfl

theorem cell23_7789137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 3, 2].length) (baseStart_7789137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789137 prefixEnd_7789137 := by exact prefixLift 7789137
  have htrace : WordTrace (prefixWord ++ tailWord_7789137) baseStart_7789137 baseEnd_7789137 := by
    simpa [prefixWord, tailWord_7789137, baseEnd_7789137] using wordTrace_append hprefix tailTrace_7789137
  have hstable : (prefixWord ++ tailWord_7789137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789137).length < 2 ^ (prefixWord ++ tailWord_7789137).sum := by decide
  have hdescent : baseEnd_7789137 < baseStart_7789137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789167 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 1, 4, 2]
def baseStart_7789167 : Nat := 118140960795 + 7789167 * 2 ^ 59
def prefixEnd_7789167 : Nat := 4983230072969 + 3 ^ 40 * 7789167 * 2
def baseEnd_7789167 : Nat := 3999586569139431581990779

theorem tailTrace_7789167 : CollatzResearch.WordTrace tailWord_7789167 prefixEnd_7789167 3999586569139431581990779 := by
  unfold tailWord_7789167
  simp only [CollatzResearch.WordTrace]
  refine ⟨284094259772185717659405755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189396173181457145106270503 284094259772185717659405755)
  ·
    refine ⟨426141389658278576489108633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284094259772185717659405755 426141389658278576489108633)
    ·
      refine ⟨319606042243708932366831475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426141389658278576489108633 319606042243708932366831475)
      ·
        refine ⟨479409063365563398550247213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319606042243708932366831475 479409063365563398550247213)
        ·
          refine ⟨179778398762086274456342705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479409063365563398550247213 179778398762086274456342705)
          ·
            refine ⟨134833799071564705842257029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179778398762086274456342705 134833799071564705842257029)
            ·
              refine ⟨25281337325918382345423193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134833799071564705842257029 25281337325918382345423193)
              ·
                refine ⟨18961002994438786759067395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25281337325918382345423193 18961002994438786759067395)
                ·
                  refine ⟨28441504491658180138601093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18961002994438786759067395 28441504491658180138601093)
                  ·
                    refine ⟨5332782092185908775987705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28441504491658180138601093 5332782092185908775987705)
                    ·
                      refine ⟨3999586569139431581990779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5332782092185908775987705 3999586569139431581990779)
                      ·
                        rfl

theorem cell23_7789167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 4, 2].length) (baseStart_7789167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789167 prefixEnd_7789167 := by exact prefixLift 7789167
  have htrace : WordTrace (prefixWord ++ tailWord_7789167) baseStart_7789167 baseEnd_7789167 := by
    simpa [prefixWord, tailWord_7789167, baseEnd_7789167] using wordTrace_append hprefix tailTrace_7789167
  have hstable : (prefixWord ++ tailWord_7789167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789167).length < 2 ^ (prefixWord ++ tailWord_7789167).sum := by decide
  have hdescent : baseEnd_7789167 < baseStart_7789167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789180 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_7789180 : Nat := 118140960795 + 7789180 * 2 ^ 59
def prefixEnd_7789180 : Nat := 4983230072969 + 3 ^ 40 * 7789180 * 2
def baseEnd_7789180 : Nat := 3999593244387940031128219

theorem tailTrace_7789180 : CollatzResearch.WordTrace tailWord_7789180 prefixEnd_7789180 3999593244387940031128219 := by
  unfold tailWord_7789180
  simp only [CollatzResearch.WordTrace]
  refine ⟨142047366960569310439814497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189396489280759080586419329 142047366960569310439814497)
  ·
    refine ⟨106535525220426982829860873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142047366960569310439814497 106535525220426982829860873)
    ·
      refine ⟨79901643915320237122395655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106535525220426982829860873 79901643915320237122395655)
      ·
        refine ⟨119852465872980355683593483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79901643915320237122395655 119852465872980355683593483)
        ·
          refine ⟨179778698809470533525390225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119852465872980355683593483 179778698809470533525390225)
          ·
            refine ⟨134834024107102900144042669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179778698809470533525390225 134834024107102900144042669)
            ·
              refine ⟨50562759040163587554016001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134834024107102900144042669 50562759040163587554016001)
              ·
                refine ⟨37922069280122690665512001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50562759040163587554016001 37922069280122690665512001)
                ·
                  refine ⟨28441551960092017999134001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37922069280122690665512001 28441551960092017999134001)
                  ·
                    refine ⟨21331163970069013499350501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28441551960092017999134001 21331163970069013499350501)
                    ·
                      refine ⟨3999593244387940031128219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21331163970069013499350501 3999593244387940031128219)
                      ·
                        rfl

theorem cell23_7789180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_7789180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789180 prefixEnd_7789180 := by exact prefixLift 7789180
  have htrace : WordTrace (prefixWord ++ tailWord_7789180) baseStart_7789180 baseEnd_7789180 := by
    simpa [prefixWord, tailWord_7789180, baseEnd_7789180] using wordTrace_append hprefix tailTrace_7789180
  have hstable : (prefixWord ++ tailWord_7789180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789180).length < 2 ^ (prefixWord ++ tailWord_7789180).sum := by decide
  have hdescent : baseEnd_7789180 < baseStart_7789180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789183 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 9]
def baseStart_7789183 : Nat := 118140960795 + 7789183 * 2 ^ 59
def prefixEnd_7789183 : Nat := 4983230072969 + 3 ^ 40 * 7789183 * 2
def baseEnd_7789183 : Nat := 3999594784829903519390705

theorem tailTrace_7789183 : CollatzResearch.WordTrace tailWord_7789183 prefixEnd_7789183 3999594784829903519390705 := by
  unfold tailWord_7789183
  simp only [CollatzResearch.WordTrace]
  refine ⟨284094843340127752391988203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189396562226751834927992135 284094843340127752391988203)
  ·
    refine ⟨426142265010191628587982305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284094843340127752391988203 426142265010191628587982305)
    ·
      refine ⟨319606698757643721440986729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426142265010191628587982305 319606698757643721440986729)
      ·
        refine ⟨239705024068232791080740047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319606698757643721440986729 239705024068232791080740047)
        ·
          refine ⟨359557536102349186621110071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239705024068232791080740047 359557536102349186621110071)
          ·
            refine ⟨539336304153523779931665107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359557536102349186621110071 539336304153523779931665107)
            ·
              refine ⟨809004456230285669897497661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539336304153523779931665107 809004456230285669897497661)
              ·
                refine ⟨303376671086357126211561623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 809004456230285669897497661 303376671086357126211561623)
                ·
                  refine ⟨455065006629535689317342435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303376671086357126211561623 455065006629535689317342435)
                  ·
                    refine ⟨682597509944303533976013653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 455065006629535689317342435 682597509944303533976013653)
                    ·
                      refine ⟨3999594784829903519390705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 682597509944303533976013653 3999594784829903519390705)
                      ·
                        rfl

theorem cell23_7789183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_7789183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789183 prefixEnd_7789183 := by exact prefixLift 7789183
  have htrace : WordTrace (prefixWord ++ tailWord_7789183) baseStart_7789183 baseEnd_7789183 := by
    simpa [prefixWord, tailWord_7789183, baseEnd_7789183] using wordTrace_append hprefix tailTrace_7789183
  have hstable : (prefixWord ++ tailWord_7789183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789183).length < 2 ^ (prefixWord ++ tailWord_7789183).sum := by decide
  have hdescent : baseEnd_7789183 < baseStart_7789183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789184 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 4, 2, 2]
def baseStart_7789184 : Nat := 118140960795 + 7789184 * 2 ^ 59
def prefixEnd_7789184 : Nat := 4983230072969 + 3 ^ 40 * 7789184 * 2
def baseEnd_7789184 : Nat := 3999595298310558015478201

theorem tailTrace_7789184 : CollatzResearch.WordTrace tailWord_7789184 prefixEnd_7789184 3999595298310558015478201 := by
  unfold tailWord_7789184
  simp only [CollatzResearch.WordTrace]
  refine ⟨142047439906562064781387303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189396586542082753041849737 142047439906562064781387303)
  ·
    refine ⟨213071159859843097172080955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142047439906562064781387303 213071159859843097172080955)
    ·
      refine ⟨319606739789764645758121433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213071159859843097172080955 319606739789764645758121433)
      ·
        refine ⟨239705054842323484318591075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319606739789764645758121433 239705054842323484318591075)
        ·
          refine ⟨359557582263485226477886613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239705054842323484318591075 359557582263485226477886613)
          ·
            refine ⟨16854261668600869991150935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 359557582263485226477886613 16854261668600869991150935)
            ·
              refine ⟨25281392502901304986726403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16854261668600869991150935 25281392502901304986726403)
              ·
                refine ⟨37922088754351957480089605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25281392502901304986726403 37922088754351957480089605)
                ·
                  refine ⟨7110391641440992027516801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37922088754351957480089605 7110391641440992027516801)
                  ·
                    refine ⟨5332793731080744020637601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7110391641440992027516801 5332793731080744020637601)
                    ·
                      refine ⟨3999595298310558015478201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5332793731080744020637601 3999595298310558015478201)
                      ·
                        rfl

theorem cell23_7789184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 4, 2, 2].length) (baseStart_7789184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789184 prefixEnd_7789184 := by exact prefixLift 7789184
  have htrace : WordTrace (prefixWord ++ tailWord_7789184) baseStart_7789184 baseEnd_7789184 := by
    simpa [prefixWord, tailWord_7789184, baseEnd_7789184] using wordTrace_append hprefix tailTrace_7789184
  have hstable : (prefixWord ++ tailWord_7789184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789184).length < 2 ^ (prefixWord ++ tailWord_7789184).sum := by decide
  have hdescent : baseEnd_7789184 < baseStart_7789184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789220 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_7789220 : Nat := 118140960795 + 7789220 * 2 ^ 59
def prefixEnd_7789220 : Nat := 4983230072969 + 3 ^ 40 * 7789220 * 2
def baseEnd_7789220 : Nat := 1333204594538039958209345

theorem tailTrace_7789220 : CollatzResearch.WordTrace tailWord_7789220 prefixEnd_7789220 1333204594538039958209345 := by
  unfold tailWord_7789220
  simp only [CollatzResearch.WordTrace]
  refine ⟨142048096420496853855542557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189397461893995805140723409 142048096420496853855542557)
  ·
    refine ⟨53268036157686320195828459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142048096420496853855542557 53268036157686320195828459)
    ·
      refine ⟨79902054236529480293742689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53268036157686320195828459 79902054236529480293742689)
      ·
        refine ⟨59926540677397110220307017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79902054236529480293742689 59926540677397110220307017)
        ·
          refine ⟨44944905508047832665230263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59926540677397110220307017 44944905508047832665230263)
          ·
            refine ⟨67417358262071748997845395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44944905508047832665230263 67417358262071748997845395)
            ·
              refine ⟨101126037393107623496768093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67417358262071748997845395 101126037393107623496768093)
              ·
                refine ⟨37922264022415358811288035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101126037393107623496768093 37922264022415358811288035)
                ·
                  refine ⟨56883396033623038216932053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37922264022415358811288035 56883396033623038216932053)
                  ·
                    refine ⟨1333204594538039958209345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56883396033623038216932053 1333204594538039958209345)
                    ·
                      rfl

theorem cell23_7789220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_7789220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789220 prefixEnd_7789220 := by exact prefixLift 7789220
  have htrace : WordTrace (prefixWord ++ tailWord_7789220) baseStart_7789220 baseEnd_7789220 := by
    simpa [prefixWord, tailWord_7789220, baseEnd_7789220] using wordTrace_append hprefix tailTrace_7789220
  have hstable : (prefixWord ++ tailWord_7789220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789220).length < 2 ^ (prefixWord ++ tailWord_7789220).sum := by decide
  have hdescent : baseEnd_7789220 < baseStart_7789220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789237 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 4, 5]
def baseStart_7789237 : Nat := 118140960795 + 7789237 * 2 ^ 59
def prefixEnd_7789237 : Nat := 4983230072969 + 3 ^ 40 * 7789237 * 2
def baseEnd_7789237 : Nat := 1333207504261748769371819

theorem tailTrace_7789237 : CollatzResearch.WordTrace tailWord_7789237 prefixEnd_7789237 1333207504261748769371819 := by
  unfold tailWord_7789237
  simp only [CollatzResearch.WordTrace]
  refine ⟨284096812881932119614453965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189397875254621413076302643 284096812881932119614453965)
  ·
    refine ⟨106536304830724544855420237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284096812881932119614453965 106536304830724544855420237)
    ·
      refine ⟨39951114311521704320782589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106536304830724544855420237 39951114311521704320782589)
      ·
        refine ⟨14981667866820639120293471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39951114311521704320782589 14981667866820639120293471)
        ·
          refine ⟨22472501800230958680440207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14981667866820639120293471 22472501800230958680440207)
          ·
            refine ⟨33708752700346438020660311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22472501800230958680440207 33708752700346438020660311)
            ·
              refine ⟨50563129050519657030990467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33708752700346438020660311 50563129050519657030990467)
              ·
                refine ⟨75844693575779485546485701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50563129050519657030990467 75844693575779485546485701)
                ·
                  refine ⟨14220880045458653539966069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75844693575779485546485701 14220880045458653539966069)
                  ·
                    refine ⟨1333207504261748769371819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14220880045458653539966069 1333207504261748769371819)
                    ·
                      rfl

theorem cell23_7789237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_7789237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789237 prefixEnd_7789237 := by exact prefixLift 7789237
  have htrace : WordTrace (prefixWord ++ tailWord_7789237) baseStart_7789237 baseEnd_7789237 := by
    simpa [prefixWord, tailWord_7789237, baseEnd_7789237] using wordTrace_append hprefix tailTrace_7789237
  have hstable : (prefixWord ++ tailWord_7789237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789237).length < 2 ^ (prefixWord ++ tailWord_7789237).sum := by decide
  have hdescent : baseEnd_7789237 < baseStart_7789237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789294 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_7789294 : Nat := 118140960795 + 7789294 * 2 ^ 59
def prefixEnd_7789294 : Nat := 4983230072969 + 3 ^ 40 * 7789294 * 2
def baseEnd_7789294 : Nat := 3999651781182552585102695

theorem tailTrace_7789294 : CollatzResearch.WordTrace tailWord_7789294 prefixEnd_7789294 3999651781182552585102695 := by
  unfold tailWord_7789294
  simp only [CollatzResearch.WordTrace]
  refine ⟨35512361480340702293659867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189399261228483745566185957 35512361480340702293659867)
  ·
    refine ⟨53268542220511053440489801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35512361480340702293659867 53268542220511053440489801)
    ·
      refine ⟨39951406665383290080367351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53268542220511053440489801 39951406665383290080367351)
      ·
        refine ⟨59927109998074935120551027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39951406665383290080367351 59927109998074935120551027)
        ·
          refine ⟨89890664997112402680826541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59927109998074935120551027 89890664997112402680826541)
          ·
            refine ⟨33708999373917151005309953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89890664997112402680826541 33708999373917151005309953)
            ·
              refine ⟨25281749530437863253982465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33708999373917151005309953 25281749530437863253982465)
              ·
                refine ⟨18961312147828397440486849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25281749530437863253982465 18961312147828397440486849)
                ·
                  refine ⟨14220984110871298080365137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18961312147828397440486849 14220984110871298080365137)
                  ·
                    refine ⟨10665738083153473560273853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14220984110871298080365137 10665738083153473560273853)
                    ·
                      refine ⟨3999651781182552585102695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10665738083153473560273853 3999651781182552585102695)
                      ·
                        rfl

theorem cell23_7789294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_7789294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789294 prefixEnd_7789294 := by exact prefixLift 7789294
  have htrace : WordTrace (prefixWord ++ tailWord_7789294) baseStart_7789294 baseEnd_7789294 := by
    simpa [prefixWord, tailWord_7789294, baseEnd_7789294] using wordTrace_append hprefix tailTrace_7789294
  have hstable : (prefixWord ++ tailWord_7789294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789294).length < 2 ^ (prefixWord ++ tailWord_7789294).sum := by decide
  have hdescent : baseEnd_7789294 < baseStart_7789294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789297 : List Nat := [1, 2, 2, 2, 2, 2, 4, 2, 6]
def baseStart_7789297 : Nat := 118140960795 + 7789297 * 2 ^ 59
def prefixEnd_7789297 : Nat := 4983230072969 + 3 ^ 40 * 7789297 * 2
def baseEnd_7789297 : Nat := 444405924624946230373909

theorem tailTrace_7789297 : CollatzResearch.WordTrace tailWord_7789297 prefixEnd_7789297 444405924624946230373909 := by
  unfold tailWord_7789297
  simp only [CollatzResearch.WordTrace]
  refine ⟨284099001261714749861638145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189399334174476499907758763 284099001261714749861638145)
  ·
    refine ⟨213074250946286062396228609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284099001261714749861638145 213074250946286062396228609)
    ·
      refine ⟨159805688209714546797171457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213074250946286062396228609 159805688209714546797171457)
      ·
        refine ⟨119854266157285910097878593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159805688209714546797171457 119854266157285910097878593)
        ·
          refine ⟨89890699617964432573408945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119854266157285910097878593 89890699617964432573408945)
          ·
            refine ⟨67418024713473324430056709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89890699617964432573408945 67418024713473324430056709)
            ·
              refine ⟨12640879633776248330635633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67418024713473324430056709 12640879633776248330635633)
              ·
                refine ⟨9480659725332186247976725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12640879633776248330635633 9480659725332186247976725)
                ·
                  refine ⟨444405924624946230373909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9480659725332186247976725 444405924624946230373909)
                  ·
                    rfl

theorem cell23_7789297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 6].length) (baseStart_7789297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789297 prefixEnd_7789297 := by exact prefixLift 7789297
  have htrace : WordTrace (prefixWord ++ tailWord_7789297) baseStart_7789297 baseEnd_7789297 := by
    simpa [prefixWord, tailWord_7789297, baseEnd_7789297] using wordTrace_append hprefix tailTrace_7789297
  have hstable : (prefixWord ++ tailWord_7789297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789297).length < 2 ^ (prefixWord ++ tailWord_7789297).sum := by decide
  have hdescent : baseEnd_7789297 < baseStart_7789297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789314 : List Nat := [3, 4, 1, 1, 1, 2, 2, 3, 6]
def baseStart_7789314 : Nat := 118140960795 + 7789314 * 2 ^ 59
def prefixEnd_7789314 : Nat := 4983230072969 + 3 ^ 40 * 7789314 * 2
def baseEnd_7789314 : Nat := 444406894532849167428067

theorem tailTrace_7789314 : CollatzResearch.WordTrace tailWord_7789314 prefixEnd_7789314 444406894532849167428067 := by
  unfold tailWord_7789314
  simp only [CollatzResearch.WordTrace]
  refine ⟨71024905325663290441251749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189399747535102107843337997 71024905325663290441251749)
  ·
    refine ⟨13317169748561866957734703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71024905325663290441251749 13317169748561866957734703)
    ·
      refine ⟨19975754622842800436602055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13317169748561866957734703 19975754622842800436602055)
      ·
        refine ⟨29963631934264200654903083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19975754622842800436602055 29963631934264200654903083)
        ·
          refine ⟨44945447901396300982354625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29963631934264200654903083 44945447901396300982354625)
          ·
            refine ⟨33709085926047225736765969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44945447901396300982354625 33709085926047225736765969)
            ·
              refine ⟨25281814444535419302574477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33709085926047225736765969 25281814444535419302574477)
              ·
                refine ⟨9480680416700782238465429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25281814444535419302574477 9480680416700782238465429)
                ·
                  refine ⟨444406894532849167428067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9480680416700782238465429 444406894532849167428067)
                  ·
                    rfl

theorem cell23_7789314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_7789314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789314 prefixEnd_7789314 := by exact prefixLift 7789314
  have htrace : WordTrace (prefixWord ++ tailWord_7789314) baseStart_7789314 baseEnd_7789314 := by
    simpa [prefixWord, tailWord_7789314, baseEnd_7789314] using wordTrace_append hprefix tailTrace_7789314
  have hstable : (prefixWord ++ tailWord_7789314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789314).length < 2 ^ (prefixWord ++ tailWord_7789314).sum := by decide
  have hdescent : baseEnd_7789314 < baseStart_7789314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789327 : List Nat := [1, 1, 2, 1, 1, 1, 6, 4, 1, 5]
def baseStart_7789327 : Nat := 118140960795 + 7789327 * 2 ^ 59
def prefixEnd_7789327 : Nat := 4983230072969 + 3 ^ 40 * 7789327 * 2
def baseEnd_7789327 : Nat := 1333222908681383651996681

theorem tailTrace_7789327 : CollatzResearch.WordTrace tailWord_7789327 prefixEnd_7789327 1333222908681383651996681 := by
  unfold tailWord_7789327
  simp only [CollatzResearch.WordTrace]
  refine ⟨284100095451606064985230235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189400063634404043323486823 284100095451606064985230235)
  ·
    refine ⟨426150143177409097477845353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284100095451606064985230235 426150143177409097477845353)
    ·
      refine ⟨319612607383056823108384015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426150143177409097477845353 319612607383056823108384015)
      ·
        refine ⟨479418911074585234662576023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319612607383056823108384015 479418911074585234662576023)
        ·
          refine ⟨719128366611877851993864035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479418911074585234662576023 719128366611877851993864035)
          ·
            refine ⟨1078692549917816777990796053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719128366611877851993864035 1078692549917816777990796053)
            ·
              refine ⟨50563713277397661468318565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1078692549917816777990796053 50563713277397661468318565)
              ·
                refine ⟨9480696239512061525309731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50563713277397661468318565 9480696239512061525309731)
                ·
                  refine ⟨14221044359268092287964597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9480696239512061525309731 14221044359268092287964597)
                  ·
                    refine ⟨1333222908681383651996681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14221044359268092287964597 1333222908681383651996681)
                    ·
                      rfl

theorem cell23_7789327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 5].length) (baseStart_7789327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789327 prefixEnd_7789327 := by exact prefixLift 7789327
  have htrace : WordTrace (prefixWord ++ tailWord_7789327) baseStart_7789327 baseEnd_7789327 := by
    simpa [prefixWord, tailWord_7789327, baseEnd_7789327] using wordTrace_append hprefix tailTrace_7789327
  have hstable : (prefixWord ++ tailWord_7789327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789327).length < 2 ^ (prefixWord ++ tailWord_7789327).sum := by decide
  have hdescent : baseEnd_7789327 < baseStart_7789327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789344 : List Nat := [2, 1, 1, 5, 1, 3, 1, 3, 1, 5]
def baseStart_7789344 : Nat := 118140960795 + 7789344 * 2 ^ 59
def prefixEnd_7789344 : Nat := 4983230072969 + 3 ^ 40 * 7789344 * 2
def baseEnd_7789344 : Nat := 1333225818405092463159155

theorem tailTrace_7789344 : CollatzResearch.WordTrace tailWord_7789344 prefixEnd_7789344 1333225818405092463159155 := by
  unfold tailWord_7789344
  simp only [CollatzResearch.WordTrace]
  refine ⟨142050357746272238444299543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189400476995029651259066057 142050357746272238444299543)
  ·
    refine ⟨213075536619408357666449315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142050357746272238444299543 213075536619408357666449315)
    ·
      refine ⟨319613304929112536499673973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213075536619408357666449315 319613304929112536499673973)
      ·
        refine ⟨29963747337104300296844435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 319613304929112536499673973 29963747337104300296844435)
        ·
          refine ⟨44945621005656450445266653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29963747337104300296844435 44945621005656450445266653)
          ·
            refine ⟨16854607877121168916974995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44945621005656450445266653 16854607877121168916974995)
            ·
              refine ⟨25281911815681753375462493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16854607877121168916974995 25281911815681753375462493)
              ·
                refine ⟨9480716930880657515798435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25281911815681753375462493 9480716930880657515798435)
                ·
                  refine ⟨14221075396320986273697653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9480716930880657515798435 14221075396320986273697653)
                  ·
                    refine ⟨1333225818405092463159155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14221075396320986273697653 1333225818405092463159155)
                    ·
                      rfl

theorem cell23_7789344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 1, 5].length) (baseStart_7789344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789344 prefixEnd_7789344 := by exact prefixLift 7789344
  have htrace : WordTrace (prefixWord ++ tailWord_7789344) baseStart_7789344 baseEnd_7789344 := by
    simpa [prefixWord, tailWord_7789344, baseEnd_7789344] using wordTrace_append hprefix tailTrace_7789344
  have hstable : (prefixWord ++ tailWord_7789344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789344).length < 2 ^ (prefixWord ++ tailWord_7789344).sum := by decide
  have hdescent : baseEnd_7789344 < baseStart_7789344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789358 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_7789358 : Nat := 118140960795 + 7789358 * 2 ^ 59
def prefixEnd_7789358 : Nat := 4983230072969 + 3 ^ 40 * 7789358 * 2
def baseEnd_7789358 : Nat := 3999684643944440334702401

theorem tailTrace_7789358 : CollatzResearch.WordTrace tailWord_7789358 prefixEnd_7789358 3999684643944440334702401 := by
  unfold tailWord_7789358
  simp only [CollatzResearch.WordTrace]
  refine ⟨35512653264311719659951091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189400817409662504853072485 35512653264311719659951091)
  ·
    refine ⟨53268979896467579489926637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35512653264311719659951091 53268979896467579489926637)
    ·
      refine ⟨19975867461175342308722489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53268979896467579489926637 19975867461175342308722489)
      ·
        refine ⟨14981900595881506731541867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19975867461175342308722489 14981900595881506731541867)
        ·
          refine ⟨22472850893822260097312801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14981900595881506731541867 22472850893822260097312801)
          ·
            refine ⟨16854638170366695072984601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22472850893822260097312801 16854638170366695072984601)
            ·
              refine ⟨12640978627775021304738451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16854638170366695072984601 12640978627775021304738451)
              ·
                refine ⟨18961467941662531957107677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12640978627775021304738451 18961467941662531957107677)
                ·
                  refine ⟨7110550478123449483915379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18961467941662531957107677 7110550478123449483915379)
                  ·
                    refine ⟨10665825717185174225873069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7110550478123449483915379 10665825717185174225873069)
                    ·
                      refine ⟨3999684643944440334702401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10665825717185174225873069 3999684643944440334702401)
                      ·
                        rfl

theorem cell23_7789358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_7789358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789358 prefixEnd_7789358 := by exact prefixLift 7789358
  have htrace : WordTrace (prefixWord ++ tailWord_7789358) baseStart_7789358 baseEnd_7789358 := by
    simpa [prefixWord, tailWord_7789358, baseEnd_7789358] using wordTrace_append hprefix tailTrace_7789358
  have hstable : (prefixWord ++ tailWord_7789358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789358).length < 2 ^ (prefixWord ++ tailWord_7789358).sum := by decide
  have hdescent : baseEnd_7789358 < baseStart_7789358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789367 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 5]
def baseStart_7789367 : Nat := 118140960795 + 7789367 * 2 ^ 59
def prefixEnd_7789367 : Nat := 4983230072969 + 3 ^ 40 * 7789367 * 2
def baseEnd_7789367 : Nat := 3999689265270330799489859

theorem tailTrace_7789367 : CollatzResearch.WordTrace tailWord_7789367 prefixEnd_7789367 3999689265270330799489859 := by
  unfold tailWord_7789367
  simp only [CollatzResearch.WordTrace]
  refine ⟨284101554371461151816686355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189401036247640767877790903 284101554371461151816686355)
  ·
    refine ⟨426152331557191727725029533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284101554371461151816686355 426152331557191727725029533)
    ·
      refine ⟨159807124333946897896886075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426152331557191727725029533 159807124333946897896886075)
      ·
        refine ⟨239710686500920346845329113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159807124333946897896886075 239710686500920346845329113)
        ·
          refine ⟨179783014875690260133996835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239710686500920346845329113 179783014875690260133996835)
          ·
            refine ⟨269674522313535390200995253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179783014875690260133996835 269674522313535390200995253)
            ·
              refine ⟨25281986466893942831343305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269674522313535390200995253 25281986466893942831343305)
              ·
                refine ⟨18961489850170457123507479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25281986466893942831343305 18961489850170457123507479)
                ·
                  refine ⟨28442234775255685685261219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18961489850170457123507479 28442234775255685685261219)
                  ·
                    refine ⟨42663352162883528527891829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28442234775255685685261219 42663352162883528527891829)
                    ·
                      refine ⟨3999689265270330799489859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42663352162883528527891829 3999689265270330799489859)
                      ·
                        rfl

theorem cell23_7789367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_7789367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789367 prefixEnd_7789367 := by exact prefixLift 7789367
  have htrace : WordTrace (prefixWord ++ tailWord_7789367) baseStart_7789367 baseEnd_7789367 := by
    simpa [prefixWord, tailWord_7789367, baseEnd_7789367] using wordTrace_append hprefix tailTrace_7789367
  have hstable : (prefixWord ++ tailWord_7789367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789367).length < 2 ^ (prefixWord ++ tailWord_7789367).sum := by decide
  have hdescent : baseEnd_7789367 < baseStart_7789367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789404 : List Nat := [2, 2, 4, 2, 1, 3, 9]
def baseStart_7789404 : Nat := 118140960795 + 7789404 * 2 ^ 59
def prefixEnd_7789404 : Nat := 4983230072969 + 3 ^ 40 * 7789404 * 2
def baseEnd_7789404 : Nat := 49379114371043792033669

theorem tailTrace_7789404 : CollatzResearch.WordTrace tailWord_7789404 prefixEnd_7789404 49379114371043792033669 := by
  unfold tailWord_7789404
  simp only [CollatzResearch.WordTrace]
  refine ⟨142051451936163553567891633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189401935914884738090522177 142051451936163553567891633)
  ·
    refine ⟨106538588952122665175918725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142051451936163553567891633 106538588952122665175918725)
    ·
      refine ⟨19975985428522999720484761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106538588952122665175918725 19975985428522999720484761)
      ·
        refine ⟨14981989071392249790363571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19975985428522999720484761 14981989071392249790363571)
        ·
          refine ⟨22472983607088374685545357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14981989071392249790363571 22472983607088374685545357)
          ·
            refine ⟨8427368852658140507079509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22472983607088374685545357 8427368852658140507079509)
            ·
              refine ⟨49379114371043792033669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8427368852658140507079509 49379114371043792033669)
              ·
                rfl

theorem cell23_7789404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 9].length) (baseStart_7789404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789404 prefixEnd_7789404 := by exact prefixLift 7789404
  have htrace : WordTrace (prefixWord ++ tailWord_7789404) baseStart_7789404 baseEnd_7789404 := by
    simpa [prefixWord, tailWord_7789404, baseEnd_7789404] using wordTrace_append hprefix tailTrace_7789404
  have hstable : (prefixWord ++ tailWord_7789404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789404).length < 2 ^ (prefixWord ++ tailWord_7789404).sum := by decide
  have hdescent : baseEnd_7789404 < baseStart_7789404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789507 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 1, 7]
def baseStart_7789507 : Nat := 118140960795 + 7789507 * 2 ^ 59
def prefixEnd_7789507 : Nat := 4983230072969 + 3 ^ 40 * 7789507 * 2
def baseEnd_7789507 : Nat := 1333253717520653417246405

theorem tailTrace_7789507 : CollatzResearch.WordTrace tailWord_7789507 prefixEnd_7789507 1333253717520653417246405 := by
  unfold tailWord_7789507
  simp only [CollatzResearch.WordTrace]
  refine ⟨284106660590953955726782775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189404440393969303817855183 284106660590953955726782775)
  ·
    refine ⟨426159990886430933590174163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284106660590953955726782775 426159990886430933590174163)
    ·
      refine ⟨639239986329646400385261245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426159990886430933590174163 639239986329646400385261245)
      ·
        refine ⟨239714994873617400144472967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639239986329646400385261245 239714994873617400144472967)
        ·
          refine ⟨359572492310426100216709451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239714994873617400144472967 359572492310426100216709451)
          ·
            refine ⟨539358738465639150325064177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359572492310426100216709451 539358738465639150325064177)
            ·
              refine ⟨404519053849229362743798133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539358738465639150325064177 404519053849229362743798133)
              ·
                refine ⟨37923661298365252757231075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 404519053849229362743798133 37923661298365252757231075)
                ·
                  refine ⟨56885491947547879135846613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37923661298365252757231075 56885491947547879135846613)
                  ·
                    refine ⟨1333253717520653417246405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56885491947547879135846613 1333253717520653417246405)
                    ·
                      rfl

theorem cell23_7789507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 7].length) (baseStart_7789507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789507 prefixEnd_7789507 := by exact prefixLift 7789507
  have htrace : WordTrace (prefixWord ++ tailWord_7789507) baseStart_7789507 baseEnd_7789507 := by
    simpa [prefixWord, tailWord_7789507, baseEnd_7789507] using wordTrace_append hprefix tailTrace_7789507
  have hstable : (prefixWord ++ tailWord_7789507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789507).length < 2 ^ (prefixWord ++ tailWord_7789507).sum := by decide
  have hdescent : baseEnd_7789507 < baseStart_7789507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789522 : List Nat := [3, 2, 2, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_7789522 : Nat := 118140960795 + 7789522 * 2 ^ 59
def prefixEnd_7789522 : Nat := 4983230072969 + 3 ^ 40 * 7789522 * 2
def baseEnd_7789522 : Nat := 3999768854771777693051647

theorem tailTrace_7789522 : CollatzResearch.WordTrace tailWord_7789522 prefixEnd_7789522 3999768854771777693051647 := by
  unfold tailWord_7789522
  simp only [CollatzResearch.WordTrace]
  refine ⟨71026801921474903322144705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189404805123933075525719213 71026801921474903322144705)
  ·
    refine ⟨53270101441106177491608529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71026801921474903322144705 53270101441106177491608529)
    ·
      refine ⟨39952576080829633118706397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53270101441106177491608529 39952576080829633118706397)
      ·
        refine ⟨14982216030311112419514899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39952576080829633118706397 14982216030311112419514899)
        ·
          refine ⟨22473324045466668629272349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14982216030311112419514899 22473324045466668629272349)
          ·
            refine ⟨8427496517050000735977131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22473324045466668629272349 8427496517050000735977131)
            ·
              refine ⟨12641244775575001103965697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8427496517050000735977131 12641244775575001103965697)
              ·
                refine ⟨9480933581681250827974273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12641244775575001103965697 9480933581681250827974273)
                ·
                  refine ⟨7110700186260938120980705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9480933581681250827974273 7110700186260938120980705)
                  ·
                    refine ⟨5333025139695703590735529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7110700186260938120980705 5333025139695703590735529)
                    ·
                      refine ⟨3999768854771777693051647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5333025139695703590735529 3999768854771777693051647)
                      ·
                        rfl

theorem cell23_7789522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_7789522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789522 prefixEnd_7789522 := by exact prefixLift 7789522
  have htrace : WordTrace (prefixWord ++ tailWord_7789522) baseStart_7789522 baseEnd_7789522 := by
    simpa [prefixWord, tailWord_7789522, baseEnd_7789522] using wordTrace_append hprefix tailTrace_7789522
  have hstable : (prefixWord ++ tailWord_7789522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789522).length < 2 ^ (prefixWord ++ tailWord_7789522).sum := by decide
  have hdescent : baseEnd_7789522 < baseStart_7789522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789538 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_7789538 : Nat := 118140960795 + 7789538 * 2 ^ 59
def prefixEnd_7789538 : Nat := 4983230072969 + 3 ^ 40 * 7789538 * 2
def baseEnd_7789538 : Nat := 3999777070462249630451573

theorem tailTrace_7789538 : CollatzResearch.WordTrace tailWord_7789538 prefixEnd_7789538 3999777070462249630451573 := by
  unfold tailWord_7789538
  simp only [CollatzResearch.WordTrace]
  refine ⟨71026947813460412005290317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189405194169227765347440845 71026947813460412005290317)
  ·
    refine ⟨26635105430047654501983869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71026947813460412005290317 26635105430047654501983869)
    ·
      refine ⟨9988164536267870438243951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26635105430047654501983869 9988164536267870438243951)
      ·
        refine ⟨14982246804401805657365927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9988164536267870438243951 14982246804401805657365927)
        ·
          refine ⟨22473370206602708486048891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14982246804401805657365927 22473370206602708486048891)
          ·
            refine ⟨33710055309904062729073337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22473370206602708486048891 33710055309904062729073337)
            ·
              refine ⟨25282541482428047046805003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33710055309904062729073337 25282541482428047046805003)
              ·
                refine ⟨37923812223642070570207505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25282541482428047046805003 37923812223642070570207505)
                ·
                  refine ⟨28442859167731552927655629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37923812223642070570207505 28442859167731552927655629)
                  ·
                    refine ⟨10666072187899332347870861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28442859167731552927655629 10666072187899332347870861)
                    ·
                      refine ⟨3999777070462249630451573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10666072187899332347870861 3999777070462249630451573)
                      ·
                        rfl

theorem cell23_7789538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_7789538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789538 prefixEnd_7789538 := by exact prefixLift 7789538
  have htrace : WordTrace (prefixWord ++ tailWord_7789538) baseStart_7789538 baseEnd_7789538 := by
    simpa [prefixWord, tailWord_7789538, baseEnd_7789538] using wordTrace_append hprefix tailTrace_7789538
  have hstable : (prefixWord ++ tailWord_7789538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789538).length < 2 ^ (prefixWord ++ tailWord_7789538).sum := by decide
  have hdescent : baseEnd_7789538 < baseStart_7789538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789544 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_7789544 : Nat := 118140960795 + 7789544 * 2 ^ 59
def prefixEnd_7789544 : Nat := 4983230072969 + 3 ^ 40 * 7789544 * 2
def baseEnd_7789544 : Nat := 3999780151346176606976545

theorem tailTrace_7789544 : CollatzResearch.WordTrace tailWord_7789544 prefixEnd_7789544 3999780151346176606976545 := by
  unfold tailWord_7789544
  simp only [CollatzResearch.WordTrace]
  refine ⟨142054005045909955522939843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189405340061213274030586457 142054005045909955522939843)
  ·
    refine ⟨213081007568864933284409765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142054005045909955522939843 213081007568864933284409765)
    ·
      refine ⟨39952688919162174990826831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213081007568864933284409765 39952688919162174990826831)
      ·
        refine ⟨59929033378743262486240247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39952688919162174990826831 59929033378743262486240247)
        ·
          refine ⟨89893550068114893729360371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59929033378743262486240247 89893550068114893729360371)
          ·
            refine ⟨134840325102172340594040557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89893550068114893729360371 134840325102172340594040557)
            ·
              refine ⟨50565121913314627722765209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134840325102172340594040557 50565121913314627722765209)
              ·
                refine ⟨37923841434985970792073907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50565121913314627722765209 37923841434985970792073907)
                ·
                  refine ⟨56885762152478956188110861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37923841434985970792073907 56885762152478956188110861)
                  ·
                    refine ⟨21332160807179608570541573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56885762152478956188110861 21332160807179608570541573)
                    ·
                      refine ⟨3999780151346176606976545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21332160807179608570541573 3999780151346176606976545)
                      ·
                        rfl

theorem cell23_7789544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_7789544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789544 prefixEnd_7789544 := by exact prefixLift 7789544
  have htrace : WordTrace (prefixWord ++ tailWord_7789544) baseStart_7789544 baseEnd_7789544 := by
    simpa [prefixWord, tailWord_7789544, baseEnd_7789544] using wordTrace_append hprefix tailTrace_7789544
  have hstable : (prefixWord ++ tailWord_7789544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789544).length < 2 ^ (prefixWord ++ tailWord_7789544).sum := by decide
  have hdescent : baseEnd_7789544 < baseStart_7789544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789601 : List Nat := [1, 2, 3, 2, 3, 2, 1, 3, 6]
def baseStart_7789601 : Nat := 118140960795 + 7789601 * 2 ^ 59
def prefixEnd_7789601 : Nat := 4983230072969 + 3 ^ 40 * 7789601 * 2
def baseEnd_7789601 : Nat := 444423268860386987107087

theorem tailTrace_7789601 : CollatzResearch.WordTrace tailWord_7789601 prefixEnd_7789601 444423268860386987107087 := by
  unfold tailWord_7789601
  simp only [CollatzResearch.WordTrace]
  refine ⟨284110089052613409780704657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189406726035075606520469771 284110089052613409780704657)
  ·
    refine ⟨213082566789460057335528493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284110089052613409780704657 213082566789460057335528493)
    ·
      refine ⟨79905962546047521500823185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213082566789460057335528493 79905962546047521500823185)
      ·
        refine ⟨59929471909535641125617389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79905962546047521500823185 59929471909535641125617389)
        ·
          refine ⟨22473551966075865422106521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59929471909535641125617389 22473551966075865422106521)
          ·
            refine ⟨16855163974556899066579891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22473551966075865422106521 16855163974556899066579891)
            ·
              refine ⟨25282745961835348599869837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16855163974556899066579891 25282745961835348599869837)
              ·
                refine ⟨9481029735688255724951189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25282745961835348599869837 9481029735688255724951189)
                ·
                  refine ⟨444423268860386987107087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9481029735688255724951189 444423268860386987107087)
                  ·
                    rfl

theorem cell23_7789601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 6].length) (baseStart_7789601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789601 prefixEnd_7789601 := by exact prefixLift 7789601
  have htrace : WordTrace (prefixWord ++ tailWord_7789601) baseStart_7789601 baseEnd_7789601 := by
    simpa [prefixWord, tailWord_7789601, baseEnd_7789601] using wordTrace_append hprefix tailTrace_7789601
  have hstable : (prefixWord ++ tailWord_7789601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789601).length < 2 ^ (prefixWord ++ tailWord_7789601).sum := by decide
  have hdescent : baseEnd_7789601 < baseStart_7789601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789611 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 5, 1, 3]
def baseStart_7789611 : Nat := 118140960795 + 7789611 * 2 ^ 59
def prefixEnd_7789611 : Nat := 4983230072969 + 3 ^ 40 * 7789611 * 2
def baseEnd_7789611 : Nat := 3999814554550027844838737

theorem tailTrace_7789611 : CollatzResearch.WordTrace tailWord_7789611 prefixEnd_7789611 3999814554550027844838737 := by
  unfold tailWord_7789611
  simp only [CollatzResearch.WordTrace]
  refine ⟨284110453782577181488568687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189406969188384787659045791 284110453782577181488568687)
  ·
    refine ⟨426165680673865772232853031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284110453782577181488568687 426165680673865772232853031)
    ·
      refine ⟨639248521010798658349279547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426165680673865772232853031 639248521010798658349279547)
      ·
        refine ⟨958872781516197987523919321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639248521010798658349279547 958872781516197987523919321)
        ·
          refine ⟨719154586137148490642939491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 958872781516197987523919321 719154586137148490642939491)
          ·
            refine ⟨1078731879205722735964409237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719154586137148490642939491 1078731879205722735964409237)
            ·
              refine ⟨50565556837768253248331683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1078731879205722735964409237 50565556837768253248331683)
              ·
                refine ⟨75848335256652379872497525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50565556837768253248331683 75848335256652379872497525)
                ·
                  refine ⟨7110781430311160613046643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75848335256652379872497525 7110781430311160613046643)
                  ·
                    refine ⟨10666172145466740919569965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7110781430311160613046643 10666172145466740919569965)
                    ·
                      refine ⟨3999814554550027844838737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10666172145466740919569965 3999814554550027844838737)
                      ·
                        rfl

theorem cell23_7789611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 1, 3].length) (baseStart_7789611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789611 prefixEnd_7789611 := by exact prefixLift 7789611
  have htrace : WordTrace (prefixWord ++ tailWord_7789611) baseStart_7789611 baseEnd_7789611 := by
    simpa [prefixWord, tailWord_7789611, baseEnd_7789611] using wordTrace_append hprefix tailTrace_7789611
  have hstable : (prefixWord ++ tailWord_7789611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789611).length < 2 ^ (prefixWord ++ tailWord_7789611).sum := by decide
  have hdescent : baseEnd_7789611 < baseStart_7789611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789644 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 5, 6]
def baseStart_7789644 : Nat := 118140960795 + 7789644 * 2 ^ 59
def prefixEnd_7789644 : Nat := 4983230072969 + 3 ^ 40 * 7789644 * 2
def baseEnd_7789644 : Nat := 1333277166470542071908695

theorem tailTrace_7789644 : CollatzResearch.WordTrace tailWord_7789644 prefixEnd_7789644 1333277166470542071908695 := by
  unfold tailWord_7789644
  simp only [CollatzResearch.WordTrace]
  refine ⟨142055828695728814062259993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189407771594305085416346657 142055828695728814062259993)
  ·
    refine ⟨106541871521796610546694995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142055828695728814062259993 106541871521796610546694995)
    ·
      refine ⟨159812807282694915820042493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106541871521796610546694995 159812807282694915820042493)
      ·
        refine ⟨59929802731010593432515935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159812807282694915820042493 59929802731010593432515935)
        ·
          refine ⟨89894704096515890148773903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59929802731010593432515935 89894704096515890148773903)
          ·
            refine ⟨134842056144773835223160855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89894704096515890148773903 134842056144773835223160855)
            ·
              refine ⟨202263084217160752834741283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134842056144773835223160855 202263084217160752834741283)
              ·
                refine ⟨303394626325741129252111925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202263084217160752834741283 303394626325741129252111925)
                ·
                  refine ⟨28443246218038230867385493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 303394626325741129252111925 28443246218038230867385493)
                  ·
                    refine ⟨1333277166470542071908695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28443246218038230867385493 1333277166470542071908695)
                    ·
                      rfl

theorem cell23_7789644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_7789644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789644 prefixEnd_7789644 := by exact prefixLift 7789644
  have htrace : WordTrace (prefixWord ++ tailWord_7789644) baseStart_7789644 baseEnd_7789644 := by
    simpa [prefixWord, tailWord_7789644, baseEnd_7789644] using wordTrace_append hprefix tailTrace_7789644
  have hstable : (prefixWord ++ tailWord_7789644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789644).length < 2 ^ (prefixWord ++ tailWord_7789644).sum := by decide
  have hdescent : baseEnd_7789644 < baseStart_7789644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789662 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_7789662 : Nat := 118140960795 + 7789662 * 2 ^ 59
def prefixEnd_7789662 : Nat := 4983230072969 + 3 ^ 40 * 7789662 * 2
def baseEnd_7789662 : Nat := 3999840742063407145301003

theorem tailTrace_7789662 : CollatzResearch.WordTrace tailWord_7789662 prefixEnd_7789662 3999840742063407145301003 := by
  unfold tailWord_7789662
  simp only [CollatzResearch.WordTrace]
  refine ⟨35514039238174052149834405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189408209270261611465783493 35514039238174052149834405)
  ·
    refine ⟨6658882357157634778093951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35514039238174052149834405 6658882357157634778093951)
    ·
      refine ⟨9988323535736452167140927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6658882357157634778093951 9988323535736452167140927)
      ·
        refine ⟨14982485303604678250711391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9988323535736452167140927 14982485303604678250711391)
        ·
          refine ⟨22473727955407017376067087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14982485303604678250711391 22473727955407017376067087)
          ·
            refine ⟨33710591933110526064100631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22473727955407017376067087 33710591933110526064100631)
            ·
              refine ⟨50565887899665789096150947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33710591933110526064100631 50565887899665789096150947)
              ·
                refine ⟨75848831849498683644226421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50565887899665789096150947 75848831849498683644226421)
                ·
                  refine ⟨7110827985890501591646227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75848831849498683644226421 7110827985890501591646227)
                  ·
                    refine ⟨10666241978835752387469341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7110827985890501591646227 10666241978835752387469341)
                    ·
                      refine ⟨3999840742063407145301003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10666241978835752387469341 3999840742063407145301003)
                      ·
                        rfl

theorem cell23_7789662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_7789662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789662 prefixEnd_7789662 := by exact prefixLift 7789662
  have htrace : WordTrace (prefixWord ++ tailWord_7789662) baseStart_7789662 baseEnd_7789662 := by
    simpa [prefixWord, tailWord_7789662, baseEnd_7789662] using wordTrace_append hprefix tailTrace_7789662
  have hstable : (prefixWord ++ tailWord_7789662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789662).length < 2 ^ (prefixWord ++ tailWord_7789662).sum := by decide
  have hdescent : baseEnd_7789662 < baseStart_7789662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789735 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_7789735 : Nat := 118140960795 + 7789735 * 2 ^ 59
def prefixEnd_7789735 : Nat := 4983230072969 + 3 ^ 40 * 7789735 * 2
def baseEnd_7789735 : Nat := 3999878226151185359688167

theorem tailTrace_7789735 : CollatzResearch.WordTrace tailWord_7789735 prefixEnd_7789735 3999878226151185359688167 := by
  unfold tailWord_7789735
  simp only [CollatzResearch.WordTrace]
  refine ⟨284114976434127950666082659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189409984289418633777388439 284114976434127950666082659)
  ·
    refine ⟨426172464651191925999123989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284114976434127950666082659 426172464651191925999123989)
    ·
      refine ⟨19976834280524621531208937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 426172464651191925999123989 19976834280524621531208937)
      ·
        refine ⟨14982625710393466148406703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19976834280524621531208937 14982625710393466148406703)
        ·
          refine ⟨22473938565590199222610055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14982625710393466148406703 22473938565590199222610055)
          ·
            refine ⟨33710907848385298833915083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22473938565590199222610055 33710907848385298833915083)
            ·
              refine ⟨50566361772577948250872625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33710907848385298833915083 50566361772577948250872625)
              ·
                refine ⟨37924771329433461188154469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50566361772577948250872625 37924771329433461188154469)
                ·
                  refine ⟨7110894624268773972778963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37924771329433461188154469 7110894624268773972778963)
                  ·
                    refine ⟨10666341936403160959168445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7110894624268773972778963 10666341936403160959168445)
                    ·
                      refine ⟨3999878226151185359688167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10666341936403160959168445 3999878226151185359688167)
                      ·
                        rfl

theorem cell23_7789735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_7789735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789735 prefixEnd_7789735 := by exact prefixLift 7789735
  have htrace : WordTrace (prefixWord ++ tailWord_7789735) baseStart_7789735 baseEnd_7789735 := by
    simpa [prefixWord, tailWord_7789735, baseEnd_7789735] using wordTrace_append hprefix tailTrace_7789735
  have hstable : (prefixWord ++ tailWord_7789735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789735).length < 2 ^ (prefixWord ++ tailWord_7789735).sum := by decide
  have hdescent : baseEnd_7789735 < baseStart_7789735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789818 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2]
def baseStart_7789818 : Nat := 118140960795 + 7789818 * 2 ^ 59
def prefixEnd_7789818 : Nat := 4983230072969 + 3 ^ 40 * 7789818 * 2
def baseEnd_7789818 : Nat := 3999920845045508534950285

theorem tailTrace_7789818 : CollatzResearch.WordTrace tailWord_7789818 prefixEnd_7789818 3999920845045508534950285 := by
  unfold tailWord_7789818
  simp only [CollatzResearch.WordTrace]
  refine ⟨71029500923206813960338527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189412002461884837227569405 71029500923206813960338527)
  ·
    refine ⟨106544251384810220940507791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71029500923206813960338527 106544251384810220940507791)
    ·
      refine ⟨159816377077215331410761687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106544251384810220940507791 159816377077215331410761687)
      ·
        refine ⟨239724565615822997116142531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159816377077215331410761687 239724565615822997116142531)
        ·
          refine ⟨359586848423734495674213797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239724565615822997116142531 359586848423734495674213797)
          ·
            refine ⟨67422534079450217938915087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 359586848423734495674213797 67422534079450217938915087)
            ·
              refine ⟨101133801119175326908372631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67422534079450217938915087 101133801119175326908372631)
              ·
                refine ⟨151700701678762990362558947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101133801119175326908372631 151700701678762990362558947)
                ·
                  refine ⟨227551052518144485543838421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151700701678762990362558947 227551052518144485543838421)
                  ·
                    refine ⟨5333227793394011379933713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 227551052518144485543838421 5333227793394011379933713)
                    ·
                      refine ⟨3999920845045508534950285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5333227793394011379933713 3999920845045508534950285)
                      ·
                        rfl

theorem cell23_7789818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2].length) (baseStart_7789818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789818 prefixEnd_7789818 := by exact prefixLift 7789818
  have htrace : WordTrace (prefixWord ++ tailWord_7789818) baseStart_7789818 baseEnd_7789818 := by
    simpa [prefixWord, tailWord_7789818, baseEnd_7789818] using wordTrace_append hprefix tailTrace_7789818
  have hstable : (prefixWord ++ tailWord_7789818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789818).length < 2 ^ (prefixWord ++ tailWord_7789818).sum := by decide
  have hdescent : baseEnd_7789818 < baseStart_7789818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789848 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 1, 3, 4]
def baseStart_7789848 : Nat := 118140960795 + 7789848 * 2 ^ 59
def prefixEnd_7789848 : Nat := 4983230072969 + 3 ^ 40 * 7789848 * 2
def baseEnd_7789848 : Nat := 3999936249465143417575147

theorem tailTrace_7789848 : CollatzResearch.WordTrace tailWord_7789848 prefixEnd_7789848 3999936249465143417575147 := by
  unfold tailWord_7789848
  simp only [CollatzResearch.WordTrace]
  refine ⟨142059548941359285482473099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189412731921812380643297465 142059548941359285482473099)
  ·
    refine ⟨213089323412038928223709649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142059548941359285482473099 213089323412038928223709649)
    ·
      refine ⟨159816992559029196167782237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213089323412038928223709649 159816992559029196167782237)
      ·
        refine ⟨59931372209635948562918339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159816992559029196167782237 59931372209635948562918339)
        ·
          refine ⟨89897058314453922844377509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59931372209635948562918339 89897058314453922844377509)
          ·
            refine ⟨16855698433960110533320783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89897058314453922844377509 16855698433960110533320783)
            ·
              refine ⟨25283547650940165799981175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16855698433960110533320783 25283547650940165799981175)
              ·
                refine ⟨37925321476410248699971763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25283547650940165799981175 37925321476410248699971763)
                ·
                  refine ⟨56887982214615373049957645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37925321476410248699971763 56887982214615373049957645)
                  ·
                    refine ⟨21332993330480764893734117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56887982214615373049957645 21332993330480764893734117)
                    ·
                      refine ⟨3999936249465143417575147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21332993330480764893734117 3999936249465143417575147)
                      ·
                        rfl

theorem cell23_7789848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_7789848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789848 prefixEnd_7789848 := by exact prefixLift 7789848
  have htrace : WordTrace (prefixWord ++ tailWord_7789848) baseStart_7789848 baseEnd_7789848 := by
    simpa [prefixWord, tailWord_7789848, baseEnd_7789848] using wordTrace_append hprefix tailTrace_7789848
  have hstable : (prefixWord ++ tailWord_7789848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789848).length < 2 ^ (prefixWord ++ tailWord_7789848).sum := by decide
  have hdescent : baseEnd_7789848 < baseStart_7789848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789868 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 3]
def baseStart_7789868 : Nat := 118140960795 + 7789868 * 2 ^ 59
def prefixEnd_7789868 : Nat := 4983230072969 + 3 ^ 40 * 7789868 * 2
def baseEnd_7789868 : Nat := 3999946519078233339325055

theorem tailTrace_7789868 : CollatzResearch.WordTrace tailWord_7789868 prefixEnd_7789868 3999946519078233339325055 := by
  unfold tailWord_7789868
  simp only [CollatzResearch.WordTrace]
  refine ⟨142059913671323057190337129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189413218228430742920449505 142059913671323057190337129)
  ·
    refine ⟨106544935253492292892752847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142059913671323057190337129 106544935253492292892752847)
    ·
      refine ⟨159817402880238439339129271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106544935253492292892752847 159817402880238439339129271)
      ·
        refine ⟨239726104320357659008693907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159817402880238439339129271 239726104320357659008693907)
        ·
          refine ⟨359589156480536488513040861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239726104320357659008693907 359589156480536488513040861)
          ·
            refine ⟨134845933680201183192390323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359589156480536488513040861 134845933680201183192390323)
            ·
              refine ⟨202268900520301774788585485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134845933680201183192390323 202268900520301774788585485)
              ·
                refine ⟨75850837695113165545719557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202268900520301774788585485 75850837695113165545719557)
                ·
                  refine ⟨14222032067833718539822417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75850837695113165545719557 14222032067833718539822417)
                  ·
                    refine ⟨10666524050875288904866813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14222032067833718539822417 10666524050875288904866813)
                    ·
                      refine ⟨3999946519078233339325055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10666524050875288904866813 3999946519078233339325055)
                      ·
                        rfl

theorem cell23_7789868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_7789868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789868 prefixEnd_7789868 := by exact prefixLift 7789868
  have htrace : WordTrace (prefixWord ++ tailWord_7789868) baseStart_7789868 baseEnd_7789868 := by
    simpa [prefixWord, tailWord_7789868, baseEnd_7789868] using wordTrace_append hprefix tailTrace_7789868
  have hstable : (prefixWord ++ tailWord_7789868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789868).length < 2 ^ (prefixWord ++ tailWord_7789868).sum := by decide
  have hdescent : baseEnd_7789868 < baseStart_7789868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789875 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 3, 4]
def baseStart_7789875 : Nat := 118140960795 + 7789875 * 2 ^ 59
def prefixEnd_7789875 : Nat := 4983230072969 + 3 ^ 40 * 7789875 * 2
def baseEnd_7789875 : Nat := 1333316704480938270645841

theorem tailTrace_7789875 : CollatzResearch.WordTrace tailWord_7789875 prefixEnd_7789875 1333316704480938270645841 := by
  unfold tailWord_7789875
  simp only [CollatzResearch.WordTrace]
  refine ⟨284120082653620754576179079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189413388435747169717452719 284120082653620754576179079)
  ·
    refine ⟨426180123980431131864268619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284120082653620754576179079 426180123980431131864268619)
    ·
      refine ⟨639270185970646697796402929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426180123980431131864268619 639270185970646697796402929)
      ·
        refine ⟨479452639477985023347302197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639270185970646697796402929 479452639477985023347302197)
        ·
          refine ⟨44948684951061095938809581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 479452639477985023347302197 44948684951061095938809581)
          ·
            refine ⟨16855756856647910977053593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44948684951061095938809581 16855756856647910977053593)
            ·
              refine ⟨12641817642485933232790195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16855756856647910977053593 12641817642485933232790195)
              ·
                refine ⟨18962726463728899849185293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12641817642485933232790195 18962726463728899849185293)
                ·
                  refine ⟨7111022423898337443444485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18962726463728899849185293 7111022423898337443444485)
                  ·
                    refine ⟨1333316704480938270645841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7111022423898337443444485 1333316704480938270645841)
                    ·
                      rfl

theorem cell23_7789875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 4].length) (baseStart_7789875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789875 prefixEnd_7789875 := by exact prefixLift 7789875
  have htrace : WordTrace (prefixWord ++ tailWord_7789875) baseStart_7789875 baseEnd_7789875 := by
    simpa [prefixWord, tailWord_7789875, baseEnd_7789875] using wordTrace_append hprefix tailTrace_7789875
  have hstable : (prefixWord ++ tailWord_7789875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789875).length < 2 ^ (prefixWord ++ tailWord_7789875).sum := by decide
  have hdescent : baseEnd_7789875 < baseStart_7789875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789891 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 6]
def baseStart_7789891 : Nat := 118140960795 + 7789891 * 2 ^ 59
def prefixEnd_7789891 : Nat := 4983230072969 + 3 ^ 40 * 7789891 * 2
def baseEnd_7789891 : Nat := 3999958329133286749337449

theorem tailTrace_7789891 : CollatzResearch.WordTrace tailWord_7789891 prefixEnd_7789891 3999958329133286749337449 := by
  unfold tailWord_7789891
  simp only [CollatzResearch.WordTrace]
  refine ⟨284120666221562789308761527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189413777481041859539174351 284120666221562789308761527)
  ·
    refine ⟨426180999332344183963142291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284120666221562789308761527 426180999332344183963142291)
    ·
      refine ⟨639271498998516275944713437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426180999332344183963142291 639271498998516275944713437)
      ·
        refine ⟨239726812124443603479267539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639271498998516275944713437 239726812124443603479267539)
        ·
          refine ⟨359590218186665405218901309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239726812124443603479267539 359590218186665405218901309)
          ·
            refine ⟨134846331819999526957087991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359590218186665405218901309 134846331819999526957087991)
            ·
              refine ⟨202269497729999290435631987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134846331819999526957087991 202269497729999290435631987)
              ·
                refine ⟨303404246594998935653447981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202269497729999290435631987 303404246594998935653447981)
                ·
                  refine ⟨113776592473124600870042993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303404246594998935653447981 113776592473124600870042993)
                  ·
                    refine ⟨85332444354843450652532245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113776592473124600870042993 85332444354843450652532245)
                    ·
                      refine ⟨3999958329133286749337449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85332444354843450652532245 3999958329133286749337449)
                      ·
                        rfl

theorem cell23_7789891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_7789891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789891 prefixEnd_7789891 := by exact prefixLift 7789891
  have htrace : WordTrace (prefixWord ++ tailWord_7789891) baseStart_7789891 baseEnd_7789891 := by
    simpa [prefixWord, tailWord_7789891, baseEnd_7789891] using wordTrace_append hprefix tailTrace_7789891
  have hstable : (prefixWord ++ tailWord_7789891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789891).length < 2 ^ (prefixWord ++ tailWord_7789891).sum := by decide
  have hdescent : baseEnd_7789891 < baseStart_7789891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789892 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_7789892 : Nat := 118140960795 + 7789892 * 2 ^ 59
def prefixEnd_7789892 : Nat := 4983230072969 + 3 ^ 40 * 7789892 * 2
def baseEnd_7789892 : Nat := 1333319614204647081808315

theorem tailTrace_7789892 : CollatzResearch.WordTrace tailWord_7789892 prefixEnd_7789892 1333319614204647081808315 := by
  unfold tailWord_7789892
  simp only [CollatzResearch.WordTrace]
  refine ⟨142060351347279583239773965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189413801796372777653031953 142060351347279583239773965)
  ·
    refine ⟨53272631755229843714915237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142060351347279583239773965 53272631755229843714915237)
    ·
      refine ⟨9988618454105595696546607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53272631755229843714915237 9988618454105595696546607)
      ·
        refine ⟨14982927681158393544819911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9988618454105595696546607 14982927681158393544819911)
        ·
          refine ⟨22474391521737590317229867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14982927681158393544819911 22474391521737590317229867)
          ·
            refine ⟨33711587282606385475844801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22474391521737590317229867 33711587282606385475844801)
            ·
              refine ⟨25283690461954789106883601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33711587282606385475844801 25283690461954789106883601)
              ·
                refine ⟨18962767846466091830162701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25283690461954789106883601 18962767846466091830162701)
                ·
                  refine ⟨7111037942424784436311013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18962767846466091830162701 7111037942424784436311013)
                  ·
                    refine ⟨1333319614204647081808315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7111037942424784436311013 1333319614204647081808315)
                    ·
                      rfl

theorem cell23_7789892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_7789892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789892 prefixEnd_7789892 := by exact prefixLift 7789892
  have htrace : WordTrace (prefixWord ++ tailWord_7789892) baseStart_7789892 baseEnd_7789892 := by
    simpa [prefixWord, tailWord_7789892, baseEnd_7789892] using wordTrace_append hprefix tailTrace_7789892
  have hstable : (prefixWord ++ tailWord_7789892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789892).length < 2 ^ (prefixWord ++ tailWord_7789892).sum := by decide
  have hdescent : baseEnd_7789892 < baseStart_7789892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789909 : List Nat := [1, 3, 2, 2, 3, 3, 1, 3, 1, 4]
def baseStart_7789909 : Nat := 118140960795 + 7789909 * 2 ^ 59
def prefixEnd_7789909 : Nat := 4983230072969 + 3 ^ 40 * 7789909 * 2
def baseEnd_7789909 : Nat := 1333322523928355892970789

theorem tailTrace_7789909 : CollatzResearch.WordTrace tailWord_7789909 prefixEnd_7789909 1333322523928355892970789 := by
  unfold tailWord_7789909
  simp only [CollatzResearch.WordTrace]
  refine ⟨284121322735497578382916781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189414215156998385588611187 284121322735497578382916781)
  ·
    refine ⟨106545496025811591893593793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284121322735497578382916781 106545496025811591893593793)
    ·
      refine ⟨79909122019358693920195345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106545496025811591893593793 79909122019358693920195345)
      ·
        refine ⟨59931841514519020440146509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79909122019358693920195345 59931841514519020440146509)
        ·
          refine ⟨22474440567944632665054941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59931841514519020440146509 22474440567944632665054941)
          ·
            refine ⟨8427915212979237249395603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22474440567944632665054941 8427915212979237249395603)
            ·
              refine ⟨12641872819468855874093405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8427915212979237249395603 12641872819468855874093405)
              ·
                refine ⟨4740702307300820952785027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12641872819468855874093405 4740702307300820952785027)
                ·
                  refine ⟨7111053460951231429177541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4740702307300820952785027 7111053460951231429177541)
                  ·
                    refine ⟨1333322523928355892970789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7111053460951231429177541 1333322523928355892970789)
                    ·
                      rfl

theorem cell23_7789909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_7789909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789909 prefixEnd_7789909 := by exact prefixLift 7789909
  have htrace : WordTrace (prefixWord ++ tailWord_7789909) baseStart_7789909 baseEnd_7789909 := by
    simpa [prefixWord, tailWord_7789909, baseEnd_7789909] using wordTrace_append hprefix tailTrace_7789909
  have hstable : (prefixWord ++ tailWord_7789909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789909).length < 2 ^ (prefixWord ++ tailWord_7789909).sum := by decide
  have hdescent : baseEnd_7789909 < baseStart_7789909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789931 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 2, 10]
def baseStart_7789931 : Nat := 118140960795 + 7789931 * 2 ^ 59
def prefixEnd_7789931 : Nat := 4983230072969 + 3 ^ 40 * 7789931 * 2
def baseEnd_7789931 : Nat := 1333326289453155530945755

theorem tailTrace_7789931 : CollatzResearch.WordTrace tailWord_7789931 prefixEnd_7789931 1333326289453155530945755 := by
  unfold tailWord_7789931
  simp only [CollatzResearch.WordTrace]
  refine ⟨284122125141417876140217647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189414750094278584093478431 284122125141417876140217647)
  ·
    refine ⟨426183187712126814210326471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284122125141417876140217647 426183187712126814210326471)
    ·
      refine ⟨639274781568190221315489707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426183187712126814210326471 639274781568190221315489707)
      ·
        refine ⟨958912172352285331973234561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639274781568190221315489707 958912172352285331973234561)
        ·
          refine ⟨719184129264213998979925921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 958912172352285331973234561 719184129264213998979925921)
          ·
            refine ⟨539388096948160499234944441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 719184129264213998979925921 539388096948160499234944441)
            ·
              refine ⟨404541072711120374426208331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539388096948160499234944441 404541072711120374426208331)
              ·
                refine ⟨606811609066680561639312497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404541072711120374426208331 606811609066680561639312497)
                ·
                  refine ⟨455108706800010421229484373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606811609066680561639312497 455108706800010421229484373)
                  ·
                    refine ⟨1333326289453155530945755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 455108706800010421229484373 1333326289453155530945755)
                    ·
                      rfl

theorem cell23_7789931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 10].length) (baseStart_7789931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789931 prefixEnd_7789931 := by exact prefixLift 7789931
  have htrace : WordTrace (prefixWord ++ tailWord_7789931) baseStart_7789931 baseEnd_7789931 := by
    simpa [prefixWord, tailWord_7789931, baseEnd_7789931] using wordTrace_append hprefix tailTrace_7789931
  have hstable : (prefixWord ++ tailWord_7789931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789931).length < 2 ^ (prefixWord ++ tailWord_7789931).sum := by decide
  have hdescent : baseEnd_7789931 < baseStart_7789931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789932 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 3]
def baseStart_7789932 : Nat := 118140960795 + 7789932 * 2 ^ 59
def prefixEnd_7789932 : Nat := 4983230072969 + 3 ^ 40 * 7789932 * 2
def baseEnd_7789932 : Nat := 3999979381840121088924761

theorem tailTrace_7789932 : CollatzResearch.WordTrace tailWord_7789932 prefixEnd_7789932 3999979381840121088924761 := by
  unfold tailWord_7789932
  simp only [CollatzResearch.WordTrace]
  refine ⟨142061080807207126655502025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189414774409609502207336033 142061080807207126655502025)
  ·
    refine ⟨106545810605405344991626519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142061080807207126655502025 106545810605405344991626519)
    ·
      refine ⟨159818715908108017487439779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106545810605405344991626519 159818715908108017487439779)
      ·
        refine ⟨239728073862162026231159669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159818715908108017487439779 239728073862162026231159669)
        ·
          refine ⟨22474506924577689959171219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239728073862162026231159669 22474506924577689959171219)
          ·
            refine ⟨33711760386866534938756829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22474506924577689959171219 33711760386866534938756829)
            ·
              refine ⟨12641910145074950602033811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33711760386866534938756829 12641910145074950602033811)
              ·
                refine ⟨18962865217612425903050717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12641910145074950602033811 18962865217612425903050717)
                ·
                  refine ⟨7111074456604659713644019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18962865217612425903050717 7111074456604659713644019)
                  ·
                    refine ⟨10666611684906989570466029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7111074456604659713644019 10666611684906989570466029)
                    ·
                      refine ⟨3999979381840121088924761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10666611684906989570466029 3999979381840121088924761)
                      ·
                        rfl

theorem cell23_7789932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_7789932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789932 prefixEnd_7789932 := by exact prefixLift 7789932
  have htrace : WordTrace (prefixWord ++ tailWord_7789932) baseStart_7789932 baseEnd_7789932 := by
    simpa [prefixWord, tailWord_7789932, baseEnd_7789932] using wordTrace_append hprefix tailTrace_7789932
  have hstable : (prefixWord ++ tailWord_7789932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789932).length < 2 ^ (prefixWord ++ tailWord_7789932).sum := by decide
  have hdescent : baseEnd_7789932 < baseStart_7789932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789948 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 1, 6]
def baseStart_7789948 : Nat := 118140960795 + 7789948 * 2 ^ 59
def prefixEnd_7789948 : Nat := 4983230072969 + 3 ^ 40 * 7789948 * 2
def baseEnd_7789948 : Nat := 1333329199176864342108229

theorem tailTrace_7789948 : CollatzResearch.WordTrace tailWord_7789948 prefixEnd_7789948 1333329199176864342108229 := by
  unfold tailWord_7789948
  simp only [CollatzResearch.WordTrace]
  refine ⟨142061372591178144021793249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189415163454904192029057665 142061372591178144021793249)
  ·
    refine ⟨106546029443383608016344937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142061372591178144021793249 106546029443383608016344937)
    ·
      refine ⟨79909522082537706012258703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106546029443383608016344937 79909522082537706012258703)
      ·
        refine ⟨119864283123806559018388055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79909522082537706012258703 119864283123806559018388055)
        ·
          refine ⟨179796424685709838527582083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119864283123806559018388055 179796424685709838527582083)
          ·
            refine ⟨269694637028564757791373125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179796424685709838527582083 269694637028564757791373125)
            ·
              refine ⟨50567744442855892085882461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269694637028564757791373125 50567744442855892085882461)
              ·
                refine ⟨18962904166070959532205923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50567744442855892085882461 18962904166070959532205923)
                ·
                  refine ⟨28444356249106439298308885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18962904166070959532205923 28444356249106439298308885)
                  ·
                    refine ⟨1333329199176864342108229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28444356249106439298308885 1333329199176864342108229)
                    ·
                      rfl

theorem cell23_7789948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_7789948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789948 prefixEnd_7789948 := by exact prefixLift 7789948
  have htrace : WordTrace (prefixWord ++ tailWord_7789948) baseStart_7789948 baseEnd_7789948 := by
    simpa [prefixWord, tailWord_7789948, baseEnd_7789948] using wordTrace_append hprefix tailTrace_7789948
  have hstable : (prefixWord ++ tailWord_7789948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789948).length < 2 ^ (prefixWord ++ tailWord_7789948).sum := by decide
  have hdescent : baseEnd_7789948 < baseStart_7789948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789955 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 4]
def baseStart_7789955 : Nat := 118140960795 + 7789955 * 2 ^ 59
def prefixEnd_7789955 : Nat := 4983230072969 + 3 ^ 40 * 7789955 * 2
def baseEnd_7789955 : Nat := 3999991191895174498937155

theorem tailTrace_7789955 : CollatzResearch.WordTrace tailWord_7789955 prefixEnd_7789955 3999991191895174498937155 := by
  unfold tailWord_7789955
  simp only [CollatzResearch.WordTrace]
  refine ⟨284123000493330928239091319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189415333662220618826060879 284123000493330928239091319)
  ·
    refine ⟨426184500739996392358636979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284123000493330928239091319 426184500739996392358636979)
    ·
      refine ⟨639276751109994588537955469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426184500739996392358636979 639276751109994588537955469)
      ·
        refine ⟨239728781666247970701733301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639276751109994588537955469 239728781666247970701733301)
        ·
          refine ⟨22474573281210747253287497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239728781666247970701733301 22474573281210747253287497)
          ·
            refine ⟨16855929960908060439965623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22474573281210747253287497 16855929960908060439965623)
            ·
              refine ⟨25283894941362090659948435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16855929960908060439965623 25283894941362090659948435)
              ·
                refine ⟨37925842412043135989922653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25283894941362090659948435 37925842412043135989922653)
                ·
                  refine ⟨14222190904516175996220995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37925842412043135989922653 14222190904516175996220995)
                  ·
                    refine ⟨21333286356774263994331493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14222190904516175996220995 21333286356774263994331493)
                    ·
                      refine ⟨3999991191895174498937155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21333286356774263994331493 3999991191895174498937155)
                      ·
                        rfl

theorem cell23_7789955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_7789955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7789955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7789955 prefixEnd_7789955 := by exact prefixLift 7789955
  have htrace : WordTrace (prefixWord ++ tailWord_7789955) baseStart_7789955 baseEnd_7789955 := by
    simpa [prefixWord, tailWord_7789955, baseEnd_7789955] using wordTrace_append hprefix tailTrace_7789955
  have hstable : (prefixWord ++ tailWord_7789955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789955).length < 2 ^ (prefixWord ++ tailWord_7789955).sum := by decide
  have hdescent : baseEnd_7789955 < baseStart_7789955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790012 : List Nat := [2, 2, 2, 4, 2, 1, 3, 7]
def baseStart_7790012 : Nat := 118140960795 + 7790012 * 2 ^ 59
def prefixEnd_7790012 : Nat := 4983230072969 + 3 ^ 40 * 7790012 * 2
def baseEnd_7790012 : Nat := 148148905936758547256459

theorem tailTrace_7790012 : CollatzResearch.WordTrace tailWord_7790012 prefixEnd_7790012 148148905936758547256459 := by
  unfold tailWord_7790012
  simp only [CollatzResearch.WordTrace]
  refine ⟨142062539727062213486958145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189416719636082951315944193 142062539727062213486958145)
  ·
    refine ⟨106546904795296660115218609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142062539727062213486958145 106546904795296660115218609)
    ·
      refine ⟨79910178596472495086413957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106546904795296660115218609 79910178596472495086413957)
      ·
        refine ⟨14983158486838592828702617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79910178596472495086413957 14983158486838592828702617)
        ·
          refine ⟨11237368865128944621526963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14983158486838592828702617 11237368865128944621526963)
          ·
            refine ⟨16856053297693416932290445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11237368865128944621526963 16856053297693416932290445)
            ·
              refine ⟨6321019986635031349608917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16856053297693416932290445 6321019986635031349608917)
              ·
                refine ⟨148148905936758547256459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6321019986635031349608917 148148905936758547256459)
                ·
                  rfl

theorem cell23_7790012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 7].length) (baseStart_7790012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790012 prefixEnd_7790012 := by exact prefixLift 7790012
  have htrace : WordTrace (prefixWord ++ tailWord_7790012) baseStart_7790012 baseEnd_7790012 := by
    simpa [prefixWord, tailWord_7790012, baseEnd_7790012] using wordTrace_append hprefix tailTrace_7790012
  have hstable : (prefixWord ++ tailWord_7790012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790012).length < 2 ^ (prefixWord ++ tailWord_7790012).sum := by decide
  have hdescent : baseEnd_7790012 < baseStart_7790012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790032 : List Nat := [2, 1, 1, 1, 1, 2, 2, 7, 1, 3, 2]
def baseStart_7790032 : Nat := 118140960795 + 7790032 * 2 ^ 59
def prefixEnd_7790032 : Nat := 4983230072969 + 3 ^ 40 * 7790032 * 2
def baseEnd_7790032 : Nat := 4000030729905570697674301

theorem tailTrace_7790032 : CollatzResearch.WordTrace tailWord_7790032 prefixEnd_7790032 4000030729905570697674301 := by
  unfold tailWord_7790032
  simp only [CollatzResearch.WordTrace]
  refine ⟨142062904457025985194822175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189417205942701313593096233 142062904457025985194822175)
  ·
    refine ⟨213094356685538977792233263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142062904457025985194822175 213094356685538977792233263)
    ·
      refine ⟨319641535028308466688349895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213094356685538977792233263 319641535028308466688349895)
      ·
        refine ⟨479462302542462700032524843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319641535028308466688349895 479462302542462700032524843)
        ·
          refine ⟨719193453813694050048787265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479462302542462700032524843 719193453813694050048787265)
          ·
            refine ⟨539395090360270537536590449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 719193453813694050048787265 539395090360270537536590449)
            ·
              refine ⟨404546317770202903152442837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539395090360270537536590449 404546317770202903152442837)
              ·
                refine ⟨9481554322739130542635379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 404546317770202903152442837 9481554322739130542635379)
                ·
                  refine ⟨14222331484108695813953069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9481554322739130542635379 14222331484108695813953069)
                  ·
                    refine ⟨5333374306540760930232401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14222331484108695813953069 5333374306540760930232401)
                    ·
                      refine ⟨4000030729905570697674301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5333374306540760930232401 4000030729905570697674301)
                      ·
                        rfl

theorem cell23_7790032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 1, 3, 2].length) (baseStart_7790032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790032 prefixEnd_7790032 := by exact prefixLift 7790032
  have htrace : WordTrace (prefixWord ++ tailWord_7790032) baseStart_7790032 baseEnd_7790032 := by
    simpa [prefixWord, tailWord_7790032, baseEnd_7790032] using wordTrace_append hprefix tailTrace_7790032
  have hstable : (prefixWord ++ tailWord_7790032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790032).length < 2 ^ (prefixWord ++ tailWord_7790032).sum := by decide
  have hdescent : baseEnd_7790032 < baseStart_7790032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790048 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 5]
def baseStart_7790048 : Nat := 118140960795 + 7790048 * 2 ^ 59
def prefixEnd_7790048 : Nat := 4983230072969 + 3 ^ 40 * 7790048 * 2
def baseEnd_7790048 : Nat := 4000038945596042635074227

theorem tailTrace_7790048 : CollatzResearch.WordTrace tailWord_7790048 prefixEnd_7790048 4000038945596042635074227 := by
  unfold tailWord_7790048
  simp only [CollatzResearch.WordTrace]
  refine ⟨142063196240997002561113399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189417594987996003414817865 142063196240997002561113399)
  ·
    refine ⟨213094794361495503841670099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142063196240997002561113399 213094794361495503841670099)
    ·
      refine ⟨319642191542243255762505149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213094794361495503841670099 319642191542243255762505149)
      ·
        refine ⟨119865821828341220910939431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319642191542243255762505149 119865821828341220910939431)
        ·
          refine ⟨179798732742511831366409147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119865821828341220910939431 179798732742511831366409147)
          ·
            refine ⟨269698099113767747049613721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179798732742511831366409147 269698099113767747049613721)
            ·
              refine ⟨202273574335325810287210291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269698099113767747049613721 202273574335325810287210291)
              ·
                refine ⟨303410361502988715430815437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202273574335325810287210291 303410361502988715430815437)
                ·
                  refine ⟨113778885563620768286555789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303410361502988715430815437 113778885563620768286555789)
                  ·
                    refine ⟨42667082086357788107458421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113778885563620768286555789 42667082086357788107458421)
                    ·
                      refine ⟨4000038945596042635074227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42667082086357788107458421 4000038945596042635074227)
                      ·
                        rfl

theorem cell23_7790048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_7790048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790048 prefixEnd_7790048 := by exact prefixLift 7790048
  have htrace : WordTrace (prefixWord ++ tailWord_7790048) baseStart_7790048 baseEnd_7790048 := by
    simpa [prefixWord, tailWord_7790048, baseEnd_7790048] using wordTrace_append hprefix tailTrace_7790048
  have hstable : (prefixWord ++ tailWord_7790048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790048).length < 2 ^ (prefixWord ++ tailWord_7790048).sum := by decide
  have hdescent : baseEnd_7790048 < baseStart_7790048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790055 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 2, 6]
def baseStart_7790055 : Nat := 118140960795 + 7790055 * 2 ^ 59
def prefixEnd_7790055 : Nat := 4983230072969 + 3 ^ 40 * 7790055 * 2
def baseEnd_7790055 : Nat := 1333347513320208035895565

theorem tailTrace_7790055 : CollatzResearch.WordTrace tailWord_7790055 prefixEnd_7790055 1333347513320208035895565 := by
  unfold tailWord_7790055
  simp only [CollatzResearch.WordTrace]
  refine ⟨284126647792968645317731619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189417765195312430211821079 284126647792968645317731619)
  ·
    refine ⟨426189971689452967976597429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284126647792968645317731619 426189971689452967976597429)
    ·
      refine ⟨39955309845886215747806009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 426189971689452967976597429 39955309845886215747806009)
      ·
        refine ⟨29966482384414661810854507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39955309845886215747806009 29966482384414661810854507)
        ·
          refine ⟨44949723576621992716281761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29966482384414661810854507 44949723576621992716281761)
          ·
            refine ⟨33712292682466494537211321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44949723576621992716281761 33712292682466494537211321)
            ·
              refine ⟨25284219511849870902908491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33712292682466494537211321 25284219511849870902908491)
              ·
                refine ⟨37926329267774806354362737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25284219511849870902908491 37926329267774806354362737)
                ·
                  refine ⟨28444746950831104765772053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37926329267774806354362737 28444746950831104765772053)
                  ·
                    refine ⟨1333347513320208035895565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28444746950831104765772053 1333347513320208035895565)
                    ·
                      rfl

theorem cell23_7790055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_7790055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790055 prefixEnd_7790055 := by exact prefixLift 7790055
  have htrace : WordTrace (prefixWord ++ tailWord_7790055) baseStart_7790055 baseEnd_7790055 := by
    simpa [prefixWord, tailWord_7790055, baseEnd_7790055] using wordTrace_append hprefix tailTrace_7790055
  have hstable : (prefixWord ++ tailWord_7790055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790055).length < 2 ^ (prefixWord ++ tailWord_7790055).sum := by decide
  have hdescent : baseEnd_7790055 < baseStart_7790055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790066 : List Nat := [3, 2, 1, 4, 1, 2, 2, 2, 1, 3, 2]
def baseStart_7790066 : Nat := 118140960795 + 7790066 * 2 ^ 59
def prefixEnd_7790066 : Nat := 4983230072969 + 3 ^ 40 * 7790066 * 2
def baseEnd_7790066 : Nat := 4000048188247823564649145

theorem tailTrace_7790066 : CollatzResearch.WordTrace tailWord_7790066 prefixEnd_7790066 4000048188247823564649145 := by
  unfold tailWord_7790066
  simp only [CollatzResearch.WordTrace]
  refine ⟨71031762248982198549095513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189418032663952529464254701 71031762248982198549095513)
  ·
    refine ⟨53273821686736648911821635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71031762248982198549095513 53273821686736648911821635)
    ·
      refine ⟨79910732530104973367732453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53273821686736648911821635 79910732530104973367732453)
      ·
        refine ⟨14983262349394682506449835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79910732530104973367732453 14983262349394682506449835)
        ·
          refine ⟨22474893524092023759674753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14983262349394682506449835 22474893524092023759674753)
          ·
            refine ⟨16856170143069017819756065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22474893524092023759674753 16856170143069017819756065)
            ·
              refine ⟨12642127607301763364817049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16856170143069017819756065 12642127607301763364817049)
              ·
                refine ⟨9481595705476322523612787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12642127607301763364817049 9481595705476322523612787)
                ·
                  refine ⟨14222393558214483785419181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9481595705476322523612787 14222393558214483785419181)
                  ·
                    refine ⟨5333397584330431419532193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14222393558214483785419181 5333397584330431419532193)
                    ·
                      refine ⟨4000048188247823564649145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5333397584330431419532193 4000048188247823564649145)
                      ·
                        rfl

theorem cell23_7790066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_7790066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790066 prefixEnd_7790066 := by exact prefixLift 7790066
  have htrace : WordTrace (prefixWord ++ tailWord_7790066) baseStart_7790066 baseEnd_7790066 := by
    simpa [prefixWord, tailWord_7790066, baseEnd_7790066] using wordTrace_append hprefix tailTrace_7790066
  have hstable : (prefixWord ++ tailWord_7790066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790066).length < 2 ^ (prefixWord ++ tailWord_7790066).sum := by decide
  have hdescent : baseEnd_7790066 < baseStart_7790066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790082 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_7790082 : Nat := 118140960795 + 7790082 * 2 ^ 59
def prefixEnd_7790082 : Nat := 4983230072969 + 3 ^ 40 * 7790082 * 2
def baseEnd_7790082 : Nat := 4000056403938295502049071

theorem tailTrace_7790082 : CollatzResearch.WordTrace tailWord_7790082 prefixEnd_7790082 4000056403938295502049071 := by
  unfold tailWord_7790082
  simp only [CollatzResearch.WordTrace]
  refine ⟨71031908140967707232241125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189418421709247219285976333 71031908140967707232241125)
  ·
    refine ⟨13318482776431445106045211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71031908140967707232241125 13318482776431445106045211)
    ·
      refine ⟨19977724164647167659067817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13318482776431445106045211 19977724164647167659067817)
      ·
        refine ⟨14983293123485375744300863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19977724164647167659067817 14983293123485375744300863)
        ·
          refine ⟨22474939685228063616451295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14983293123485375744300863 22474939685228063616451295)
          ·
            refine ⟨33712409527842095424676943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22474939685228063616451295 33712409527842095424676943)
            ·
              refine ⟨50568614291763143137015415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33712409527842095424676943 50568614291763143137015415)
              ·
                refine ⟨75852921437644714705523123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50568614291763143137015415 75852921437644714705523123)
                ·
                  refine ⟨113779382156467072058284685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75852921437644714705523123 113779382156467072058284685)
                  ·
                    refine ⟨42667268308675152021856757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113779382156467072058284685 42667268308675152021856757)
                    ·
                      refine ⟨4000056403938295502049071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42667268308675152021856757 4000056403938295502049071)
                      ·
                        rfl

theorem cell23_7790082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_7790082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790082 prefixEnd_7790082 := by exact prefixLift 7790082
  have htrace : WordTrace (prefixWord ++ tailWord_7790082) baseStart_7790082 baseEnd_7790082 := by
    simpa [prefixWord, tailWord_7790082, baseEnd_7790082] using wordTrace_append hprefix tailTrace_7790082
  have hstable : (prefixWord ++ tailWord_7790082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790082).length < 2 ^ (prefixWord ++ tailWord_7790082).sum := by decide
  have hdescent : baseEnd_7790082 < baseStart_7790082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790113 : List Nat := [1, 2, 3, 2, 2, 4, 2, 1, 2, 2, 2]
def baseStart_7790113 : Nat := 118140960795 + 7790113 * 2 ^ 59
def prefixEnd_7790113 : Nat := 4983230072969 + 3 ^ 40 * 7790113 * 2
def baseEnd_7790113 : Nat := 4000072321838584880761429

theorem tailTrace_7790113 : CollatzResearch.WordTrace tailWord_7790113 prefixEnd_7790113 4000072321838584880761429 := by
  unfold tailWord_7790113
  simp only [CollatzResearch.WordTrace]
  refine ⟨284128763226758521223342993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189419175484505680815561995 284128763226758521223342993)
  ·
    refine ⟨213096572420068890917507245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284128763226758521223342993 213096572420068890917507245)
    ·
      refine ⟨79911214657525834094065217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213096572420068890917507245 79911214657525834094065217)
      ·
        refine ⟨59933410993144375570548913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79911214657525834094065217 59933410993144375570548913)
        ·
          refine ⟨44950058244858281677911685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59933410993144375570548913 44950058244858281677911685)
          ·
            refine ⟨8428135920910927814608441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44950058244858281677911685 8428135920910927814608441)
            ·
              refine ⟨6321101940683195860956331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8428135920910927814608441 6321101940683195860956331)
              ·
                refine ⟨9481652911024793791434497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321101940683195860956331 9481652911024793791434497)
                ·
                  refine ⟨7111239683268595343575873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9481652911024793791434497 7111239683268595343575873)
                  ·
                    refine ⟨5333429762451446507681905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7111239683268595343575873 5333429762451446507681905)
                    ·
                      refine ⟨4000072321838584880761429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5333429762451446507681905 4000072321838584880761429)
                      ·
                        rfl

theorem cell23_7790113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_7790113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790113 prefixEnd_7790113 := by exact prefixLift 7790113
  have htrace : WordTrace (prefixWord ++ tailWord_7790113) baseStart_7790113 baseEnd_7790113 := by
    simpa [prefixWord, tailWord_7790113, baseEnd_7790113] using wordTrace_append hprefix tailTrace_7790113
  have hstable : (prefixWord ++ tailWord_7790113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790113).length < 2 ^ (prefixWord ++ tailWord_7790113).sum := by decide
  have hdescent : baseEnd_7790113 < baseStart_7790113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790155 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 3]
def baseStart_7790155 : Nat := 118140960795 + 7790155 * 2 ^ 59
def prefixEnd_7790155 : Nat := 4983230072969 + 3 ^ 40 * 7790155 * 2
def baseEnd_7790155 : Nat := 4000093888026073716436235

theorem tailTrace_7790155 : CollatzResearch.WordTrace tailWord_7790155 prefixEnd_7790155 4000093888026073716436235 := by
  unfold tailWord_7790155
  simp only [CollatzResearch.WordTrace]
  refine ⟨284130295092606362396371919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189420196728404241597581279 284130295092606362396371919)
  ·
    refine ⟨426195442638909543594557879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284130295092606362396371919 426195442638909543594557879)
    ·
      refine ⟨639293163958364315391836819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426195442638909543594557879 639293163958364315391836819)
      ·
        refine ⟨958939745937546473087755229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639293163958364315391836819 958939745937546473087755229)
        ·
          refine ⟨359602404726579927407908211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 958939745937546473087755229 359602404726579927407908211)
          ·
            refine ⟨539403607089869891111862317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359602404726579927407908211 539403607089869891111862317)
            ·
              refine ⟨202276352658701209166948369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 539403607089869891111862317 202276352658701209166948369)
              ·
                refine ⟨151707264494025906875211277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202276352658701209166948369 151707264494025906875211277)
                ·
                  refine ⟨56890224185259715078204229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151707264494025906875211277 56890224185259715078204229)
                  ·
                    refine ⟨10666917034736196577163293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56890224185259715078204229 10666917034736196577163293)
                    ·
                      refine ⟨4000093888026073716436235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10666917034736196577163293 4000093888026073716436235)
                      ·
                        rfl

theorem cell23_7790155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 3].length) (baseStart_7790155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790155 prefixEnd_7790155 := by exact prefixLift 7790155
  have htrace : WordTrace (prefixWord ++ tailWord_7790155) baseStart_7790155 baseEnd_7790155 := by
    simpa [prefixWord, tailWord_7790155, baseEnd_7790155] using wordTrace_append hprefix tailTrace_7790155
  have hstable : (prefixWord ++ tailWord_7790155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790155).length < 2 ^ (prefixWord ++ tailWord_7790155).sum := by decide
  have hdescent : baseEnd_7790155 < baseStart_7790155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790165 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_7790165 : Nat := 118140960795 + 7790165 * 2 ^ 59
def prefixEnd_7790165 : Nat := 4983230072969 + 3 ^ 40 * 7790165 * 2
def baseEnd_7790165 : Nat := 4000099022832618677311189

theorem tailTrace_7790165 : CollatzResearch.WordTrace tailWord_7790165 prefixEnd_7790165 4000099022832618677311189 := by
  unfold tailWord_7790165
  simp only [CollatzResearch.WordTrace]
  refine ⟨284130659822570134104235949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189420439881713422736157299 284130659822570134104235949)
  ·
    refine ⟨106548997433463800289088481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284130659822570134104235949 106548997433463800289088481)
    ·
      refine ⟨79911748075097850216816361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106548997433463800289088481 79911748075097850216816361)
      ·
        refine ⟨59933811056323387662612271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79911748075097850216816361 59933811056323387662612271)
        ·
          refine ⟨89900716584485081493918407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59933811056323387662612271 89900716584485081493918407)
          ·
            refine ⟨134851074876727622240877611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89900716584485081493918407 134851074876727622240877611)
            ·
              refine ⟨202276612315091433361316417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134851074876727622240877611 202276612315091433361316417)
              ·
                refine ⟨151707459236318575020987313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202276612315091433361316417 151707459236318575020987313)
                ·
                  refine ⟨113780594427238931265740485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151707459236318575020987313 113780594427238931265740485)
                  ·
                    refine ⟨21333861455107299612326341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113780594427238931265740485 21333861455107299612326341)
                    ·
                      refine ⟨4000099022832618677311189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21333861455107299612326341 4000099022832618677311189)
                      ·
                        rfl

theorem cell23_7790165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_7790165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790165 prefixEnd_7790165 := by exact prefixLift 7790165
  have htrace : WordTrace (prefixWord ++ tailWord_7790165) baseStart_7790165 baseEnd_7790165 := by
    simpa [prefixWord, tailWord_7790165, baseEnd_7790165] using wordTrace_append hprefix tailTrace_7790165
  have hstable : (prefixWord ++ tailWord_7790165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790165).length < 2 ^ (prefixWord ++ tailWord_7790165).sum := by decide
  have hdescent : baseEnd_7790165 < baseStart_7790165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790189 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_7790189 : Nat := 118140960795 + 7790189 * 2 ^ 59
def prefixEnd_7790189 : Nat := 4983230072969 + 3 ^ 40 * 7790189 * 2
def baseEnd_7790189 : Nat := 4000111346368326583411079

theorem tailTrace_7790189 : CollatzResearch.WordTrace tailWord_7790189 prefixEnd_7790189 4000111346368326583411079 := by
  unfold tailWord_7790189
  simp only [CollatzResearch.WordTrace]
  refine ⟨284131535174483186203109621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189421023449655457468739747 284131535174483186203109621)
  ·
    refine ⟨26637331422607798706541527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284131535174483186203109621 26637331422607798706541527)
    ·
      refine ⟨39955997133911698059812291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26637331422607798706541527 39955997133911698059812291)
      ·
        refine ⟨59933995700867547089718437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39955997133911698059812291 59933995700867547089718437)
        ·
          refine ⟨11237624193912665079322207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59933995700867547089718437 11237624193912665079322207)
          ·
            refine ⟨16856436290868997618983311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11237624193912665079322207 16856436290868997618983311)
            ·
              refine ⟨25284654436303496428474967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16856436290868997618983311 25284654436303496428474967)
              ·
                refine ⟨37926981654455244642712451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25284654436303496428474967 37926981654455244642712451)
                ·
                  refine ⟨56890472481682866964068677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37926981654455244642712451 56890472481682866964068677)
                  ·
                    refine ⟨10666963590315537555762877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56890472481682866964068677 10666963590315537555762877)
                    ·
                      refine ⟨4000111346368326583411079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10666963590315537555762877 4000111346368326583411079)
                      ·
                        rfl

theorem cell23_7790189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_7790189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790189 prefixEnd_7790189 := by exact prefixLift 7790189
  have htrace : WordTrace (prefixWord ++ tailWord_7790189) baseStart_7790189 baseEnd_7790189 := by
    simpa [prefixWord, tailWord_7790189, baseEnd_7790189] using wordTrace_append hprefix tailTrace_7790189
  have hstable : (prefixWord ++ tailWord_7790189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790189).length < 2 ^ (prefixWord ++ tailWord_7790189).sum := by decide
  have hdescent : baseEnd_7790189 < baseStart_7790189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790209 : List Nat := [1, 2, 4, 2, 1, 4, 1, 2, 6]
def baseStart_7790209 : Nat := 118140960795 + 7790209 * 2 ^ 59
def prefixEnd_7790209 : Nat := 4983230072969 + 3 ^ 40 * 7790209 * 2
def baseEnd_7790209 : Nat := 444457957331268500573443

theorem tailTrace_7790209 : CollatzResearch.WordTrace tailWord_7790209 prefixEnd_7790209 444457957331268500573443 := by
  unfold tailWord_7790209
  simp only [CollatzResearch.WordTrace]
  refine ⟨284132264634410729618837681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189421509756273819745891787 284132264634410729618837681)
  ·
    refine ⟨213099198475808047214128261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284132264634410729618837681 213099198475808047214128261)
    ·
      refine ⟨39956099714214008852649049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213099198475808047214128261 39956099714214008852649049)
      ·
        refine ⟨29967074785660506639486787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39956099714214008852649049 29967074785660506639486787)
        ·
          refine ⟨44950612178490759959230181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29967074785660506639486787 44950612178490759959230181)
          ·
            refine ⟨8428239783467017492355659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44950612178490759959230181 8428239783467017492355659)
            ·
              refine ⟨12642359675200526238533489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8428239783467017492355659 12642359675200526238533489)
              ·
                refine ⟨9481769756400394678900117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12642359675200526238533489 9481769756400394678900117)
                ·
                  refine ⟨444457957331268500573443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9481769756400394678900117 444457957331268500573443)
                  ·
                    rfl

theorem cell23_7790209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 6].length) (baseStart_7790209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790209 prefixEnd_7790209 := by exact prefixLift 7790209
  have htrace : WordTrace (prefixWord ++ tailWord_7790209) baseStart_7790209 baseEnd_7790209 := by
    simpa [prefixWord, tailWord_7790209, baseEnd_7790209] using wordTrace_append hprefix tailTrace_7790209
  have hstable : (prefixWord ++ tailWord_7790209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790209).length < 2 ^ (prefixWord ++ tailWord_7790209).sum := by decide
  have hdescent : baseEnd_7790209 < baseStart_7790209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790219 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 3, 1, 3]
def baseStart_7790219 : Nat := 118140960795 + 7790219 * 2 ^ 59
def prefixEnd_7790219 : Nat := 4983230072969 + 3 ^ 40 * 7790219 * 2
def baseEnd_7790219 : Nat := 4000126750787961466035941

theorem tailTrace_7790219 : CollatzResearch.WordTrace tailWord_7790219 prefixEnd_7790219 4000126750787961466035941 := by
  unfold tailWord_7790219
  simp only [CollatzResearch.WordTrace]
  refine ⟨284132629364374501326701711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189421752909583000884467807 284132629364374501326701711)
  ·
    refine ⟨426198944046561751990052567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284132629364374501326701711 426198944046561751990052567)
    ·
      refine ⟨639298416069842627985078851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426198944046561751990052567 639298416069842627985078851)
      ·
        refine ⟨958947624104763941977618277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639298416069842627985078851 958947624104763941977618277)
        ·
          refine ⟨179802679519643239120803427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 958947624104763941977618277 179802679519643239120803427)
          ·
            refine ⟨269704019279464858681205141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179802679519643239120803427 269704019279464858681205141)
            ·
              refine ⟨12642375903724915250681491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 269704019279464858681205141 12642375903724915250681491)
              ·
                refine ⟨18963563855587372876022237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12642375903724915250681491 18963563855587372876022237)
                ·
                  refine ⟨7111336445845264828508339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18963563855587372876022237 7111336445845264828508339)
                  ·
                    refine ⟨10667004668767897242762509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7111336445845264828508339 10667004668767897242762509)
                    ·
                      refine ⟨4000126750787961466035941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10667004668767897242762509 4000126750787961466035941)
                      ·
                        rfl

theorem cell23_7790219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 1, 3].length) (baseStart_7790219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790219 prefixEnd_7790219 := by exact prefixLift 7790219
  have htrace : WordTrace (prefixWord ++ tailWord_7790219) baseStart_7790219 baseEnd_7790219 := by
    simpa [prefixWord, tailWord_7790219, baseEnd_7790219] using wordTrace_append hprefix tailTrace_7790219
  have hstable : (prefixWord ++ tailWord_7790219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790219).length < 2 ^ (prefixWord ++ tailWord_7790219).sum := by decide
  have hdescent : baseEnd_7790219 < baseStart_7790219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790225 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_7790225 : Nat := 118140960795 + 7790225 * 2 ^ 59
def prefixEnd_7790225 : Nat := 4983230072969 + 3 ^ 40 * 7790225 * 2
def baseEnd_7790225 : Nat := 4000129831671888442560913

theorem tailTrace_7790225 : CollatzResearch.WordTrace tailWord_7790225 prefixEnd_7790225 4000129831671888442560913 := by
  unfold tailWord_7790225
  simp only [CollatzResearch.WordTrace]
  refine ⟨284132848202352764351420129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189421898801568509567613419 284132848202352764351420129)
  ·
    refine ⟨213099636151764573263565097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284132848202352764351420129 213099636151764573263565097)
    ·
      refine ⟨159824727113823429947673823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213099636151764573263565097 159824727113823429947673823)
      ·
        refine ⟨239737090670735144921510735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159824727113823429947673823 239737090670735144921510735)
        ·
          refine ⟨359605636006102717382266103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239737090670735144921510735 359605636006102717382266103)
          ·
            refine ⟨539408454009154076073399155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359605636006102717382266103 539408454009154076073399155)
            ·
              refine ⟨809112681013731114110098733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539408454009154076073399155 809112681013731114110098733)
              ·
                refine ⟨303417255380149167791287025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 809112681013731114110098733 303417255380149167791287025)
                ·
                  refine ⟨227562941535111875843465269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303417255380149167791287025 227562941535111875843465269)
                  ·
                    refine ⟨21334025768916738360324869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 227562941535111875843465269 21334025768916738360324869)
                    ·
                      refine ⟨4000129831671888442560913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21334025768916738360324869 4000129831671888442560913)
                      ·
                        rfl

theorem cell23_7790225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_7790225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790225 prefixEnd_7790225 := by exact prefixLift 7790225
  have htrace : WordTrace (prefixWord ++ tailWord_7790225) baseStart_7790225 baseEnd_7790225 := by
    simpa [prefixWord, tailWord_7790225, baseEnd_7790225] using wordTrace_append hprefix tailTrace_7790225
  have hstable : (prefixWord ++ tailWord_7790225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790225).length < 2 ^ (prefixWord ++ tailWord_7790225).sum := by decide
  have hdescent : baseEnd_7790225 < baseStart_7790225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790226 : List Nat := [3, 2, 3, 1, 3, 1, 3, 1, 6]
def baseStart_7790226 : Nat := 118140960795 + 7790226 * 2 ^ 59
def prefixEnd_7790226 : Nat := 4983230072969 + 3 ^ 40 * 7790226 * 2
def baseEnd_7790226 : Nat := 444458927239171437627601

theorem tailTrace_7790226 : CollatzResearch.WordTrace tailWord_7790226 prefixEnd_7790226 444458927239171437627601 := by
  unfold tailWord_7790226
  simp only [CollatzResearch.WordTrace]
  refine ⟨71033221168837285380551633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189421923116899427681471021 71033221168837285380551633)
  ·
    refine ⟨53274915876627964035413725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71033221168837285380551633 53274915876627964035413725)
    ·
      refine ⟨19978093453735486513280147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53274915876627964035413725 19978093453735486513280147)
      ·
        refine ⟨29967140180603229769920221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19978093453735486513280147 29967140180603229769920221)
        ·
          refine ⟨11237677567726211163720083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29967140180603229769920221 11237677567726211163720083)
          ·
            refine ⟨16856516351589316745580125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11237677567726211163720083 16856516351589316745580125)
            ·
              refine ⟨6321193631845993779592547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16856516351589316745580125 6321193631845993779592547)
              ·
                refine ⟨9481790447768990669388821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321193631845993779592547 9481790447768990669388821)
                ·
                  refine ⟨444458927239171437627601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9481790447768990669388821 444458927239171437627601)
                  ·
                    rfl

theorem cell23_7790226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_7790226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790226 prefixEnd_7790226 := by exact prefixLift 7790226
  have htrace : WordTrace (prefixWord ++ tailWord_7790226) baseStart_7790226 baseEnd_7790226 := by
    simpa [prefixWord, tailWord_7790226, baseEnd_7790226] using wordTrace_append hprefix tailTrace_7790226
  have hstable : (prefixWord ++ tailWord_7790226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790226).length < 2 ^ (prefixWord ++ tailWord_7790226).sum := by decide
  have hdescent : baseEnd_7790226 < baseStart_7790226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790265 : List Nat := [1, 2, 1, 4, 1, 1, 13]
def baseStart_7790265 : Nat := 118140960795 + 7790265 * 2 ^ 59
def prefixEnd_7790265 : Nat := 4983230072969 + 3 ^ 40 * 7790265 * 2
def baseEnd_7790265 : Nat := 49384572480223065260009

theorem tailTrace_7790265 : CollatzResearch.WordTrace tailWord_7790265 prefixEnd_7790265 49384572480223065260009 := by
  unfold tailWord_7790265
  simp only [CollatzResearch.WordTrace]
  refine ⟨284134307122207851182876249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189422871414805234121917499 284134307122207851182876249)
  ·
    refine ⟨213100730341655888387157187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284134307122207851182876249 213100730341655888387157187)
    ·
      refine ⟨319651095512483832580735781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213100730341655888387157187 319651095512483832580735781)
      ·
        refine ⟨59934580408590718608887959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319651095512483832580735781 59934580408590718608887959)
        ·
          refine ⟨89901870612886077913331939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59934580408590718608887959 89901870612886077913331939)
          ·
            refine ⟨134852805919329116869997909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89901870612886077913331939 134852805919329116869997909)
            ·
              refine ⟨49384572480223065260009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 134852805919329116869997909 49384572480223065260009)
              ·
                rfl

theorem cell23_7790265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 13].length) (baseStart_7790265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790265 prefixEnd_7790265 := by exact prefixLift 7790265
  have htrace : WordTrace (prefixWord ++ tailWord_7790265) baseStart_7790265 baseEnd_7790265 := by
    simpa [prefixWord, tailWord_7790265, baseEnd_7790265] using wordTrace_append hprefix tailTrace_7790265
  have hstable : (prefixWord ++ tailWord_7790265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790265).length < 2 ^ (prefixWord ++ tailWord_7790265).sum := by decide
  have hdescent : baseEnd_7790265 < baseStart_7790265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790269 : List Nat := [1, 4, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_7790269 : Nat := 118140960795 + 7790269 * 2 ^ 59
def prefixEnd_7790269 : Nat := 4983230072969 + 3 ^ 40 * 7790269 * 2
def baseEnd_7790269 : Nat := 1333384141606895423470237

theorem tailTrace_7790269 : CollatzResearch.WordTrace tailWord_7790269 prefixEnd_7790269 1333384141606895423470237 := by
  unfold tailWord_7790269
  simp only [CollatzResearch.WordTrace]
  refine ⟨284134453014193359866021861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189422968676128906577347907 284134453014193359866021861)
  ·
    refine ⟨53275209940161254974879099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284134453014193359866021861 53275209940161254974879099)
    ·
      refine ⟨79912814910241882462318649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53275209940161254974879099 79912814910241882462318649)
      ·
        refine ⟨59934611182681411846738987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79912814910241882462318649 59934611182681411846738987)
        ·
          refine ⟨89901916774022117770108481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59934611182681411846738987 89901916774022117770108481)
          ·
            refine ⟨67426437580516588327581361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89901916774022117770108481 67426437580516588327581361)
            ·
              refine ⟨50569828185387441245686021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67426437580516588327581361 50569828185387441245686021)
              ·
                refine ⟨9481842784760145233566129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50569828185387441245686021 9481842784760145233566129)
                ·
                  refine ⟨7111382088570108925174597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9481842784760145233566129 7111382088570108925174597)
                  ·
                    refine ⟨1333384141606895423470237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7111382088570108925174597 1333384141606895423470237)
                    ·
                      rfl

theorem cell23_7790269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_7790269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790269 prefixEnd_7790269 := by exact prefixLift 7790269
  have htrace : WordTrace (prefixWord ++ tailWord_7790269) baseStart_7790269 baseEnd_7790269 := by
    simpa [prefixWord, tailWord_7790269, baseEnd_7790269] using wordTrace_append hprefix tailTrace_7790269
  have hstable : (prefixWord ++ tailWord_7790269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790269).length < 2 ^ (prefixWord ++ tailWord_7790269).sum := by decide
  have hdescent : baseEnd_7790269 < baseStart_7790269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790270 : List Nat := [4, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3]
def baseStart_7790270 : Nat := 118140960795 + 7790270 * 2 ^ 59
def prefixEnd_7790270 : Nat := 4983230072969 + 3 ^ 40 * 7790270 * 2
def baseEnd_7790270 : Nat := 4000152938301340766498207

theorem tailTrace_7790270 : CollatzResearch.WordTrace tailWord_7790270 prefixEnd_7790270 4000152938301340766498207 := by
  unfold tailWord_7790270
  simp only [CollatzResearch.WordTrace]
  refine ⟨35516811185898717129601033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189422992991459824691205509 35516811185898717129601033)
  ·
    refine ⟨26637608389424037847200775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35516811185898717129601033 26637608389424037847200775)
    ·
      refine ⟨39956412584136056770801163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26637608389424037847200775 39956412584136056770801163)
      ·
        refine ⟨59934618876204085156201745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39956412584136056770801163 59934618876204085156201745)
        ·
          refine ⟨44950964157153063867151309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59934618876204085156201745 44950964157153063867151309)
          ·
            refine ⟨16856611558932398950181741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44950964157153063867151309 16856611558932398950181741)
            ·
              refine ⟨6321229334599649606318153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16856611558932398950181741 6321229334599649606318153)
              ·
                refine ⟨4740922000949737204738615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6321229334599649606318153 4740922000949737204738615)
                ·
                  refine ⟨7111383001424605807107923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4740922000949737204738615 7111383001424605807107923)
                  ·
                    refine ⟨10667074502136908710661885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7111383001424605807107923 10667074502136908710661885)
                    ·
                      refine ⟨4000152938301340766498207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10667074502136908710661885 4000152938301340766498207)
                      ·
                        rfl

theorem cell23_7790270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_7790270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790270 prefixEnd_7790270 := by exact prefixLift 7790270
  have htrace : WordTrace (prefixWord ++ tailWord_7790270) baseStart_7790270 baseEnd_7790270 := by
    simpa [prefixWord, tailWord_7790270, baseEnd_7790270] using wordTrace_append hprefix tailTrace_7790270
  have hstable : (prefixWord ++ tailWord_7790270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790270).length < 2 ^ (prefixWord ++ tailWord_7790270).sum := by decide
  have hdescent : baseEnd_7790270 < baseStart_7790270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790309 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 1, 3, 3]
def baseStart_7790309 : Nat := 118140960795 + 7790309 * 2 ^ 59
def prefixEnd_7790309 : Nat := 4983230072969 + 3 ^ 40 * 7790309 * 2
def baseEnd_7790309 : Nat := 4000172964046866113910527

theorem tailTrace_7790309 : CollatzResearch.WordTrace tailWord_7790309 prefixEnd_7790309 4000172964046866113910527 := by
  unfold tailWord_7790309
  simp only [CollatzResearch.WordTrace]
  refine ⟨284135911934048446697477981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189423941289365631131651987 284135911934048446697477981)
  ·
    refine ⟨106550966975268167511554243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284135911934048446697477981 106550966975268167511554243)
    ·
      refine ⟨159826450462902251267331365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106550966975268167511554243 159826450462902251267331365)
      ·
        refine ⟨29967459461794172112624631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159826450462902251267331365 29967459461794172112624631)
        ·
          refine ⟨44951189192691258168936947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29967459461794172112624631 44951189192691258168936947)
          ·
            refine ⟨67426783789036887253405421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44951189192691258168936947 67426783789036887253405421)
            ·
              refine ⟨25285043920888832720027033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67426783789036887253405421 25285043920888832720027033)
              ·
                refine ⟨18963782940666624540020275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25285043920888832720027033 18963782940666624540020275)
                ·
                  refine ⟨28445674410999936810030413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18963782940666624540020275 28445674410999936810030413)
                  ·
                    refine ⟨10667127904124976303761405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28445674410999936810030413 10667127904124976303761405)
                    ·
                      refine ⟨4000172964046866113910527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10667127904124976303761405 4000172964046866113910527)
                      ·
                        rfl

theorem cell23_7790309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_7790309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790309 prefixEnd_7790309 := by exact prefixLift 7790309
  have htrace : WordTrace (prefixWord ++ tailWord_7790309) baseStart_7790309 baseEnd_7790309 := by
    simpa [prefixWord, tailWord_7790309, baseEnd_7790309] using wordTrace_append hprefix tailTrace_7790309
  have hstable : (prefixWord ++ tailWord_7790309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790309).length < 2 ^ (prefixWord ++ tailWord_7790309).sum := by decide
  have hdescent : baseEnd_7790309 < baseStart_7790309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790332 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_7790332 : Nat := 118140960795 + 7790332 * 2 ^ 59
def prefixEnd_7790332 : Nat := 4983230072969 + 3 ^ 40 * 7790332 * 2
def baseEnd_7790332 : Nat := 4000184774101919523922921

theorem tailTrace_7790332 : CollatzResearch.WordTrace tailWord_7790332 prefixEnd_7790332 4000184774101919523922921 := by
  unfold tailWord_7790332
  simp only [CollatzResearch.WordTrace]
  refine ⟨142068375406482560812782625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189424500541976747750376833 142068375406482560812782625)
  ·
    refine ⟨106551281554861920609586969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142068375406482560812782625 106551281554861920609586969)
    ·
      refine ⟨79913461166146440457190227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106551281554861920609586969 79913461166146440457190227)
      ·
        refine ⟨119870191749219660685785341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79913461166146440457190227 119870191749219660685785341)
        ·
          refine ⟨44951321905957372757169503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119870191749219660685785341 44951321905957372757169503)
          ·
            refine ⟨67426982858936059135754255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44951321905957372757169503 67426982858936059135754255)
            ·
              refine ⟨101140474288404088703631383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67426982858936059135754255 101140474288404088703631383)
              ·
                refine ⟨151710711432606133055447075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101140474288404088703631383 151710711432606133055447075)
                ·
                  refine ⟨227566067148909199583170613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151710711432606133055447075 227566067148909199583170613)
                  ·
                    refine ⟨21334318795210237460922245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 227566067148909199583170613 21334318795210237460922245)
                    ·
                      refine ⟨4000184774101919523922921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21334318795210237460922245 4000184774101919523922921)
                      ·
                        rfl

theorem cell23_7790332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_7790332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790332 prefixEnd_7790332 := by exact prefixLift 7790332
  have htrace : WordTrace (prefixWord ++ tailWord_7790332) baseStart_7790332 baseEnd_7790332 := by
    simpa [prefixWord, tailWord_7790332, baseEnd_7790332] using wordTrace_append hprefix tailTrace_7790332
  have hstable : (prefixWord ++ tailWord_7790332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790332).length < 2 ^ (prefixWord ++ tailWord_7790332).sum := by decide
  have hdescent : baseEnd_7790332 < baseStart_7790332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790423 : List Nat := [1, 1, 3, 2, 5, 2, 1, 3, 5]
def baseStart_7790423 : Nat := 118140960795 + 7790423 * 2 ^ 59
def prefixEnd_7790423 : Nat := 4983230072969 + 3 ^ 40 * 7790423 * 2
def baseEnd_7790423 : Nat := 444470166760164296431667

theorem tailTrace_7790423 : CollatzResearch.WordTrace tailWord_7790423 prefixEnd_7790423 444470166760164296431667 := by
  unfold tailWord_7790423
  simp only [CollatzResearch.WordTrace]
  refine ⟨284140069855635444167127923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189426713237090296111418615 284140069855635444167127923)
  ·
    refine ⟨426210104783453166250691885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284140069855635444167127923 426210104783453166250691885)
    ·
      refine ⟨159828789293794937344009457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426210104783453166250691885 159828789293794937344009457)
      ·
        refine ⟨119871591970346203008007093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159828789293794937344009457 119871591970346203008007093)
        ·
          refine ⟨11237961747219956532000665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119871591970346203008007093 11237961747219956532000665)
          ·
            refine ⟨8428471310414967399000499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11237961747219956532000665 8428471310414967399000499)
            ·
              refine ⟨12642706965622451098500749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8428471310414967399000499 12642706965622451098500749)
              ·
                refine ⟨4741015112108419161937781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12642706965622451098500749 4741015112108419161937781)
                ·
                  refine ⟨444470166760164296431667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4741015112108419161937781 444470166760164296431667)
                  ·
                    rfl

theorem cell23_7790423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 5].length) (baseStart_7790423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790423 prefixEnd_7790423 := by exact prefixLift 7790423
  have htrace : WordTrace (prefixWord ++ tailWord_7790423) baseStart_7790423 baseEnd_7790423 := by
    simpa [prefixWord, tailWord_7790423, baseEnd_7790423] using wordTrace_append hprefix tailTrace_7790423
  have hstable : (prefixWord ++ tailWord_7790423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790423).length < 2 ^ (prefixWord ++ tailWord_7790423).sum := by decide
  have hdescent : baseEnd_7790423 < baseStart_7790423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790436 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_7790436 : Nat := 118140960795 + 7790436 * 2 ^ 59
def prefixEnd_7790436 : Nat := 4983230072969 + 3 ^ 40 * 7790436 * 2
def baseEnd_7790436 : Nat := 1333412725363329039007481

theorem tailTrace_7790436 : CollatzResearch.WordTrace tailWord_7790436 prefixEnd_7790436 1333412725363329039007481 := by
  unfold tailWord_7790436
  simp only [CollatzResearch.WordTrace]
  refine ⟨142070272002294173693675581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189427029336392231591567441 142070272002294173693675581)
  ·
    refine ⟨53276352000860315135128343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142070272002294173693675581 53276352000860315135128343)
    ·
      refine ⟨79914528001290472702692515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53276352000860315135128343 79914528001290472702692515)
      ·
        refine ⟨119871792001935709054038773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79914528001290472702692515 119871792001935709054038773)
        ·
          refine ⟨11237980500181472723816135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119871792001935709054038773 11237980500181472723816135)
          ·
            refine ⟨16856970750272209085724203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11237980500181472723816135 16856970750272209085724203)
            ·
              refine ⟨25285456125408313628586305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16856970750272209085724203 25285456125408313628586305)
              ·
                refine ⟨18964092094056235221439729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25285456125408313628586305 18964092094056235221439729)
                ·
                  refine ⟨14223069070542176416079797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18964092094056235221439729 14223069070542176416079797)
                  ·
                    refine ⟨1333412725363329039007481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14223069070542176416079797 1333412725363329039007481)
                    ·
                      rfl

theorem cell23_7790436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_7790436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790436 prefixEnd_7790436 := by exact prefixLift 7790436
  have htrace : WordTrace (prefixWord ++ tailWord_7790436) baseStart_7790436 baseEnd_7790436 := by
    simpa [prefixWord, tailWord_7790436, baseEnd_7790436] using wordTrace_append hprefix tailTrace_7790436
  have hstable : (prefixWord ++ tailWord_7790436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790436).length < 2 ^ (prefixWord ++ tailWord_7790436).sum := by decide
  have hdescent : baseEnd_7790436 < baseStart_7790436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790446 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_7790446 : Nat := 118140960795 + 7790446 * 2 ^ 59
def prefixEnd_7790446 : Nat := 4983230072969 + 3 ^ 40 * 7790446 * 2
def baseEnd_7790446 : Nat := 4000243310896532077897397

theorem tailTrace_7790446 : CollatzResearch.WordTrace tailWord_7790446 prefixEnd_7790446 4000243310896532077897397 := by
  unfold tailWord_7790446
  simp only [CollatzResearch.WordTrace]
  refine ⟨35517613591819014886901899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189427272489701412730143461 35517613591819014886901899)
  ·
    refine ⟨53276420387728522330352849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35517613591819014886901899 53276420387728522330352849)
    ·
      refine ⟨39957315290796391747764637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53276420387728522330352849 39957315290796391747764637)
      ·
        refine ⟨14983993234048646905411739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39957315290796391747764637 14983993234048646905411739)
        ·
          refine ⟨22475989851072970358117609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14983993234048646905411739 22475989851072970358117609)
          ·
            refine ⟨16856992388304727768588207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22475989851072970358117609 16856992388304727768588207)
            ·
              refine ⟨25285488582457091652882311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16856992388304727768588207 25285488582457091652882311)
              ·
                refine ⟨37928232873685637479323467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25285488582457091652882311 37928232873685637479323467)
                ·
                  refine ⟨56892349310528456218985201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37928232873685637479323467 56892349310528456218985201)
                  ·
                    refine ⟨42669261982896342164238901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56892349310528456218985201 42669261982896342164238901)
                    ·
                      refine ⟨4000243310896532077897397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42669261982896342164238901 4000243310896532077897397)
                      ·
                        rfl

theorem cell23_7790446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_7790446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790446 prefixEnd_7790446 := by exact prefixLift 7790446
  have htrace : WordTrace (prefixWord ++ tailWord_7790446) baseStart_7790446 baseEnd_7790446 := by
    simpa [prefixWord, tailWord_7790446, baseEnd_7790446] using wordTrace_append hprefix tailTrace_7790446
  have hstable : (prefixWord ++ tailWord_7790446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790446).length < 2 ^ (prefixWord ++ tailWord_7790446).sum := by decide
  have hdescent : baseEnd_7790446 < baseStart_7790446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790459 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 3]
def baseStart_7790459 : Nat := 118140960795 + 7790459 * 2 ^ 59
def prefixEnd_7790459 : Nat := 4983230072969 + 3 ^ 40 * 7790459 * 2
def baseEnd_7790459 : Nat := 4000249986145040527034837

theorem tailTrace_7790459 : CollatzResearch.WordTrace tailWord_7790459 prefixEnd_7790459 4000249986145040527034837 := by
  unfold tailWord_7790459
  simp only [CollatzResearch.WordTrace]
  refine ⟨284141382883505022315438431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189427588589003348210292287 284141382883505022315438431)
  ·
    refine ⟨426212074325257533473157647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284141382883505022315438431 426212074325257533473157647)
    ·
      refine ⟨639318111487886300209736471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426212074325257533473157647 639318111487886300209736471)
      ·
        refine ⟨958977167231829450314604707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639318111487886300209736471 958977167231829450314604707)
        ·
          refine ⟨1438465750847744175471907061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958977167231829450314604707 1438465750847744175471907061)
          ·
            refine ⟨134856164141976016450491287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1438465750847744175471907061 134856164141976016450491287)
            ·
              refine ⟨202284246212964024675736931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134856164141976016450491287 202284246212964024675736931)
              ·
                refine ⟨303426369319446037013605397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202284246212964024675736931 303426369319446037013605397)
                ·
                  refine ⟨14223111061849032985012753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 303426369319446037013605397 14223111061849032985012753)
                  ·
                    refine ⟨10667333296386774738759565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14223111061849032985012753 10667333296386774738759565)
                    ·
                      refine ⟨4000249986145040527034837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10667333296386774738759565 4000249986145040527034837)
                      ·
                        rfl

theorem cell23_7790459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 3].length) (baseStart_7790459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790459 prefixEnd_7790459 := by exact prefixLift 7790459
  have htrace : WordTrace (prefixWord ++ tailWord_7790459) baseStart_7790459 baseEnd_7790459 := by
    simpa [prefixWord, tailWord_7790459, baseEnd_7790459] using wordTrace_append hprefix tailTrace_7790459
  have hstable : (prefixWord ++ tailWord_7790459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790459).length < 2 ^ (prefixWord ++ tailWord_7790459).sum := by decide
  have hdescent : baseEnd_7790459 < baseStart_7790459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790500 : List Nat := [2, 3, 1, 2, 1, 3, 4, 2, 1, 4]
def baseStart_7790500 : Nat := 118140960795 + 7790500 * 2 ^ 59
def prefixEnd_7790500 : Nat := 4983230072969 + 3 ^ 40 * 7790500 * 2
def baseEnd_7790500 : Nat := 1333423679617291622207383

theorem tailTrace_7790500 : CollatzResearch.WordTrace tailWord_7790500 prefixEnd_7790500 1333423679617291622207383 := by
  unfold tailWord_7790500
  simp only [CollatzResearch.WordTrace]
  refine ⟨142071439138178243158840477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189428585517570990878453969 142071439138178243158840477)
  ·
    refine ⟨53276789676816841184565179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142071439138178243158840477 53276789676816841184565179)
    ·
      refine ⟨79915184515225261776847769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53276789676816841184565179 79915184515225261776847769)
      ·
        refine ⟨59936388386418946332635827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79915184515225261776847769 59936388386418946332635827)
        ·
          refine ⟨89904582579628419498953741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59936388386418946332635827 89904582579628419498953741)
          ·
            refine ⟨33714218467360657312107653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89904582579628419498953741 33714218467360657312107653)
            ·
              refine ⟨6321415962630123246020185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33714218467360657312107653 6321415962630123246020185)
              ·
                refine ⟨4741061971972592434515139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6321415962630123246020185 4741061971972592434515139)
                ·
                  refine ⟨7111592957958888651772709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741061971972592434515139 7111592957958888651772709)
                  ·
                    refine ⟨1333423679617291622207383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7111592957958888651772709 1333423679617291622207383)
                    ·
                      rfl

theorem cell23_7790500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_7790500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790500 prefixEnd_7790500 := by exact prefixLift 7790500
  have htrace : WordTrace (prefixWord ++ tailWord_7790500) baseStart_7790500 baseEnd_7790500 := by
    simpa [prefixWord, tailWord_7790500, baseEnd_7790500] using wordTrace_append hprefix tailTrace_7790500
  have hstable : (prefixWord ++ tailWord_7790500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790500).length < 2 ^ (prefixWord ++ tailWord_7790500).sum := by decide
  have hdescent : baseEnd_7790500 < baseStart_7790500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790526 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_7790526 : Nat := 118140960795 + 7790526 * 2 ^ 59
def prefixEnd_7790526 : Nat := 4983230072969 + 3 ^ 40 * 7790526 * 2
def baseEnd_7790526 : Nat := 1333428129782963921632343

theorem tailTrace_7790526 : CollatzResearch.WordTrace tailWord_7790526 prefixEnd_7790526 1333428129782963921632343 := by
  unfold tailWord_7790526
  simp only [CollatzResearch.WordTrace]
  refine ⟨35517978321782786594765929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189429217716174861838751621 35517978321782786594765929)
  ·
    refine ⟨26638483741337089946074447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35517978321782786594765929 26638483741337089946074447)
    ·
      refine ⟨39957725612005634919111671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26638483741337089946074447 39957725612005634919111671)
      ·
        refine ⟨59936588418008452378667507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39957725612005634919111671 59936588418008452378667507)
        ·
          refine ⟨89904882627012678568001261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59936588418008452378667507 89904882627012678568001261)
          ·
            refine ⟨33714330985129754463000473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89904882627012678568001261 33714330985129754463000473)
            ·
              refine ⟨25285748238847315847250355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33714330985129754463000473 25285748238847315847250355)
              ·
                refine ⟨37928622358270973770875533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25285748238847315847250355 37928622358270973770875533)
                ·
                  refine ⟨14223233384351615164078325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37928622358270973770875533 14223233384351615164078325)
                  ·
                    refine ⟨1333428129782963921632343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14223233384351615164078325 1333428129782963921632343)
                    ·
                      rfl

theorem cell23_7790526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_7790526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790526 prefixEnd_7790526 := by exact prefixLift 7790526
  have htrace : WordTrace (prefixWord ++ tailWord_7790526) baseStart_7790526 baseEnd_7790526 := by
    simpa [prefixWord, tailWord_7790526, baseEnd_7790526] using wordTrace_append hprefix tailTrace_7790526
  have hstable : (prefixWord ++ tailWord_7790526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790526).length < 2 ^ (prefixWord ++ tailWord_7790526).sum := by decide
  have hdescent : baseEnd_7790526 < baseStart_7790526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790539 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 1, 6]
def baseStart_7790539 : Nat := 118140960795 + 7790539 * 2 ^ 59
def prefixEnd_7790539 : Nat := 4983230072969 + 3 ^ 40 * 7790539 * 2
def baseEnd_7790539 : Nat := 1333430354865800071344823

theorem tailTrace_7790539 : CollatzResearch.WordTrace tailWord_7790539 prefixEnd_7790539 1333430354865800071344823 := by
  unfold tailWord_7790539
  simp only [CollatzResearch.WordTrace]
  refine ⟨284144300723215195978350671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189429533815476797318900447 284144300723215195978350671)
  ·
    refine ⟨426216451084822793967526007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284144300723215195978350671 426216451084822793967526007)
    ·
      refine ⟨639324676627234190951289011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426216451084822793967526007 639324676627234190951289011)
      ·
        refine ⟨958987014940851286426933517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639324676627234190951289011 958987014940851286426933517)
        ·
          refine ⟨359620130602819232410100069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 958987014940851286426933517 359620130602819232410100069)
          ·
            refine ⟨67428774488028606076893763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 359620130602819232410100069 67428774488028606076893763)
            ·
              refine ⟨101143161732042909115340645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67428774488028606076893763 101143161732042909115340645)
              ·
                refine ⟨18964342824758045459126371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101143161732042909115340645 18964342824758045459126371)
                ·
                  refine ⟨28446514237137068188689557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18964342824758045459126371 28446514237137068188689557)
                  ·
                    refine ⟨1333430354865800071344823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28446514237137068188689557 1333430354865800071344823)
                    ·
                      rfl

theorem cell23_7790539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 6].length) (baseStart_7790539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790539 prefixEnd_7790539 := by exact prefixLift 7790539
  have htrace : WordTrace (prefixWord ++ tailWord_7790539) baseStart_7790539 baseEnd_7790539 := by
    simpa [prefixWord, tailWord_7790539, baseEnd_7790539] using wordTrace_append hprefix tailTrace_7790539
  have hstable : (prefixWord ++ tailWord_7790539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790539).length < 2 ^ (prefixWord ++ tailWord_7790539).sum := by decide
  have hdescent : baseEnd_7790539 < baseStart_7790539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790540 : List Nat := [2, 2, 1, 4, 1, 2, 1, 5, 1, 1, 3]
def baseStart_7790540 : Nat := 118140960795 + 7790540 * 2 ^ 59
def prefixEnd_7790540 : Nat := 4983230072969 + 3 ^ 40 * 7790540 * 2
def baseEnd_7790540 : Nat := 4000291578078054710121965

theorem tailTrace_7790540 : CollatzResearch.WordTrace tailWord_7790540 prefixEnd_7790540 4000291578078054710121965 := by
  unfold tailWord_7790540
  simp only [CollatzResearch.WordTrace]
  refine ⟨142072168598105786574568537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189429558130807715432758049 142072168598105786574568537)
  ·
    refine ⟨106554126448579339930926403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142072168598105786574568537 106554126448579339930926403)
    ·
      refine ⟨159831189672869009896389605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106554126448579339930926403 159831189672869009896389605)
      ·
        refine ⟨29968348063662939355573051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159831189672869009896389605 29968348063662939355573051)
        ·
          refine ⟨44952522095494409033359577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29968348063662939355573051 44952522095494409033359577)
          ·
            refine ⟨33714391571620806775019683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44952522095494409033359577 33714391571620806775019683)
            ·
              refine ⟨50571587357431210162529525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33714391571620806775019683 50571587357431210162529525)
              ·
                refine ⟨4741086314759175952737143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50571587357431210162529525 4741086314759175952737143)
                ·
                  refine ⟨7111629472138763929105715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741086314759175952737143 7111629472138763929105715)
                  ·
                    refine ⟨10667444208208145893658573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7111629472138763929105715 10667444208208145893658573)
                    ·
                      refine ⟨4000291578078054710121965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10667444208208145893658573 4000291578078054710121965)
                      ·
                        rfl

theorem cell23_7790540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_7790540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790540 prefixEnd_7790540 := by exact prefixLift 7790540
  have htrace : WordTrace (prefixWord ++ tailWord_7790540) baseStart_7790540 baseEnd_7790540 := by
    simpa [prefixWord, tailWord_7790540, baseEnd_7790540] using wordTrace_append hprefix tailTrace_7790540
  have hstable : (prefixWord ++ tailWord_7790540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790540).length < 2 ^ (prefixWord ++ tailWord_7790540).sum := by decide
  have hdescent : baseEnd_7790540 < baseStart_7790540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790576 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 4]
def baseStart_7790576 : Nat := 118140960795 + 7790576 * 2 ^ 59
def prefixEnd_7790576 : Nat := 4983230072969 + 3 ^ 40 * 7790576 * 2
def baseEnd_7790576 : Nat := 4000310063381616569271799

theorem tailTrace_7790576 : CollatzResearch.WordTrace tailWord_7790576 prefixEnd_7790576 4000310063381616569271799 := by
  unfold tailWord_7790576
  simp only [CollatzResearch.WordTrace]
  refine ⟨142072825112040575648723791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189430433482720767531631721 142072825112040575648723791)
  ·
    refine ⟨213109237668060863473085687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142072825112040575648723791 213109237668060863473085687)
    ·
      refine ⟨319663856502091295209628531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213109237668060863473085687 319663856502091295209628531)
      ·
        refine ⟨479495784753136942814442797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319663856502091295209628531 479495784753136942814442797)
        ·
          refine ⟨179810919282426353555416049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479495784753136942814442797 179810919282426353555416049)
          ·
            refine ⟨134858189461819765166562037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179810919282426353555416049 134858189461819765166562037)
            ·
              refine ⟨12642955262045602984365191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134858189461819765166562037 12642955262045602984365191)
              ·
                refine ⟨18964432893068404476547787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12642955262045602984365191 18964432893068404476547787)
                ·
                  refine ⟨28446649339602606714821681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18964432893068404476547787 28446649339602606714821681)
                  ·
                    refine ⟨21334987004701955036116261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28446649339602606714821681 21334987004701955036116261)
                    ·
                      refine ⟨4000310063381616569271799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21334987004701955036116261 4000310063381616569271799)
                      ·
                        rfl

theorem cell23_7790576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 4].length) (baseStart_7790576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790576 prefixEnd_7790576 := by exact prefixLift 7790576
  have htrace : WordTrace (prefixWord ++ tailWord_7790576) baseStart_7790576 baseEnd_7790576 := by
    simpa [prefixWord, tailWord_7790576, baseEnd_7790576] using wordTrace_append hprefix tailTrace_7790576
  have hstable : (prefixWord ++ tailWord_7790576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790576).length < 2 ^ (prefixWord ++ tailWord_7790576).sum := by decide
  have hdescent : baseEnd_7790576 < baseStart_7790576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790597 : List Nat := [1, 3, 1, 1, 2, 4, 3, 3, 1, 2, 2]
def baseStart_7790597 : Nat := 118140960795 + 7790597 * 2 ^ 59
def prefixEnd_7790597 : Nat := 4983230072969 + 3 ^ 40 * 7790597 * 2
def baseEnd_7790597 : Nat := 4000320846475360987109203

theorem tailTrace_7790597 : CollatzResearch.WordTrace tailWord_7790597 prefixEnd_7790597 4000320846475360987109203 := by
  unfold tailWord_7790597
  simp only [CollatzResearch.WordTrace]
  refine ⟨284146416157005071883962045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189430944104670047922641363 284146416157005071883962045)
  ·
    refine ⟨106554906058876901956485767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284146416157005071883962045 106554906058876901956485767)
    ·
      refine ⟨159832359088315352934728651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106554906058876901956485767 159832359088315352934728651)
      ·
        refine ⟨239748538632473029402092977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159832359088315352934728651 239748538632473029402092977)
        ·
          refine ⟨179811403974354772051569733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239748538632473029402092977 179811403974354772051569733)
          ·
            refine ⟨33714638245191519759669325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179811403974354772051569733 33714638245191519759669325)
            ·
              refine ⟨12642989341946819909875997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33714638245191519759669325 12642989341946819909875997)
              ·
                refine ⟨4741121003230057466203499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12642989341946819909875997 4741121003230057466203499)
                ·
                  refine ⟨7111681504845086199305249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741121003230057466203499 7111681504845086199305249)
                  ·
                    refine ⟨5333761128633814649478937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7111681504845086199305249 5333761128633814649478937)
                    ·
                      refine ⟨4000320846475360987109203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5333761128633814649478937 4000320846475360987109203)
                      ·
                        rfl

theorem cell23_7790597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 1, 2, 2].length) (baseStart_7790597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790597 prefixEnd_7790597 := by exact prefixLift 7790597
  have htrace : WordTrace (prefixWord ++ tailWord_7790597) baseStart_7790597 baseEnd_7790597 := by
    simpa [prefixWord, tailWord_7790597, baseEnd_7790597] using wordTrace_append hprefix tailTrace_7790597
  have hstable : (prefixWord ++ tailWord_7790597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790597).length < 2 ^ (prefixWord ++ tailWord_7790597).sum := by decide
  have hdescent : baseEnd_7790597 < baseStart_7790597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790623 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 3, 3, 2]
def baseStart_7790623 : Nat := 118140960795 + 7790623 * 2 ^ 59
def prefixEnd_7790623 : Nat := 4983230072969 + 3 ^ 40 * 7790623 * 2
def baseEnd_7790623 : Nat := 4000334196972377885384083

theorem tailTrace_7790623 : CollatzResearch.WordTrace tailWord_7790623 prefixEnd_7790623 4000334196972377885384083 := by
  unfold tailWord_7790623
  simp only [CollatzResearch.WordTrace]
  refine ⟨284147364454910878324408523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189431576303273918882939015 284147364454910878324408523)
  ·
    refine ⟨426221046682366317486612785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284147364454910878324408523 426221046682366317486612785)
    ·
      refine ⟨319665785011774738114959589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426221046682366317486612785 319665785011774738114959589)
      ·
        refine ⟨59937334689707763396554923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319665785011774738114959589 59937334689707763396554923)
        ·
          refine ⟨89906002034561645094832385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59937334689707763396554923 89906002034561645094832385)
          ·
            refine ⟨67429501525921233821124289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89906002034561645094832385 67429501525921233821124289)
            ·
              refine ⟨50572126144440925365843217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67429501525921233821124289 50572126144440925365843217)
              ·
                refine ⟨37929094608330694024382413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50572126144440925365843217 37929094608330694024382413)
                ·
                  refine ⟨14223410478124010259143405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37929094608330694024382413 14223410478124010259143405)
                  ·
                    refine ⟨5333778929296503847178777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14223410478124010259143405 5333778929296503847178777)
                    ·
                      refine ⟨4000334196972377885384083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5333778929296503847178777 4000334196972377885384083)
                      ·
                        rfl

theorem cell23_7790623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_7790623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790623 prefixEnd_7790623 := by exact prefixLift 7790623
  have htrace : WordTrace (prefixWord ++ tailWord_7790623) baseStart_7790623 baseEnd_7790623 := by
    simpa [prefixWord, tailWord_7790623, baseEnd_7790623] using wordTrace_append hprefix tailTrace_7790623
  have hstable : (prefixWord ++ tailWord_7790623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790623).length < 2 ^ (prefixWord ++ tailWord_7790623).sum := by decide
  have hdescent : baseEnd_7790623 < baseStart_7790623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790640 : List Nat := [2, 1, 1, 1, 2, 5, 3, 2, 1, 3, 2]
def baseStart_7790640 : Nat := 118140960795 + 7790640 * 2 ^ 59
def prefixEnd_7790640 : Nat := 4983230072969 + 3 ^ 40 * 7790640 * 2
def baseEnd_7790640 : Nat := 4000342926143504318871505

theorem tailTrace_7790640 : CollatzResearch.WordTrace tailWord_7790640 prefixEnd_7790640 4000342926143504318871505 := by
  unfold tailWord_7790640
  simp only [CollatzResearch.WordTrace]
  refine ⟨142073992247924645113888687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189431989663899526818518249 142073992247924645113888687)
  ·
    refine ⟨213110988371886967670833031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142073992247924645113888687 213110988371886967670833031)
    ·
      refine ⟨319666482557830451506249547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213110988371886967670833031 319666482557830451506249547)
      ·
        refine ⟨479499723836745677259374321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319666482557830451506249547 479499723836745677259374321)
        ·
          refine ⟨359624792877559257944530741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479499723836745677259374321 359624792877559257944530741)
          ·
            refine ⟨33714824332271180432299757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 359624792877559257944530741 33714824332271180432299757)
            ·
              refine ⟨12643059124601692662112409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33714824332271180432299757 12643059124601692662112409)
              ·
                refine ⟨9482294343451269496584307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12643059124601692662112409 9482294343451269496584307)
                ·
                  refine ⟨14223441515176904244876461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9482294343451269496584307 14223441515176904244876461)
                  ·
                    refine ⟨5333790568191339091828673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14223441515176904244876461 5333790568191339091828673)
                    ·
                      refine ⟨4000342926143504318871505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5333790568191339091828673 4000342926143504318871505)
                      ·
                        rfl

theorem cell23_7790640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 1, 3, 2].length) (baseStart_7790640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790640 prefixEnd_7790640 := by exact prefixLift 7790640
  have htrace : WordTrace (prefixWord ++ tailWord_7790640) baseStart_7790640 baseEnd_7790640 := by
    simpa [prefixWord, tailWord_7790640, baseEnd_7790640] using wordTrace_append hprefix tailTrace_7790640
  have hstable : (prefixWord ++ tailWord_7790640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790640).length < 2 ^ (prefixWord ++ tailWord_7790640).sum := by decide
  have hdescent : baseEnd_7790640 < baseStart_7790640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790656 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 5]
def baseStart_7790656 : Nat := 118140960795 + 7790656 * 2 ^ 59
def prefixEnd_7790656 : Nat := 4983230072969 + 3 ^ 40 * 7790656 * 2
def baseEnd_7790656 : Nat := 4000351141833976256271431

theorem tailTrace_7790656 : CollatzResearch.WordTrace tailWord_7790656 prefixEnd_7790656 4000351141833976256271431 := by
  unfold tailWord_7790656
  simp only [CollatzResearch.WordTrace]
  refine ⟨142074284031895662480179911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189432378709194216640239881 142074284031895662480179911)
  ·
    refine ⟨213111426047843493720269867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142074284031895662480179911 213111426047843493720269867)
    ·
      refine ⟨319667139071765240580404801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213111426047843493720269867 319667139071765240580404801)
      ·
        refine ⟨239750354303823930435303601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319667139071765240580404801 239750354303823930435303601)
        ·
          refine ⟨179812765727867947826477701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239750354303823930435303601 179812765727867947826477701)
          ·
            refine ⟨33714893573975240217464569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179812765727867947826477701 33714893573975240217464569)
            ·
              refine ⟨25286170180481430163098427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33714893573975240217464569 25286170180481430163098427)
              ·
                refine ⟨37929255270722145244647641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25286170180481430163098427 37929255270722145244647641)
                ·
                  refine ⟨28446941453041608933485731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37929255270722145244647641 28446941453041608933485731)
                  ·
                    refine ⟨42670412179562413400228597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28446941453041608933485731 42670412179562413400228597)
                    ·
                      refine ⟨4000351141833976256271431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42670412179562413400228597 4000351141833976256271431)
                      ·
                        rfl

theorem cell23_7790656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_7790656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790656 prefixEnd_7790656 := by exact prefixLift 7790656
  have htrace : WordTrace (prefixWord ++ tailWord_7790656) baseStart_7790656 baseEnd_7790656 := by
    simpa [prefixWord, tailWord_7790656, baseEnd_7790656] using wordTrace_append hprefix tailTrace_7790656
  have hstable : (prefixWord ++ tailWord_7790656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790656).length < 2 ^ (prefixWord ++ tailWord_7790656).sum := by decide
  have hdescent : baseEnd_7790656 < baseStart_7790656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790659 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 11]
def baseStart_7790659 : Nat := 118140960795 + 7790659 * 2 ^ 59
def prefixEnd_7790659 : Nat := 4983230072969 + 3 ^ 40 * 7790659 * 2
def baseEnd_7790659 : Nat := 444483631363993304948213

theorem tailTrace_7790659 : CollatzResearch.WordTrace tailWord_7790659 prefixEnd_7790659 444483631363993304948213 := by
  unfold tailWord_7790659
  simp only [CollatzResearch.WordTrace]
  refine ⟨284148677482780456472719031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189432451655186970981812687 284148677482780456472719031)
  ·
    refine ⟨426223016224170684709078547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284148677482780456472719031 426223016224170684709078547)
    ·
      refine ⟨639334524336256027063617821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426223016224170684709078547 639334524336256027063617821)
      ·
        refine ⟨239750446626096010148856683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639334524336256027063617821 239750446626096010148856683)
        ·
          refine ⟨359625669939144015223285025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239750446626096010148856683 359625669939144015223285025)
          ·
            refine ⟨269719252454358011417463769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359625669939144015223285025 269719252454358011417463769)
            ·
              refine ⟨202289439340768508563097827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269719252454358011417463769 202289439340768508563097827)
              ·
                refine ⟨303434159011152762844646741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202289439340768508563097827 303434159011152762844646741)
                ·
                  refine ⟨444483631363993304948213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 303434159011152762844646741 444483631363993304948213)
                  ·
                    rfl

theorem cell23_7790659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 11].length) (baseStart_7790659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790659 prefixEnd_7790659 := by exact prefixLift 7790659
  have htrace : WordTrace (prefixWord ++ tailWord_7790659) baseStart_7790659 baseEnd_7790659 := by
    simpa [prefixWord, tailWord_7790659, baseEnd_7790659] using wordTrace_append hprefix tailTrace_7790659
  have hstable : (prefixWord ++ tailWord_7790659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790659).length < 2 ^ (prefixWord ++ tailWord_7790659).sum := by decide
  have hdescent : baseEnd_7790659 < baseStart_7790659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790666 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_7790666 : Nat := 118140960795 + 7790666 * 2 ^ 59
def prefixEnd_7790666 : Nat := 4983230072969 + 3 ^ 40 * 7790666 * 2
def baseEnd_7790666 : Nat := 4000356276640521217146385

theorem tailTrace_7790666 : CollatzResearch.WordTrace tailWord_7790666 prefixEnd_7790666 4000356276640521217146385 := by
  unfold tailWord_7790666
  simp only [CollatzResearch.WordTrace]
  refine ⟨71037233198438774167055963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189432621862503397778815901 71037233198438774167055963)
  ·
    refine ⟨106555849797658161250583945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71037233198438774167055963 106555849797658161250583945)
    ·
      refine ⟨79916887348243620937937959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106555849797658161250583945 79916887348243620937937959)
      ·
        refine ⟨119875331022365431406906939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79916887348243620937937959 119875331022365431406906939)
        ·
          refine ⟨179812996533548147110360409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119875331022365431406906939 179812996533548147110360409)
          ·
            refine ⟨134859747400161110332770307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179812996533548147110360409 134859747400161110332770307)
            ·
              refine ⟨202289621100241665499155461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134859747400161110332770307 202289621100241665499155461)
              ·
                refine ⟨37929303956295312281091649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202289621100241665499155461 37929303956295312281091649)
                ·
                  refine ⟨28446977967221484210818737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37929303956295312281091649 28446977967221484210818737)
                  ·
                    refine ⟨21335233475416113158114053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28446977967221484210818737 21335233475416113158114053)
                    ·
                      refine ⟨4000356276640521217146385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21335233475416113158114053 4000356276640521217146385)
                      ·
                        rfl

theorem cell23_7790666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_7790666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790666 prefixEnd_7790666 := by exact prefixLift 7790666
  have htrace : WordTrace (prefixWord ++ tailWord_7790666) baseStart_7790666 baseEnd_7790666 := by
    simpa [prefixWord, tailWord_7790666, baseEnd_7790666] using wordTrace_append hprefix tailTrace_7790666
  have hstable : (prefixWord ++ tailWord_7790666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790666).length < 2 ^ (prefixWord ++ tailWord_7790666).sum := by decide
  have hdescent : baseEnd_7790666 < baseStart_7790666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790676 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 7]
def baseStart_7790676 : Nat := 118140960795 + 7790676 * 2 ^ 59
def prefixEnd_7790676 : Nat := 4983230072969 + 3 ^ 40 * 7790676 * 2
def baseEnd_7790676 : Nat := 444484601271896242002371

theorem tailTrace_7790676 : CollatzResearch.WordTrace tailWord_7790676 prefixEnd_7790676 444484601271896242002371 := by
  unfold tailWord_7790676
  simp only [CollatzResearch.WordTrace]
  refine ⟨142074648761859434188043941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189432865015812578917391921 142074648761859434188043941)
  ·
    refine ⟨26638996642848643910258239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142074648761859434188043941 26638996642848643910258239)
    ·
      refine ⟨39958494964272965865387359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26638996642848643910258239 39958494964272965865387359)
      ·
        refine ⟨59937742446409448798081039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39958494964272965865387359 59937742446409448798081039)
        ·
          refine ⟨89906613669614173197121559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59937742446409448798081039 89906613669614173197121559)
          ·
            refine ⟨134859920504421259795682339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89906613669614173197121559 134859920504421259795682339)
            ·
              refine ⟨202289880756631889693523509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134859920504421259795682339 202289880756631889693523509)
              ·
                refine ⟨18964676320934239658767829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202289880756631889693523509 18964676320934239658767829)
                ·
                  refine ⟨444484601271896242002371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18964676320934239658767829 444484601271896242002371)
                  ·
                    rfl

theorem cell23_7790676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_7790676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790676 prefixEnd_7790676 := by exact prefixLift 7790676
  have htrace : WordTrace (prefixWord ++ tailWord_7790676) baseStart_7790676 baseEnd_7790676 := by
    simpa [prefixWord, tailWord_7790676, baseEnd_7790676] using wordTrace_append hprefix tailTrace_7790676
  have hstable : (prefixWord ++ tailWord_7790676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790676).length < 2 ^ (prefixWord ++ tailWord_7790676).sum := by decide
  have hdescent : baseEnd_7790676 < baseStart_7790676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790710 : List Nat := [5, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_7790710 : Nat := 118140960795 + 7790710 * 2 ^ 59
def prefixEnd_7790710 : Nat := 4983230072969 + 3 ^ 40 * 7790710 * 2
def baseEnd_7790710 : Nat := 444486541087702116110687

theorem tailTrace_7790710 : CollatzResearch.WordTrace tailWord_7790710 prefixEnd_7790710 444486541087702116110687 := by
  unfold tailWord_7790710
  simp only [CollatzResearch.WordTrace]
  refine ⟨17759408600349730761426599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189433691737063794788550389 17759408600349730761426599)
  ·
    refine ⟨26639112900524596142139899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17759408600349730761426599 26639112900524596142139899)
    ·
      refine ⟨39958669350786894213209849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26639112900524596142139899 39958669350786894213209849)
      ·
        refine ⟨29969002013090170659907387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39958669350786894213209849 29969002013090170659907387)
        ·
          refine ⟨44953503019635255989861081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29969002013090170659907387 44953503019635255989861081)
          ·
            refine ⟨33715127264726441992395811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44953503019635255989861081 33715127264726441992395811)
            ·
              refine ⟨50572690897089662988593717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33715127264726441992395811 50572690897089662988593717)
              ·
                refine ⟨4741189771602155905180661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50572690897089662988593717 4741189771602155905180661)
                ·
                  refine ⟨444486541087702116110687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4741189771602155905180661 444486541087702116110687)
                  ·
                    rfl

theorem cell23_7790710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_7790710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790710 prefixEnd_7790710 := by exact prefixLift 7790710
  have htrace : WordTrace (prefixWord ++ tailWord_7790710) baseStart_7790710 baseEnd_7790710 := by
    simpa [prefixWord, tailWord_7790710, baseEnd_7790710] using wordTrace_append hprefix tailTrace_7790710
  have hstable : (prefixWord ++ tailWord_7790710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790710).length < 2 ^ (prefixWord ++ tailWord_7790710).sum := by decide
  have hdescent : baseEnd_7790710 < baseStart_7790710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790721 : List Nat := [1, 2, 4, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_7790721 : Nat := 118140960795 + 7790721 * 2 ^ 59
def prefixEnd_7790721 : Nat := 4983230072969 + 3 ^ 40 * 7790721 * 2
def baseEnd_7790721 : Nat := 4000384518076518501958633

theorem tailTrace_7790721 : CollatzResearch.WordTrace tailWord_7790721 prefixEnd_7790721 4000384518076518501958633 := by
  unfold tailWord_7790721
  simp only [CollatzResearch.WordTrace]
  refine ⟨284150938808555841061476017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189433959205703894040984011 284150938808555841061476017)
  ·
    refine ⟨213113204106416880796107013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284150938808555841061476017 213113204106416880796107013)
    ·
      refine ⟨39958725769953165149270065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213113204106416880796107013 39958725769953165149270065)
      ·
        refine ⟨29969044327464873861952549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39958725769953165149270065 29969044327464873861952549)
        ·
          refine ⟨5619195811399663849116103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29969044327464873861952549 5619195811399663849116103)
          ·
            refine ⟨8428793717099495773674155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5619195811399663849116103 8428793717099495773674155)
            ·
              refine ⟨12643190575649243660511233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8428793717099495773674155 12643190575649243660511233)
              ·
                refine ⟨9482392931736932745383425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12643190575649243660511233 9482392931736932745383425)
                ·
                  refine ⟨7111794698802699559037569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9482392931736932745383425 7111794698802699559037569)
                  ·
                    refine ⟨5333846024102024669278177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7111794698802699559037569 5333846024102024669278177)
                    ·
                      refine ⟨4000384518076518501958633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5333846024102024669278177 4000384518076518501958633)
                      ·
                        rfl

theorem cell23_7790721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_7790721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790721 prefixEnd_7790721 := by exact prefixLift 7790721
  have htrace : WordTrace (prefixWord ++ tailWord_7790721) baseStart_7790721 baseEnd_7790721 := by
    simpa [prefixWord, tailWord_7790721, baseEnd_7790721] using wordTrace_append hprefix tailTrace_7790721
  have hstable : (prefixWord ++ tailWord_7790721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790721).length < 2 ^ (prefixWord ++ tailWord_7790721).sum := by decide
  have hdescent : baseEnd_7790721 < baseStart_7790721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790810 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3]
def baseStart_7790810 : Nat := 118140960795 + 7790810 * 2 ^ 59
def prefixEnd_7790810 : Nat := 4983230072969 + 3 ^ 40 * 7790810 * 2
def baseEnd_7790810 : Nat := 4000430217854768653745723

theorem tailTrace_7790810 : CollatzResearch.WordTrace tailWord_7790810 prefixEnd_7790810 4000430217854768653745723 := by
  unfold tailWord_7790810
  simp only [CollatzResearch.WordTrace]
  refine ⟨71038546226308352315366471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189436123270155606174310589 71038546226308352315366471)
  ·
    refine ⟨106557819339462528473049707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71038546226308352315366471 106557819339462528473049707)
    ·
      refine ⟨159836729009193792709574561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106557819339462528473049707 159836729009193792709574561)
      ·
        refine ⟨119877546756895344532180921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159836729009193792709574561 119877546756895344532180921)
        ·
          refine ⟨89908160067671508399135691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119877546756895344532180921 89908160067671508399135691)
          ·
            refine ⟨134862240101507262598703537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89908160067671508399135691 134862240101507262598703537)
            ·
              refine ⟨101146680076130446949027653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134862240101507262598703537 101146680076130446949027653)
              ·
                refine ⟨18965002514274458802942685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101146680076130446949027653 18965002514274458802942685)
                ·
                  refine ⟨7111875942852922051103507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18965002514274458802942685 7111875942852922051103507)
                  ·
                    refine ⟨10667813914279383076655261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7111875942852922051103507 10667813914279383076655261)
                    ·
                      refine ⟨4000430217854768653745723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10667813914279383076655261 4000430217854768653745723)
                      ·
                        rfl

theorem cell23_7790810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_7790810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790810 prefixEnd_7790810 := by exact prefixLift 7790810
  have htrace : WordTrace (prefixWord ++ tailWord_7790810) baseStart_7790810 baseEnd_7790810 := by
    simpa [prefixWord, tailWord_7790810, baseEnd_7790810] using wordTrace_append hprefix tailTrace_7790810
  have hstable : (prefixWord ++ tailWord_7790810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790810).length < 2 ^ (prefixWord ++ tailWord_7790810).sum := by decide
  have hdescent : baseEnd_7790810 < baseStart_7790810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790827 : List Nat := [1, 1, 1, 1, 2, 5, 2, 5, 1, 1, 3]
def baseStart_7790827 : Nat := 118140960795 + 7790827 * 2 ^ 59
def prefixEnd_7790827 : Nat := 4983230072969 + 3 ^ 40 * 7790827 * 2
def baseEnd_7790827 : Nat := 4000438947025895087233145

theorem tailTrace_7790827 : CollatzResearch.WordTrace tailWord_7790827 prefixEnd_7790827 4000438947025895087233145 := by
  unfold tailWord_7790827
  simp only [CollatzResearch.WordTrace]
  refine ⟨284154804946171821164834735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189436536630781214109889823 284154804946171821164834735)
  ·
    refine ⟨426232207419257731747252103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284154804946171821164834735 426232207419257731747252103)
    ·
      refine ⟨639348311128886597620878155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426232207419257731747252103 639348311128886597620878155)
      ·
        refine ⟨959022466693329896431317233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639348311128886597620878155 959022466693329896431317233)
        ·
          refine ⟨719266850019997422323487925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 959022466693329896431317233 719266850019997422323487925)
          ·
            refine ⟨67431267189374758342826993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 719266850019997422323487925 67431267189374758342826993)
            ·
              refine ⟨50573450392031068757120245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67431267189374758342826993 50573450392031068757120245)
              ·
                refine ⟨4741260974252912695980023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50573450392031068757120245 4741260974252912695980023)
                ·
                  refine ⟨7111891461379369043970035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741260974252912695980023 7111891461379369043970035)
                  ·
                    refine ⟨10667837192069053565955053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7111891461379369043970035 10667837192069053565955053)
                    ·
                      refine ⟨4000438947025895087233145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10667837192069053565955053 4000438947025895087233145)
                      ·
                        rfl

theorem cell23_7790827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 1, 1, 3].length) (baseStart_7790827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790827 prefixEnd_7790827 := by exact prefixLift 7790827
  have htrace : WordTrace (prefixWord ++ tailWord_7790827) baseStart_7790827 baseEnd_7790827 := by
    simpa [prefixWord, tailWord_7790827, baseEnd_7790827] using wordTrace_append hprefix tailTrace_7790827
  have hstable : (prefixWord ++ tailWord_7790827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790827).length < 2 ^ (prefixWord ++ tailWord_7790827).sum := by decide
  have hdescent : baseEnd_7790827 < baseStart_7790827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790844 : List Nat := [2, 2, 2, 1, 4, 2, 1, 4, 1, 1, 3]
def baseStart_7790844 : Nat := 118140960795 + 7790844 * 2 ^ 59
def prefixEnd_7790844 : Nat := 4983230072969 + 3 ^ 40 * 7790844 * 2
def baseEnd_7790844 : Nat := 4000447676197021520720567

theorem tailTrace_7790844 : CollatzResearch.WordTrace tailWord_7790844 prefixEnd_7790844 4000447676197021520720567 := by
  unfold tailWord_7790844
  simp only [CollatzResearch.WordTrace]
  refine ⟨142077712493555116534101793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189436949991406822045469057 142077712493555116534101793)
  ·
    refine ⟨106558284370166337400576345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142077712493555116534101793 106558284370166337400576345)
    ·
      refine ⟨79918713277624753050432259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106558284370166337400576345 79918713277624753050432259)
      ·
        refine ⟨119878069916437129575648389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79918713277624753050432259 119878069916437129575648389)
        ·
          refine ⟨22477138109331961795434073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119878069916437129575648389 22477138109331961795434073)
          ·
            refine ⟨16857853581998971346575555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22477138109331961795434073 16857853581998971346575555)
            ·
              refine ⟨25286780372998457019863333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16857853581998971346575555 25286780372998457019863333)
              ·
                refine ⟨4741271319937210691224375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25286780372998457019863333 4741271319937210691224375)
                ·
                  refine ⟨7111906979905816036836563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741271319937210691224375 7111906979905816036836563)
                  ·
                    refine ⟨10667860469858724055254845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7111906979905816036836563 10667860469858724055254845)
                    ·
                      refine ⟨4000447676197021520720567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10667860469858724055254845 4000447676197021520720567)
                      ·
                        rfl

theorem cell23_7790844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_7790844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790844 prefixEnd_7790844 := by exact prefixLift 7790844
  have htrace : WordTrace (prefixWord ++ tailWord_7790844) baseStart_7790844 baseEnd_7790844 := by
    simpa [prefixWord, tailWord_7790844, baseEnd_7790844] using wordTrace_append hprefix tailTrace_7790844
  have hstable : (prefixWord ++ tailWord_7790844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790844).length < 2 ^ (prefixWord ++ tailWord_7790844).sum := by decide
  have hdescent : baseEnd_7790844 < baseStart_7790844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790860 : List Nat := [2, 2, 1, 2, 2, 2, 1, 5, 2, 4]
def baseStart_7790860 : Nat := 118140960795 + 7790860 * 2 ^ 59
def prefixEnd_7790860 : Nat := 4983230072969 + 3 ^ 40 * 7790860 * 2
def baseEnd_7790860 : Nat := 1333485297295831152706831

theorem tailTrace_7790860 : CollatzResearch.WordTrace tailWord_7790860 prefixEnd_7790860 1333485297295831152706831 := by
  unfold tailWord_7790860
  simp only [CollatzResearch.WordTrace]
  refine ⟨142078004277526133900393017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189437339036701511867190689 142078004277526133900393017)
  ·
    refine ⟨106558503208144600425294763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142078004277526133900393017 106558503208144600425294763)
    ·
      refine ⟨159837754812216900637942145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106558503208144600425294763 159837754812216900637942145)
      ·
        refine ⟨119878316109162675478456609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159837754812216900637942145 119878316109162675478456609)
        ·
          refine ⟨89908737081872006608842457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119878316109162675478456609 89908737081872006608842457)
          ·
            refine ⟨67431552811404004956631843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89908737081872006608842457 67431552811404004956631843)
            ·
              refine ⟨101147329217106007434947765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67431552811404004956631843 101147329217106007434947765)
              ·
                refine ⟨9482562114103688197026353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101147329217106007434947765 9482562114103688197026353)
                ·
                  refine ⟨7111921585577766147769765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9482562114103688197026353 7111921585577766147769765)
                  ·
                    refine ⟨1333485297295831152706831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7111921585577766147769765 1333485297295831152706831)
                    ·
                      rfl

theorem cell23_7790860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_7790860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790860 prefixEnd_7790860 := by exact prefixLift 7790860
  have htrace : WordTrace (prefixWord ++ tailWord_7790860) baseStart_7790860 baseEnd_7790860 := by
    simpa [prefixWord, tailWord_7790860, baseEnd_7790860] using wordTrace_append hprefix tailTrace_7790860
  have hstable : (prefixWord ++ tailWord_7790860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790860).length < 2 ^ (prefixWord ++ tailWord_7790860).sum := by decide
  have hdescent : baseEnd_7790860 < baseStart_7790860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790878 : List Nat := [4, 3, 2, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_7790878 : Nat := 118140960795 + 7790878 * 2 ^ 59
def prefixEnd_7790878 : Nat := 4983230072969 + 3 ^ 40 * 7790878 * 2
def baseEnd_7790878 : Nat := 4000465134539274387695411

theorem tailTrace_7790878 : CollatzResearch.WordTrace tailWord_7790878 prefixEnd_7790878 4000465134539274387695411 := by
  unfold tailWord_7790878
  simp only [CollatzResearch.WordTrace]
  refine ⟨35519583133623382109367661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189437776712658037916627525 35519583133623382109367661)
  ·
    refine ⟨13319843675108768291012873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35519583133623382109367661 13319843675108768291012873)
    ·
      refine ⟨9989882756331576218259655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13319843675108768291012873 9989882756331576218259655)
      ·
        refine ⟨14984824134497364327389483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9989882756331576218259655 14984824134497364327389483)
        ·
          refine ⟨22477236201746046491084225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14984824134497364327389483 22477236201746046491084225)
          ·
            refine ⟨16857927151309534868313169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22477236201746046491084225 16857927151309534868313169)
            ·
              refine ⟨12643445363482151151234877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16857927151309534868313169 12643445363482151151234877)
              ·
                refine ⟨4741292011305806681713079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12643445363482151151234877 4741292011305806681713079)
                ·
                  refine ⟨7111938016958710022569619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741292011305806681713079 7111938016958710022569619)
                  ·
                    refine ⟨10667907025438065033854429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7111938016958710022569619 10667907025438065033854429)
                    ·
                      refine ⟨4000465134539274387695411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10667907025438065033854429 4000465134539274387695411)
                      ·
                        rfl

theorem cell23_7790878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_7790878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790878 prefixEnd_7790878 := by exact prefixLift 7790878
  have htrace : WordTrace (prefixWord ++ tailWord_7790878) baseStart_7790878 baseEnd_7790878 := by
    simpa [prefixWord, tailWord_7790878, baseEnd_7790878] using wordTrace_append hprefix tailTrace_7790878
  have hstable : (prefixWord ++ tailWord_7790878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790878).length < 2 ^ (prefixWord ++ tailWord_7790878).sum := by decide
  have hdescent : baseEnd_7790878 < baseStart_7790878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790880 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 4]
def baseStart_7790880 : Nat := 118140960795 + 7790880 * 2 ^ 59
def prefixEnd_7790880 : Nat := 4983230072969 + 3 ^ 40 * 7790880 * 2
def baseEnd_7790880 : Nat := 4000466161500583379870401

theorem tailTrace_7790880 : CollatzResearch.WordTrace tailWord_7790880 prefixEnd_7790880 4000466161500583379870401 := by
  unfold tailWord_7790880
  simp only [CollatzResearch.WordTrace]
  refine ⟨142078369007489905608257047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189437825343319874144342729 142078369007489905608257047)
  ·
    refine ⟨213117553511234858412385571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142078369007489905608257047 213117553511234858412385571)
    ·
      refine ⟨319676330266852287618578357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213117553511234858412385571 319676330266852287618578357)
      ·
        refine ⟨29969655962517401964241721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 319676330266852287618578357 29969655962517401964241721)
        ·
          refine ⟨22477241971888051473181291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29969655962517401964241721 22477241971888051473181291)
          ·
            refine ⟨33715862957832077209771937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22477241971888051473181291 33715862957832077209771937)
            ·
              refine ⟨25286897218374057907328953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33715862957832077209771937 25286897218374057907328953)
              ·
                refine ⟨18965172913780543430496715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25286897218374057907328953 18965172913780543430496715)
                ·
                  refine ⟨28447759370670815145745073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18965172913780543430496715 28447759370670815145745073)
                  ·
                    refine ⟨21335819528003111359308805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28447759370670815145745073 21335819528003111359308805)
                    ·
                      refine ⟨4000466161500583379870401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21335819528003111359308805 4000466161500583379870401)
                      ·
                        rfl

theorem cell23_7790880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_7790880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790880 prefixEnd_7790880 := by exact prefixLift 7790880
  have htrace : WordTrace (prefixWord ++ tailWord_7790880) baseStart_7790880 baseEnd_7790880 := by
    simpa [prefixWord, tailWord_7790880, baseEnd_7790880] using wordTrace_append hprefix tailTrace_7790880
  have hstable : (prefixWord ++ tailWord_7790880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790880).length < 2 ^ (prefixWord ++ tailWord_7790880).sum := by decide
  have hdescent : baseEnd_7790880 < baseStart_7790880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790884 : List Nat := [2, 3, 1, 3, 1, 4, 2, 1, 1, 1, 4]
def baseStart_7790884 : Nat := 118140960795 + 7790884 * 2 ^ 59
def prefixEnd_7790884 : Nat := 4983230072969 + 3 ^ 40 * 7790884 * 2
def baseEnd_7790884 : Nat := 4000468215423201364220383

theorem tailTrace_7790884 : CollatzResearch.WordTrace tailWord_7790884 prefixEnd_7790884 4000468215423201364220383 := by
  unfold tailWord_7790884
  simp only [CollatzResearch.WordTrace]
  refine ⟨142078441953482659949829853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189437922604643546599773137 142078441953482659949829853)
  ·
    refine ⟨53279415732555997481186195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142078441953482659949829853 53279415732555997481186195)
    ·
      refine ⟨79919123598833996221779293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53279415732555997481186195 79919123598833996221779293)
      ·
        refine ⟨29969671349562748583167235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79919123598833996221779293 29969671349562748583167235)
        ·
          refine ⟨44954507024344122874750853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29969671349562748583167235 44954507024344122874750853)
          ·
            refine ⟨8428970067064523039015785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44954507024344122874750853 8428970067064523039015785)
            ·
              refine ⟨6321727550298392279261839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8428970067064523039015785 6321727550298392279261839)
              ·
                refine ⟨9482591325447588418892759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321727550298392279261839 9482591325447588418892759)
                ·
                  refine ⟨14223886988171382628339139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9482591325447588418892759 14223886988171382628339139)
                  ·
                    refine ⟨21335830482257073942508709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14223886988171382628339139 21335830482257073942508709)
                    ·
                      refine ⟨4000468215423201364220383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21335830482257073942508709 4000468215423201364220383)
                      ·
                        rfl

theorem cell23_7790884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_7790884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790884 prefixEnd_7790884 := by exact prefixLift 7790884
  have htrace : WordTrace (prefixWord ++ tailWord_7790884) baseStart_7790884 baseEnd_7790884 := by
    simpa [prefixWord, tailWord_7790884, baseEnd_7790884] using wordTrace_append hprefix tailTrace_7790884
  have hstable : (prefixWord ++ tailWord_7790884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790884).length < 2 ^ (prefixWord ++ tailWord_7790884).sum := by decide
  have hdescent : baseEnd_7790884 < baseStart_7790884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790890 : List Nat := [3, 1, 4, 2, 2, 1, 10]
def baseStart_7790890 : Nat := 118140960795 + 7790890 * 2 ^ 59
def prefixEnd_7790890 : Nat := 4983230072969 + 3 ^ 40 * 7790890 * 2
def baseEnd_7790890 : Nat := 49388534522310226428955

theorem tailTrace_7790890 : CollatzResearch.WordTrace tailWord_7790890 prefixEnd_7790890 49388534522310226428955 := by
  unfold tailWord_7790890
  simp only [CollatzResearch.WordTrace]
  refine ⟨71039275686235895731094531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189438068496629055282918749 71039275686235895731094531)
  ·
    refine ⟨106558913529353843596641797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71039275686235895731094531 106558913529353843596641797)
    ·
      refine ⟨19979796286753845674370337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106558913529353843596641797 19979796286753845674370337)
      ·
        refine ⟨14984847215065384255777753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19979796286753845674370337 14984847215065384255777753)
        ·
          refine ⟨11238635411299038191833315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14984847215065384255777753 11238635411299038191833315)
          ·
            refine ⟨16857953116948557287749973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11238635411299038191833315 16857953116948557287749973)
            ·
              refine ⟨49388534522310226428955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16857953116948557287749973 49388534522310226428955)
              ·
                rfl

theorem cell23_7790890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 10].length) (baseStart_7790890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790890 prefixEnd_7790890 := by exact prefixLift 7790890
  have htrace : WordTrace (prefixWord ++ tailWord_7790890) baseStart_7790890 baseEnd_7790890 := by
    simpa [prefixWord, tailWord_7790890, baseEnd_7790890] using wordTrace_append hprefix tailTrace_7790890
  have hstable : (prefixWord ++ tailWord_7790890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790890).length < 2 ^ (prefixWord ++ tailWord_7790890).sum := by decide
  have hdescent : baseEnd_7790890 < baseStart_7790890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790894 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_7790894 : Nat := 118140960795 + 7790894 * 2 ^ 59
def prefixEnd_7790894 : Nat := 4983230072969 + 3 ^ 40 * 7790894 * 2
def baseEnd_7790894 : Nat := 1333491116743248775031779

theorem tailTrace_7790894 : CollatzResearch.WordTrace tailWord_7790894 prefixEnd_7790894 1333491116743248775031779 := by
  unfold tailWord_7790894
  simp only [CollatzResearch.WordTrace]
  refine ⟨35519656079616136450940467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189438165757952727738349157 35519656079616136450940467)
  ·
    refine ⟨53279484119424204676410701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35519656079616136450940467 53279484119424204676410701)
    ·
      refine ⟨19979806544784076753654013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53279484119424204676410701 19979806544784076753654013)
      ·
        refine ⟨7492427454294028782620255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19979806544784076753654013 7492427454294028782620255)
        ·
          refine ⟨11238641181441043173930383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7492427454294028782620255 11238641181441043173930383)
          ·
            refine ⟨16857961772161564760895575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11238641181441043173930383 16857961772161564760895575)
            ·
              refine ⟨25286942658242347141343363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16857961772161564760895575 25286942658242347141343363)
              ·
                refine ⟨37930413987363520712015045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25286942658242347141343363 37930413987363520712015045)
                ·
                  refine ⟨7111952622630660133502821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37930413987363520712015045 7111952622630660133502821)
                  ·
                    refine ⟨1333491116743248775031779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7111952622630660133502821 1333491116743248775031779)
                    ·
                      rfl

theorem cell23_7790894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_7790894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790894 prefixEnd_7790894 := by exact prefixLift 7790894
  have htrace : WordTrace (prefixWord ++ tailWord_7790894) baseStart_7790894 baseEnd_7790894 := by
    simpa [prefixWord, tailWord_7790894, baseEnd_7790894] using wordTrace_append hprefix tailTrace_7790894
  have hstable : (prefixWord ++ tailWord_7790894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790894).length < 2 ^ (prefixWord ++ tailWord_7790894).sum := by decide
  have hdescent : baseEnd_7790894 < baseStart_7790894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7790943 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 5]
def baseStart_7790943 : Nat := 118140960795 + 7790943 * 2 ^ 59
def prefixEnd_7790943 : Nat := 4983230072969 + 3 ^ 40 * 7790943 * 2
def baseEnd_7790943 : Nat := 4000498510781816633382611

theorem tailTrace_7790943 : CollatzResearch.WordTrace tailWord_7790943 prefixEnd_7790943 4000498510781816633382611 := by
  unfold tailWord_7790943
  simp only [CollatzResearch.WordTrace]
  refine ⟨284159035813751572976057483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189439357209167715317371655 284159035813751572976057483)
  ·
    refine ⟨426238553720627359464086225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284159035813751572976057483 426238553720627359464086225)
    ·
      refine ⟨319678915290470519598064669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426238553720627359464086225 319678915290470519598064669)
      ·
        refine ⟨119879593233926444849274251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319678915290470519598064669 119879593233926444849274251)
        ·
          refine ⟨179819389850889667273911377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119879593233926444849274251 179819389850889667273911377)
          ·
            refine ⟨134864542388167250455433533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179819389850889667273911377 134864542388167250455433533)
            ·
              refine ⟨50574203395562718920787575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134864542388167250455433533 50574203395562718920787575)
              ·
                refine ⟨75861305093344078381181363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50574203395562718920787575 75861305093344078381181363)
                ·
                  refine ⟨113791957640016117571772045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75861305093344078381181363 113791957640016117571772045)
                  ·
                    refine ⟨42671984115006044089414517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113791957640016117571772045 42671984115006044089414517)
                    ·
                      refine ⟨4000498510781816633382611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42671984115006044089414517 4000498510781816633382611)
                      ·
                        rfl

theorem cell23_7790943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_7790943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7790943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7790943 prefixEnd_7790943 := by exact prefixLift 7790943
  have htrace : WordTrace (prefixWord ++ tailWord_7790943) baseStart_7790943 baseEnd_7790943 := by
    simpa [prefixWord, tailWord_7790943, baseEnd_7790943] using wordTrace_append hprefix tailTrace_7790943
  have hstable : (prefixWord ++ tailWord_7790943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7790943).length < 2 ^ (prefixWord ++ tailWord_7790943).sum := by decide
  have hdescent : baseEnd_7790943 < baseStart_7790943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7790943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791023 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 4, 8]
def baseStart_7791023 : Nat := 118140960795 + 7791023 * 2 ^ 59
def prefixEnd_7791023 : Nat := 4983230072969 + 3 ^ 40 * 7791023 * 2
def baseEnd_7791023 : Nat := 1333513196411392106794081

theorem tailTrace_7791023 : CollatzResearch.WordTrace tailWord_7791023 prefixEnd_7791023 1333513196411392106794081 := by
  unfold tailWord_7791023
  simp only [CollatzResearch.WordTrace]
  refine ⟨284161953653461746638969723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189441302435641164425979815 284161953653461746638969723)
  ·
    refine ⟨426242930480192619958454585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284161953653461746638969723 426242930480192619958454585)
    ·
      refine ⟨319682197860144464968840939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426242930480192619958454585 319682197860144464968840939)
      ·
        refine ⟨479523296790216697453261409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319682197860144464968840939 479523296790216697453261409)
        ·
          refine ⟨359642472592662523089946057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479523296790216697453261409 359642472592662523089946057)
          ·
            refine ⟨269731854444496892317459543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359642472592662523089946057 269731854444496892317459543)
            ·
              refine ⟨404597781666745338476189315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269731854444496892317459543 404597781666745338476189315)
              ·
                refine ⟨606896672500118007714283973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404597781666745338476189315 606896672500118007714283973)
                ·
                  refine ⟨113793126093772126446428245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 606896672500118007714283973 113793126093772126446428245)
                  ·
                    refine ⟨1333513196411392106794081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113793126093772126446428245 1333513196411392106794081)
                    ·
                      rfl

theorem cell23_7791023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_7791023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791023 prefixEnd_7791023 := by exact prefixLift 7791023
  have htrace : WordTrace (prefixWord ++ tailWord_7791023) baseStart_7791023 baseEnd_7791023 := by
    simpa [prefixWord, tailWord_7791023, baseEnd_7791023] using wordTrace_append hprefix tailTrace_7791023
  have hstable : (prefixWord ++ tailWord_7791023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791023).length < 2 ^ (prefixWord ++ tailWord_7791023).sum := by decide
  have hdescent : baseEnd_7791023 < baseStart_7791023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791047 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_7791047 : Nat := 118140960795 + 7791047 * 2 ^ 59
def prefixEnd_7791047 : Nat := 4983230072969 + 3 ^ 40 * 7791047 * 2
def baseEnd_7791047 : Nat := 4000551912769884226482133

theorem tailTrace_7791047 : CollatzResearch.WordTrace tailWord_7791047 prefixEnd_7791047 4000551912769884226482133 := by
  unfold tailWord_7791047
  simp only [CollatzResearch.WordTrace]
  refine ⟨284162829005374798737843395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189441886003583199158562263 284162829005374798737843395)
  ·
    refine ⟨426244243508062198106765093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284162829005374798737843395 426244243508062198106765093)
    ·
      refine ⟨79920795657761662145018455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 426244243508062198106765093 79920795657761662145018455)
      ·
        refine ⟨119881193486642493217527683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79920795657761662145018455 119881193486642493217527683)
        ·
          refine ⟨179821790229963739826291525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119881193486642493217527683 179821790229963739826291525)
          ·
            refine ⟨33716585668118201217429661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179821790229963739826291525 33716585668118201217429661)
            ·
              refine ⟨12643719625544325456536123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33716585668118201217429661 12643719625544325456536123)
              ·
                refine ⟨18965579438316488184804185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12643719625544325456536123 18965579438316488184804185)
                ·
                  refine ⟨14224184578737366138603139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18965579438316488184804185 14224184578737366138603139)
                  ·
                    refine ⟨21336276868106049207904709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14224184578737366138603139 21336276868106049207904709)
                    ·
                      refine ⟨4000551912769884226482133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21336276868106049207904709 4000551912769884226482133)
                      ·
                        rfl

theorem cell23_7791047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_7791047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791047 prefixEnd_7791047 := by exact prefixLift 7791047
  have htrace : WordTrace (prefixWord ++ tailWord_7791047) baseStart_7791047 baseEnd_7791047 := by
    simpa [prefixWord, tailWord_7791047, baseEnd_7791047] using wordTrace_append hprefix tailTrace_7791047
  have hstable : (prefixWord ++ tailWord_7791047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791047).length < 2 ^ (prefixWord ++ tailWord_7791047).sum := by decide
  have hdescent : baseEnd_7791047 < baseStart_7791047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791107 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 1, 5, 2]
def baseStart_7791107 : Nat := 118140960795 + 7791107 * 2 ^ 59
def prefixEnd_7791107 : Nat := 4983230072969 + 3 ^ 40 * 7791107 * 2
def baseEnd_7791107 : Nat := 4000582721609153991731857

theorem tailTrace_7791107 : CollatzResearch.WordTrace tailWord_7791107 prefixEnd_7791107 4000582721609153991731857 := by
  unfold tailWord_7791107
  simp only [CollatzResearch.WordTrace]
  refine ⟨284165017385157428985027575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189443344923438285990018383 284165017385157428985027575)
  ·
    refine ⟨426247526077736143477541363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284165017385157428985027575 426247526077736143477541363)
    ·
      refine ⟨639371289116604215216312045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426247526077736143477541363 639371289116604215216312045)
      ·
        refine ⟨239764233418726580706117017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639371289116604215216312045 239764233418726580706117017)
        ·
          refine ⟨179823175064044935529587763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239764233418726580706117017 179823175064044935529587763)
          ·
            refine ⟨269734762596067403294381645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179823175064044935529587763 269734762596067403294381645)
            ·
              refine ⟨101150535973525276235393117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269734762596067403294381645 101150535973525276235393117)
              ·
                refine ⟨37931450990071978588272419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101150535973525276235393117 37931450990071978588272419)
                ·
                  refine ⟨56897176485107967882408629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37931450990071978588272419 56897176485107967882408629)
                  ·
                    refine ⟨5334110295478871988975809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56897176485107967882408629 5334110295478871988975809)
                    ·
                      refine ⟨4000582721609153991731857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5334110295478871988975809 4000582721609153991731857)
                      ·
                        rfl

theorem cell23_7791107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 5, 2].length) (baseStart_7791107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791107 prefixEnd_7791107 := by exact prefixLift 7791107
  have htrace : WordTrace (prefixWord ++ tailWord_7791107) baseStart_7791107 baseEnd_7791107 := by
    simpa [prefixWord, tailWord_7791107, baseEnd_7791107] using wordTrace_append hprefix tailTrace_7791107
  have hstable : (prefixWord ++ tailWord_7791107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791107).length < 2 ^ (prefixWord ++ tailWord_7791107).sum := by decide
  have hdescent : baseEnd_7791107 < baseStart_7791107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791108 : List Nat := [2, 3, 2, 3, 1, 3, 1, 3, 1, 4]
def baseStart_7791108 : Nat := 118140960795 + 7791108 * 2 ^ 59
def prefixEnd_7791108 : Nat := 4983230072969 + 3 ^ 40 * 7791108 * 2
def baseEnd_7791108 : Nat := 1333527745029936162606451

theorem tailTrace_7791108 : CollatzResearch.WordTrace tailWord_7791108 prefixEnd_7791108 1333527745029936162606451 := by
  unfold tailWord_7791108
  simp only [CollatzResearch.WordTrace]
  refine ⟨142082526929076903077906989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189443369238769204103875985 142082526929076903077906989)
  ·
    refine ⟨53280947598403838654215121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142082526929076903077906989 53280947598403838654215121)
    ·
      refine ⟨39960710698802878990661341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53280947598403838654215121 39960710698802878990661341)
      ·
        refine ⟨14985266512051079621498003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39960710698802878990661341 14985266512051079621498003)
        ·
          refine ⟨22477899768076619432247005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14985266512051079621498003 22477899768076619432247005)
          ·
            refine ⟨8429212413028732287092627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22477899768076619432247005 8429212413028732287092627)
            ·
              refine ⟨12643818619543098430638941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8429212413028732287092627 12643818619543098430638941)
              ·
                refine ⟨4741431982328661911489603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12643818619543098430638941 4741431982328661911489603)
                ·
                  refine ⟨7112147973492992867234405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741431982328661911489603 7112147973492992867234405)
                  ·
                    refine ⟨1333527745029936162606451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7112147973492992867234405 1333527745029936162606451)
                    ·
                      rfl

theorem cell23_7791108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_7791108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791108 prefixEnd_7791108 := by exact prefixLift 7791108
  have htrace : WordTrace (prefixWord ++ tailWord_7791108) baseStart_7791108 baseEnd_7791108 := by
    simpa [prefixWord, tailWord_7791108, baseEnd_7791108] using wordTrace_append hprefix tailTrace_7791108
  have hstable : (prefixWord ++ tailWord_7791108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791108).length < 2 ^ (prefixWord ++ tailWord_7791108).sum := by decide
  have hdescent : baseEnd_7791108 < baseStart_7791108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791137 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_7791137 : Nat := 118140960795 + 7791137 * 2 ^ 59
def prefixEnd_7791137 : Nat := 4983230072969 + 3 ^ 40 * 7791137 * 2
def baseEnd_7791137 : Nat := 4000598126028788874356719

theorem tailTrace_7791137 : CollatzResearch.WordTrace tailWord_7791137 prefixEnd_7791137 4000598126028788874356719 := by
  unfold tailWord_7791137
  simp only [CollatzResearch.WordTrace]
  refine ⟨284166111575048744108619665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189444074383365829405746443 284166111575048744108619665)
  ·
    refine ⟨213124583681286558081464749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284166111575048744108619665 213124583681286558081464749)
    ·
      refine ⟨79921718880482459280549281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213124583681286558081464749 79921718880482459280549281)
      ·
        refine ⟨59941289160361844460411961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79921718880482459280549281 59941289160361844460411961)
        ·
          refine ⟨44955966870271383345308971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59941289160361844460411961 44955966870271383345308971)
          ·
            refine ⟨67433950305407075017963457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44955966870271383345308971 67433950305407075017963457)
            ·
              refine ⟨50575462729055306263472593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67433950305407075017963457 50575462729055306263472593)
              ·
                refine ⟨37931597046791479697604445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50575462729055306263472593 37931597046791479697604445)
                ·
                  refine ⟨14224348892546804886601667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37931597046791479697604445 14224348892546804886601667)
                  ·
                    refine ⟨21336523338820207329902501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14224348892546804886601667 21336523338820207329902501)
                    ·
                      refine ⟨4000598126028788874356719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21336523338820207329902501 4000598126028788874356719)
                      ·
                        rfl

theorem cell23_7791137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_7791137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791137 prefixEnd_7791137 := by exact prefixLift 7791137
  have htrace : WordTrace (prefixWord ++ tailWord_7791137) baseStart_7791137 baseEnd_7791137 := by
    simpa [prefixWord, tailWord_7791137, baseEnd_7791137] using wordTrace_append hprefix tailTrace_7791137
  have hstable : (prefixWord ++ tailWord_7791137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791137).length < 2 ^ (prefixWord ++ tailWord_7791137).sum := by decide
  have hdescent : baseEnd_7791137 < baseStart_7791137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791154 : List Nat := [3, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4]
def baseStart_7791154 : Nat := 118140960795 + 7791154 * 2 ^ 59
def prefixEnd_7791154 : Nat := 4983230072969 + 3 ^ 40 * 7791154 * 2
def baseEnd_7791154 : Nat := 4000606855199915307844141

theorem tailTrace_7791154 : CollatzResearch.WordTrace tailWord_7791154 prefixEnd_7791154 4000606855199915307844141 := by
  unfold tailWord_7791154
  simp only [CollatzResearch.WordTrace]
  refine ⟨71041682903996789002997129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189444487743991437341325677 71041682903996789002997129)
  ·
    refine ⟨53281262177997591752247847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71041682903996789002997129 53281262177997591752247847)
    ·
      refine ⟨79921893266996387628371771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53281262177997591752247847 79921893266996387628371771)
      ·
        refine ⟨119882839900494581442557657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79921893266996387628371771 119882839900494581442557657)
        ·
          refine ⟨89912129925370936081918243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119882839900494581442557657 89912129925370936081918243)
          ·
            refine ⟨134868194888056404122877365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89912129925370936081918243 134868194888056404122877365)
            ·
              refine ⟨12643893270755287886519753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134868194888056404122877365 12643893270755287886519753)
              ·
                refine ⟨9482919953066465914889815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12643893270755287886519753 9482919953066465914889815)
                ·
                  refine ⟨14224379929599698872334723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9482919953066465914889815 14224379929599698872334723)
                  ·
                    refine ⟨21336569894399548308502085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14224379929599698872334723 21336569894399548308502085)
                    ·
                      refine ⟨4000606855199915307844141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21336569894399548308502085 4000606855199915307844141)
                      ·
                        rfl

theorem cell23_7791154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_7791154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791154 prefixEnd_7791154 := by exact prefixLift 7791154
  have htrace : WordTrace (prefixWord ++ tailWord_7791154) baseStart_7791154 baseEnd_7791154 := by
    simpa [prefixWord, tailWord_7791154, baseEnd_7791154] using wordTrace_append hprefix tailTrace_7791154
  have hstable : (prefixWord ++ tailWord_7791154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791154).length < 2 ^ (prefixWord ++ tailWord_7791154).sum := by decide
  have hdescent : baseEnd_7791154 < baseStart_7791154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791158 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_7791158 : Nat := 118140960795 + 7791158 * 2 ^ 59
def prefixEnd_7791158 : Nat := 4983230072969 + 3 ^ 40 * 7791158 * 2
def baseEnd_7791158 : Nat := 4000608909122533292194123

theorem tailTrace_7791158 : CollatzResearch.WordTrace tailWord_7791158 prefixEnd_7791158 4000608909122533292194123 := by
  unfold tailWord_7791158
  simp only [CollatzResearch.WordTrace]
  refine ⟨17760429844248291543445883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189444585005315109796756085 17760429844248291543445883)
  ·
    refine ⟨26640644766372437315168825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17760429844248291543445883 26640644766372437315168825)
    ·
      refine ⟨19980483574779327986376619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26640644766372437315168825 19980483574779327986376619)
      ·
        refine ⟨29970725362168991979564929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19980483574779327986376619 29970725362168991979564929)
        ·
          refine ⟨22478044021626743984673697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29970725362168991979564929 22478044021626743984673697)
          ·
            refine ⟨16858533016220057988505273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22478044021626743984673697 16858533016220057988505273)
            ·
              refine ⟨12643899762165043491378955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16858533016220057988505273 12643899762165043491378955)
              ·
                refine ⟨18965849643247565237068433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12643899762165043491378955 18965849643247565237068433)
                ·
                  refine ⟨14224387232435673927801325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18965849643247565237068433 14224387232435673927801325)
                  ·
                    refine ⟨5334145212163377722925497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14224387232435673927801325 5334145212163377722925497)
                    ·
                      refine ⟨4000608909122533292194123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5334145212163377722925497 4000608909122533292194123)
                      ·
                        rfl

theorem cell23_7791158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_7791158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791158 prefixEnd_7791158 := by exact prefixLift 7791158
  have htrace : WordTrace (prefixWord ++ tailWord_7791158) baseStart_7791158 baseEnd_7791158 := by
    simpa [prefixWord, tailWord_7791158, baseEnd_7791158] using wordTrace_append hprefix tailTrace_7791158
  have hstable : (prefixWord ++ tailWord_7791158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791158).length < 2 ^ (prefixWord ++ tailWord_7791158).sum := by decide
  have hdescent : baseEnd_7791158 < baseStart_7791158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791160 : List Nat := [2, 1, 2, 1, 4, 1, 1, 11]
def baseStart_7791160 : Nat := 118140960795 + 7791160 * 2 ^ 59
def prefixEnd_7791160 : Nat := 4983230072969 + 3 ^ 40 * 7791160 * 2
def baseEnd_7791160 : Nat := 148170738373475640161819

theorem tailTrace_7791160 : CollatzResearch.WordTrace tailWord_7791160 prefixEnd_7791160 148170738373475640161819 := by
  unfold tailWord_7791160
  simp only [CollatzResearch.WordTrace]
  refine ⟨142083475226982709518353467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189444633635976946024471289 142083475226982709518353467)
  ·
    refine ⟨213125212840474064277530201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142083475226982709518353467 213125212840474064277530201)
    ·
      refine ⟨159843909630355548208147651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213125212840474064277530201 159843909630355548208147651)
      ·
        refine ⟨239765864445533322312221477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159843909630355548208147651 239765864445533322312221477)
        ·
          refine ⟨44956099583537497933541527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239765864445533322312221477 44956099583537497933541527)
          ·
            refine ⟨67434149375306246900312291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44956099583537497933541527 67434149375306246900312291)
            ·
              refine ⟨101151224062959370350468437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67434149375306246900312291 101151224062959370350468437)
              ·
                refine ⟨148170738373475640161819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 101151224062959370350468437 148170738373475640161819)
                ·
                  rfl

theorem cell23_7791160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 11].length) (baseStart_7791160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791160 prefixEnd_7791160 := by exact prefixLift 7791160
  have htrace : WordTrace (prefixWord ++ tailWord_7791160) baseStart_7791160 baseEnd_7791160 := by
    simpa [prefixWord, tailWord_7791160, baseEnd_7791160] using wordTrace_append hprefix tailTrace_7791160
  have hstable : (prefixWord ++ tailWord_7791160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791160).length < 2 ^ (prefixWord ++ tailWord_7791160).sum := by decide
  have hdescent : baseEnd_7791160 < baseStart_7791160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791167 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 4]
def baseStart_7791167 : Nat := 118140960795 + 7791167 * 2 ^ 59
def prefixEnd_7791167 : Nat := 4983230072969 + 3 ^ 40 * 7791167 * 2
def baseEnd_7791167 : Nat := 4000613530448423756981581

theorem tailTrace_7791167 : CollatzResearch.WordTrace tailWord_7791167 prefixEnd_7791167 4000613530448423756981581 := by
  unfold tailWord_7791167
  simp only [CollatzResearch.WordTrace]
  refine ⟨284167205764940059232211755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189444803843293372821474503 284167205764940059232211755)
  ·
    refine ⟨426250808647410088848317633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284167205764940059232211755 426250808647410088848317633)
    ·
      refine ⟨319688106485557566636238225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426250808647410088848317633 319688106485557566636238225)
      ·
        refine ⟨239766079864168174977178669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319688106485557566636238225 239766079864168174977178669)
        ·
          refine ⟨89912279949063065616442001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239766079864168174977178669 89912279949063065616442001)
          ·
            refine ⟨67434209961797299212331501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89912279949063065616442001 67434209961797299212331501)
            ·
              refine ⟨25287828735673987204624313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67434209961797299212331501 25287828735673987204624313)
              ·
                refine ⟨18965871551755490403468235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25287828735673987204624313 18965871551755490403468235)
                ·
                  refine ⟨28448807327633235605202353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18965871551755490403468235 28448807327633235605202353)
                  ·
                    refine ⟨21336605495724926703901765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28448807327633235605202353 21336605495724926703901765)
                    ·
                      refine ⟨4000613530448423756981581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21336605495724926703901765 4000613530448423756981581)
                      ·
                        rfl

theorem cell23_7791167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_7791167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791167 prefixEnd_7791167 := by exact prefixLift 7791167
  have htrace : WordTrace (prefixWord ++ tailWord_7791167) baseStart_7791167 baseEnd_7791167 := by
    simpa [prefixWord, tailWord_7791167, baseEnd_7791167] using wordTrace_append hprefix tailTrace_7791167
  have hstable : (prefixWord ++ tailWord_7791167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791167).length < 2 ^ (prefixWord ++ tailWord_7791167).sum := by decide
  have hdescent : baseEnd_7791167 < baseStart_7791167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791181 : List Nat := [1, 6, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_7791181 : Nat := 118140960795 + 7791181 * 2 ^ 59
def prefixEnd_7791181 : Nat := 4983230072969 + 3 ^ 40 * 7791181 * 2
def baseEnd_7791181 : Nat := 1333540239725862234068839

theorem tailTrace_7791181 : CollatzResearch.WordTrace tailWord_7791181 prefixEnd_7791181 1333540239725862234068839 := by
  unfold tailWord_7791181
  simp only [CollatzResearch.WordTrace]
  refine ⟨284167716386889339623221397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189445144257926226415480931 284167716386889339623221397)
  ·
    refine ⟨13320361705635437794838503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 284167716386889339623221397 13320361705635437794838503)
    ·
      refine ⟨19980542558453156692257755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13320361705635437794838503 19980542558453156692257755)
      ·
        refine ⟨29970813837679735038386633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19980542558453156692257755 29970813837679735038386633)
        ·
          refine ⟨22478110378259801278789975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29970813837679735038386633 22478110378259801278789975)
          ·
            refine ⟨33717165567389701918184963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22478110378259801278789975 33717165567389701918184963)
            ·
              refine ⟨50575748351084552877277445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33717165567389701918184963 50575748351084552877277445)
              ·
                refine ⟨9482952815828353664489521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50575748351084552877277445 9482952815828353664489521)
                ·
                  refine ⟨7112214611871265248367141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9482952815828353664489521 7112214611871265248367141)
                  ·
                    refine ⟨1333540239725862234068839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7112214611871265248367141 1333540239725862234068839)
                    ·
                      rfl

theorem cell23_7791181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_7791181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791181 prefixEnd_7791181 := by exact prefixLift 7791181
  have htrace : WordTrace (prefixWord ++ tailWord_7791181) baseStart_7791181 baseEnd_7791181 := by
    simpa [prefixWord, tailWord_7791181, baseEnd_7791181] using wordTrace_append hprefix tailTrace_7791181
  have hstable : (prefixWord ++ tailWord_7791181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791181).length < 2 ^ (prefixWord ++ tailWord_7791181).sum := by decide
  have hdescent : baseEnd_7791181 < baseStart_7791181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791204 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_7791204 : Nat := 118140960795 + 7791204 * 2 ^ 59
def prefixEnd_7791204 : Nat := 4983230072969 + 3 ^ 40 * 7791204 * 2
def baseEnd_7791204 : Nat := 4000632529232640112218911

theorem tailTrace_7791204 : CollatzResearch.WordTrace tailWord_7791204 prefixEnd_7791204 4000632529232640112218911 := by
  unfold tailWord_7791204
  simp only [CollatzResearch.WordTrace]
  refine ⟨142084277632903007275654333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189445703510537343034205777 142084277632903007275654333)
  ·
    refine ⟨53281604112338627728370375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142084277632903007275654333 53281604112338627728370375)
    ·
      refine ⟨79922406168507941592555563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53281604112338627728370375 79922406168507941592555563)
      ·
        refine ⟨119883609252761912388833345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79922406168507941592555563 119883609252761912388833345)
        ·
          refine ⟨89912706939571434291625009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119883609252761912388833345 89912706939571434291625009)
          ·
            refine ⟨67434530204678575718718757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89912706939571434291625009 67434530204678575718718757)
            ·
              refine ⟨12643974413377232947259767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67434530204678575718718757 12643974413377232947259767)
              ·
                refine ⟨18965961620065849420889651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12643974413377232947259767 18965961620065849420889651)
                ·
                  refine ⟨28448942430098774131334477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18965961620065849420889651 28448942430098774131334477)
                  ·
                    refine ⟨10668353411287040299250429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28448942430098774131334477 10668353411287040299250429)
                    ·
                      refine ⟨4000632529232640112218911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10668353411287040299250429 4000632529232640112218911)
                      ·
                        rfl

theorem cell23_7791204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_7791204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791204 prefixEnd_7791204 := by exact prefixLift 7791204
  have htrace : WordTrace (prefixWord ++ tailWord_7791204) baseStart_7791204 baseEnd_7791204 := by
    simpa [prefixWord, tailWord_7791204, baseEnd_7791204] using wordTrace_append hprefix tailTrace_7791204
  have hstable : (prefixWord ++ tailWord_7791204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791204).length < 2 ^ (prefixWord ++ tailWord_7791204).sum := by decide
  have hdescent : baseEnd_7791204 < baseStart_7791204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791222 : List Nat := [5, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2]
def baseStart_7791222 : Nat := 118140960795 + 7791222 * 2 ^ 59
def prefixEnd_7791222 : Nat := 4983230072969 + 3 ^ 40 * 7791222 * 2
def baseEnd_7791222 : Nat := 4000641771884421041793829

theorem tailTrace_7791222 : CollatzResearch.WordTrace tailWord_7791222 prefixEnd_7791222 4000641771884421041793829 := by
  unfold tailWord_7791222
  simp only [CollatzResearch.WordTrace]
  refine ⟨17760575736233800226591495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189446141186493869083642613 17760575736233800226591495)
  ·
    refine ⟨26640863604350700339887243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17760575736233800226591495 26640863604350700339887243)
    ·
      refine ⟨39961295406526050509830865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26640863604350700339887243 39961295406526050509830865)
      ·
        refine ⟨29970971554894537882373149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39961295406526050509830865 29970971554894537882373149)
        ·
          refine ⟨11239114333085451705889931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29970971554894537882373149 11239114333085451705889931)
          ·
            refine ⟨16858671499628177558834897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11239114333085451705889931 16858671499628177558834897)
            ·
              refine ⟨12644003624721133169126173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16858671499628177558834897 12644003624721133169126173)
              ·
                refine ⟨4741501359270424938422315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12644003624721133169126173 4741501359270424938422315)
                ·
                  refine ⟨7112252038905637407633473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741501359270424938422315 7112252038905637407633473)
                  ·
                    refine ⟨5334189029179228055725105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7112252038905637407633473 5334189029179228055725105)
                    ·
                      refine ⟨4000641771884421041793829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5334189029179228055725105 4000641771884421041793829)
                      ·
                        rfl

theorem cell23_7791222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_7791222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791222 prefixEnd_7791222 := by exact prefixLift 7791222
  have htrace : WordTrace (prefixWord ++ tailWord_7791222) baseStart_7791222 baseEnd_7791222 := by
    simpa [prefixWord, tailWord_7791222, baseEnd_7791222] using wordTrace_append hprefix tailTrace_7791222
  have hstable : (prefixWord ++ tailWord_7791222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791222).length < 2 ^ (prefixWord ++ tailWord_7791222).sum := by decide
  have hdescent : baseEnd_7791222 < baseStart_7791222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791237 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 2, 6]
def baseStart_7791237 : Nat := 118140960795 + 7791237 * 2 ^ 59
def prefixEnd_7791237 : Nat := 4983230072969 + 3 ^ 40 * 7791237 * 2
def baseEnd_7791237 : Nat := 1333549824698079494368753

theorem tailTrace_7791237 : CollatzResearch.WordTrace tailWord_7791237 prefixEnd_7791237 1333549824698079494368753 := by
  unfold tailWord_7791237
  simp only [CollatzResearch.WordTrace]
  refine ⟨284169758874686461187259965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189446505916457640791506643 284169758874686461187259965)
  ·
    refine ⟨106563659578007422945222487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284169758874686461187259965 106563659578007422945222487)
    ·
      refine ⟨159845489367011134417833731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106563659578007422945222487 159845489367011134417833731)
      ·
        refine ⟨239768234050516701626750597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159845489367011134417833731 239768234050516701626750597)
        ·
          refine ⟨44956543884471881555015737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239768234050516701626750597 44956543884471881555015737)
          ·
            refine ⟨33717407913353911166261803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44956543884471881555015737 33717407913353911166261803)
            ·
              refine ⟨50576111870030866749392705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33717407913353911166261803 50576111870030866749392705)
              ·
                refine ⟨37932083902523150062044529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50576111870030866749392705 37932083902523150062044529)
                ·
                  refine ⟨28449062926892362546533397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37932083902523150062044529 28449062926892362546533397)
                  ·
                    refine ⟨1333549824698079494368753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28449062926892362546533397 1333549824698079494368753)
                    ·
                      rfl

theorem cell23_7791237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_7791237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791237 prefixEnd_7791237 := by exact prefixLift 7791237
  have htrace : WordTrace (prefixWord ++ tailWord_7791237) baseStart_7791237 baseEnd_7791237 := by
    simpa [prefixWord, tailWord_7791237, baseEnd_7791237] using wordTrace_append hprefix tailTrace_7791237
  have hstable : (prefixWord ++ tailWord_7791237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791237).length < 2 ^ (prefixWord ++ tailWord_7791237).sum := by decide
  have hdescent : baseEnd_7791237 < baseStart_7791237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791257 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 2, 2, 4]
def baseStart_7791257 : Nat := 118140960795 + 7791257 * 2 ^ 59
def prefixEnd_7791257 : Nat := 4983230072969 + 3 ^ 40 * 7791257 * 2
def baseEnd_7791257 : Nat := 4000659743707328404856167

theorem tailTrace_7791257 : CollatzResearch.WordTrace tailWord_7791257 prefixEnd_7791257 4000659743707328404856167 := by
  unfold tailWord_7791257
  simp only [CollatzResearch.WordTrace]
  refine ⟨284170488334614004602988025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189446992223076003068658683 284170488334614004602988025)
  ·
    refine ⟨213127866250960503452241019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284170488334614004602988025 213127866250960503452241019)
    ·
      refine ⟨319691799376440755178361529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213127866250960503452241019 319691799376440755178361529)
      ·
        refine ⟨239768849532330566383771147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319691799376440755178361529 239768849532330566383771147)
        ·
          refine ⟨359653274298495849575656721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239768849532330566383771147 359653274298495849575656721)
          ·
            refine ⟨269739955723871887181742541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359653274298495849575656721 269739955723871887181742541)
            ·
              refine ⟨101152483396451957693153453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269739955723871887181742541 101152483396451957693153453)
              ·
                refine ⟨37932181273669484134932545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101152483396451957693153453 37932181273669484134932545)
                ·
                  refine ⟨28449135955252113101199409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37932181273669484134932545 28449135955252113101199409)
                  ·
                    refine ⟨21336851966439084825899557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28449135955252113101199409 21336851966439084825899557)
                    ·
                      refine ⟨4000659743707328404856167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21336851966439084825899557 4000659743707328404856167)
                      ·
                        rfl

theorem cell23_7791257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_7791257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791257 prefixEnd_7791257 := by exact prefixLift 7791257
  have htrace : WordTrace (prefixWord ++ tailWord_7791257) baseStart_7791257 baseEnd_7791257 := by
    simpa [prefixWord, tailWord_7791257, baseEnd_7791257] using wordTrace_append hprefix tailTrace_7791257
  have hstable : (prefixWord ++ tailWord_7791257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791257).length < 2 ^ (prefixWord ++ tailWord_7791257).sum := by decide
  have hdescent : baseEnd_7791257 < baseStart_7791257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791261 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_7791261 : Nat := 118140960795 + 7791261 * 2 ^ 59
def prefixEnd_7791261 : Nat := 4983230072969 + 3 ^ 40 * 7791261 * 2
def baseEnd_7791261 : Nat := 4000661797629946389206149

theorem tailTrace_7791261 : CollatzResearch.WordTrace tailWord_7791261 prefixEnd_7791261 4000661797629946389206149 := by
  unfold tailWord_7791261
  simp only [CollatzResearch.WordTrace]
  refine ⟨284170634226599513286133637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189447089484399675524089091 284170634226599513286133637)
  ·
    refine ⟨53281993917487408741150057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284170634226599513286133637 53281993917487408741150057)
    ·
      refine ⟨39961495438115556555862543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53281993917487408741150057 39961495438115556555862543)
      ·
        refine ⟨59942243157173334833793815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39961495438115556555862543 59942243157173334833793815)
        ·
          refine ⟨89913364735760002250690723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59942243157173334833793815 89913364735760002250690723)
          ·
            refine ⟨134870047103640003376036085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89913364735760002250690723 134870047103640003376036085)
            ·
              refine ⟨12644066915966250316503383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134870047103640003376036085 12644066915966250316503383)
              ·
                refine ⟨18966100373949375474755075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12644066915966250316503383 18966100373949375474755075)
                ·
                  refine ⟨28449150560924063212132613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18966100373949375474755075 28449150560924063212132613)
                  ·
                    refine ⟨5334215730173261852274865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28449150560924063212132613 5334215730173261852274865)
                    ·
                      refine ⟨4000661797629946389206149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5334215730173261852274865 4000661797629946389206149)
                      ·
                        rfl

theorem cell23_7791261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_7791261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791261 prefixEnd_7791261 := by exact prefixLift 7791261
  have htrace : WordTrace (prefixWord ++ tailWord_7791261) baseStart_7791261 baseEnd_7791261 := by
    simpa [prefixWord, tailWord_7791261, baseEnd_7791261] using wordTrace_append hprefix tailTrace_7791261
  have hstable : (prefixWord ++ tailWord_7791261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791261).length < 2 ^ (prefixWord ++ tailWord_7791261).sum := by decide
  have hdescent : baseEnd_7791261 < baseStart_7791261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791281 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 2, 1, 5]
def baseStart_7791281 : Nat := 118140960795 + 7791281 * 2 ^ 59
def prefixEnd_7791281 : Nat := 4983230072969 + 3 ^ 40 * 7791281 * 2
def baseEnd_7791281 : Nat := 4000672067243036310956057

theorem tailTrace_7791281 : CollatzResearch.WordTrace tailWord_7791281 prefixEnd_7791281 4000672067243036310956057 := by
  unfold tailWord_7791281
  simp only [CollatzResearch.WordTrace]
  refine ⟨284171363686527056701861697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189447575791018037801241131 284171363686527056701861697)
  ·
    refine ⟨213128522764895292526396273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284171363686527056701861697 213128522764895292526396273)
    ·
      refine ⟨159846392073671469394797205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213128522764895292526396273 159846392073671469394797205)
      ·
        refine ⟨7492799628453350127881119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159846392073671469394797205 7492799628453350127881119)
        ·
          refine ⟨11239199442680025191821679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7492799628453350127881119 11239199442680025191821679)
          ·
            refine ⟨16858799164020037787732519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11239199442680025191821679 16858799164020037787732519)
            ·
              refine ⟨25288198746030056681598779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16858799164020037787732519 25288198746030056681598779)
              ·
                refine ⟨37932298119045085022398169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25288198746030056681598779 37932298119045085022398169)
                ·
                  refine ⟨28449223589283813766798627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37932298119045085022398169 28449223589283813766798627)
                  ·
                    refine ⟨42673835383925720650197941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28449223589283813766798627 42673835383925720650197941)
                    ·
                      refine ⟨4000672067243036310956057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42673835383925720650197941 4000672067243036310956057)
                      ·
                        rfl

theorem cell23_7791281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_7791281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791281 prefixEnd_7791281 := by exact prefixLift 7791281
  have htrace : WordTrace (prefixWord ++ tailWord_7791281) baseStart_7791281 baseEnd_7791281 := by
    simpa [prefixWord, tailWord_7791281, baseEnd_7791281] using wordTrace_append hprefix tailTrace_7791281
  have hstable : (prefixWord ++ tailWord_7791281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791281).length < 2 ^ (prefixWord ++ tailWord_7791281).sum := by decide
  have hdescent : baseEnd_7791281 < baseStart_7791281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791331 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 2, 5]
def baseStart_7791331 : Nat := 118140960795 + 7791331 * 2 ^ 59
def prefixEnd_7791331 : Nat := 4983230072969 + 3 ^ 40 * 7791331 * 2
def baseEnd_7791331 : Nat := 1333565913758587038443609

theorem tailTrace_7791331 : CollatzResearch.WordTrace tailWord_7791331 prefixEnd_7791331 1333565913758587038443609 := by
  unfold tailWord_7791331
  simp only [CollatzResearch.WordTrace]
  refine ⟨284173187336345915241181847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189448791557563943494121231 284173187336345915241181847)
  ·
    refine ⟨426259781004518872861772771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284173187336345915241181847 426259781004518872861772771)
    ·
      refine ⟨639389671506778309292659157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426259781004518872861772771 639389671506778309292659157)
      ·
        refine ⟨14985695425940116624046699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 639389671506778309292659157 14985695425940116624046699)
        ·
          refine ⟨22478543138910174936070049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14985695425940116624046699 22478543138910174936070049)
          ·
            refine ⟨16858907354182631202052537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22478543138910174936070049 16858907354182631202052537)
            ·
              refine ⟨12644180515636973401539403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16858907354182631202052537 12644180515636973401539403)
              ·
                refine ⟨18966270773455460102309105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12644180515636973401539403 18966270773455460102309105)
                ·
                  refine ⟨14224703080091595076731829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18966270773455460102309105 14224703080091595076731829)
                  ·
                    refine ⟨1333565913758587038443609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14224703080091595076731829 1333565913758587038443609)
                    ·
                      rfl

theorem cell23_7791331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 5].length) (baseStart_7791331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791331 prefixEnd_7791331 := by exact prefixLift 7791331
  have htrace : WordTrace (prefixWord ++ tailWord_7791331) baseStart_7791331 baseEnd_7791331 := by
    simpa [prefixWord, tailWord_7791331, baseEnd_7791331] using wordTrace_append hprefix tailTrace_7791331
  have hstable : (prefixWord ++ tailWord_7791331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791331).length < 2 ^ (prefixWord ++ tailWord_7791331).sum := by decide
  have hdescent : baseEnd_7791331 < baseStart_7791331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791347 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 6]
def baseStart_7791347 : Nat := 118140960795 + 7791347 * 2 ^ 59
def prefixEnd_7791347 : Nat := 4983230072969 + 3 ^ 40 * 7791347 * 2
def baseEnd_7791347 : Nat := 4000705956966233052730753

theorem tailTrace_7791347 : CollatzResearch.WordTrace tailWord_7791347 prefixEnd_7791347 4000705956966233052730753 := by
  unfold tailWord_7791347
  simp only [CollatzResearch.WordTrace]
  refine ⟨284173770904287949973764295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189449180602858633315842863 284173770904287949973764295)
  ·
    refine ⟨426260656356431924960646443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284173770904287949973764295 426260656356431924960646443)
    ·
      refine ⟨639390984534647887440969665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426260656356431924960646443 639390984534647887440969665)
      ·
        refine ⟨479543238400985915580727249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639390984534647887440969665 479543238400985915580727249)
        ·
          refine ⟨359657428800739436685545437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479543238400985915580727249 359657428800739436685545437)
          ·
            refine ⟨134871535800277288757079539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359657428800739436685545437 134871535800277288757079539)
            ·
              refine ⟨202307303700415933135619309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134871535800277288757079539 202307303700415933135619309)
              ·
                refine ⟨75865238887655974925857241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202307303700415933135619309 75865238887655974925857241)
                ·
                  refine ⟨56898929165741981194392931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75865238887655974925857241 56898929165741981194392931)
                  ·
                    refine ⟨85348393748612971791589397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56898929165741981194392931 85348393748612971791589397)
                    ·
                      refine ⟨4000705956966233052730753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85348393748612971791589397 4000705956966233052730753)
                      ·
                        rfl

theorem cell23_7791347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_7791347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791347 prefixEnd_7791347 := by exact prefixLift 7791347
  have htrace : WordTrace (prefixWord ++ tailWord_7791347) baseStart_7791347 baseEnd_7791347 := by
    simpa [prefixWord, tailWord_7791347, baseEnd_7791347] using wordTrace_append hprefix tailTrace_7791347
  have hstable : (prefixWord ++ tailWord_7791347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791347).length < 2 ^ (prefixWord ++ tailWord_7791347).sum := by decide
  have hdescent : baseEnd_7791347 < baseStart_7791347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791388 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_7791388 : Nat := 118140960795 + 7791388 * 2 ^ 59
def prefixEnd_7791388 : Nat := 4983230072969 + 3 ^ 40 * 7791388 * 2
def baseEnd_7791388 : Nat := 4000727009673067392318065

theorem tailTrace_7791388 : CollatzResearch.WordTrace tailWord_7791388 prefixEnd_7791388 4000727009673067392318065 := by
  unfold tailWord_7791388
  simp only [CollatzResearch.WordTrace]
  refine ⟨142087633148569706988003409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189450177531426275984004545 142087633148569706988003409)
  ·
    refine ⟨106565724861427280241002557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142087633148569706988003409 106565724861427280241002557)
    ·
      refine ⟨39962146823035230090375959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106565724861427280241002557 39962146823035230090375959)
      ·
        refine ⟨59943220234552845135563939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39962146823035230090375959 59943220234552845135563939)
        ·
          refine ⟨89914830351829267703345909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59943220234552845135563939 89914830351829267703345909)
          ·
            refine ⟨8429515345483993847188679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89914830351829267703345909 8429515345483993847188679)
            ·
              refine ⟨12644273018225990770783019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8429515345483993847188679 12644273018225990770783019)
              ·
                refine ⟨18966409527338986156174529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12644273018225990770783019 18966409527338986156174529)
                ·
                  refine ⟨14224807145504239617130897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18966409527338986156174529 14224807145504239617130897)
                  ·
                    refine ⟨10668605359128179712848173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14224807145504239617130897 10668605359128179712848173)
                    ·
                      refine ⟨4000727009673067392318065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10668605359128179712848173 4000727009673067392318065)
                      ·
                        rfl

theorem cell23_7791388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_7791388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791388 prefixEnd_7791388 := by exact prefixLift 7791388
  have htrace : WordTrace (prefixWord ++ tailWord_7791388) baseStart_7791388 baseEnd_7791388 := by
    simpa [prefixWord, tailWord_7791388, baseEnd_7791388] using wordTrace_append hprefix tailTrace_7791388
  have hstable : (prefixWord ++ tailWord_7791388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791388).length < 2 ^ (prefixWord ++ tailWord_7791388).sum := by decide
  have hdescent : baseEnd_7791388 < baseStart_7791388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791424 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 4]
def baseStart_7791424 : Nat := 118140960795 + 7791424 * 2 ^ 59
def prefixEnd_7791424 : Nat := 4983230072969 + 3 ^ 40 * 7791424 * 2
def baseEnd_7791424 : Nat := 4000745494976629251467899

theorem tailTrace_7791424 : CollatzResearch.WordTrace tailWord_7791424 prefixEnd_7791424 4000745494976629251467899 := by
  unfold tailWord_7791424
  simp only [CollatzResearch.WordTrace]
  refine ⟨142088289662504496062158663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189451052883339328082878217 142088289662504496062158663)
  ·
    refine ⟨213132434493756744093237995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142088289662504496062158663 213132434493756744093237995)
    ·
      refine ⟨319698651740635116139856993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213132434493756744093237995 319698651740635116139856993)
      ·
        refine ⟨239773988805476337104892745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319698651740635116139856993 239773988805476337104892745)
        ·
          refine ⟨179830491604107252828669559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239773988805476337104892745 179830491604107252828669559)
          ·
            refine ⟨269745737406160879243004339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179830491604107252828669559 269745737406160879243004339)
            ·
              refine ⟨404618606109241318864506509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269745737406160879243004339 404618606109241318864506509)
              ·
                refine ⟨151731977290965494574189941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404618606109241318864506509 151731977290965494574189941)
                ·
                  refine ⟨14224872871028015116330307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151731977290965494574189941 14224872871028015116330307)
                  ·
                    refine ⟨21337309306542022674495461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14224872871028015116330307 21337309306542022674495461)
                    ·
                      refine ⟨4000745494976629251467899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21337309306542022674495461 4000745494976629251467899)
                      ·
                        rfl

theorem cell23_7791424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_7791424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791424 prefixEnd_7791424 := by exact prefixLift 7791424
  have htrace : WordTrace (prefixWord ++ tailWord_7791424) baseStart_7791424 baseEnd_7791424 := by
    simpa [prefixWord, tailWord_7791424, baseEnd_7791424] using wordTrace_append hprefix tailTrace_7791424
  have hstable : (prefixWord ++ tailWord_7791424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791424).length < 2 ^ (prefixWord ++ tailWord_7791424).sum := by decide
  have hdescent : baseEnd_7791424 < baseStart_7791424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791425 : List Nat := [1, 2, 5, 3, 1, 1, 3, 1, 6]
def baseStart_7791425 : Nat := 118140960795 + 7791425 * 2 ^ 59
def prefixEnd_7791425 : Nat := 4983230072969 + 3 ^ 40 * 7791425 * 2
def baseEnd_7791425 : Nat := 444527334273031527506155

theorem tailTrace_7791425 : CollatzResearch.WordTrace tailWord_7791425 prefixEnd_7791425 444527334273031527506155 := by
  unfold tailWord_7791425
  simp only [CollatzResearch.WordTrace]
  refine ⟨284176615798005369295103729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189451077198670246196735819 284176615798005369295103729)
  ·
    refine ⟨213132461848504026971327797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284176615798005369295103729 213132461848504026971327797)
    ·
      refine ⟨19981168298297252528561981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213132461848504026971327797 19981168298297252528561981)
      ·
        refine ⟨7492938111861469698210743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19981168298297252528561981 7492938111861469698210743)
        ·
          refine ⟨11239407167792204547316115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7492938111861469698210743 11239407167792204547316115)
          ·
            refine ⟨16859110751688306820974173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11239407167792204547316115 16859110751688306820974173)
            ·
              refine ⟨6322166531883115057865315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16859110751688306820974173 6322166531883115057865315)
              ·
                refine ⟨9483249797824672586797973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6322166531883115057865315 9483249797824672586797973)
                ·
                  refine ⟨444527334273031527506155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9483249797824672586797973 444527334273031527506155)
                  ·
                    rfl

theorem cell23_7791425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 6].length) (baseStart_7791425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791425 prefixEnd_7791425 := by exact prefixLift 7791425
  have htrace : WordTrace (prefixWord ++ tailWord_7791425) baseStart_7791425 baseEnd_7791425 := by
    simpa [prefixWord, tailWord_7791425, baseEnd_7791425] using wordTrace_append hprefix tailTrace_7791425
  have hstable : (prefixWord ++ tailWord_7791425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791425).length < 2 ^ (prefixWord ++ tailWord_7791425).sum := by decide
  have hdescent : baseEnd_7791425 < baseStart_7791425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791434 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 1, 6]
def baseStart_7791434 : Nat := 118140960795 + 7791434 * 2 ^ 59
def prefixEnd_7791434 : Nat := 4983230072969 + 3 ^ 40 * 7791434 * 2
def baseEnd_7791434 : Nat := 1333583543261058070780951

theorem tailTrace_7791434 : CollatzResearch.WordTrace tailWord_7791434 prefixEnd_7791434 1333583543261058070780951 := by
  unfold tailWord_7791434
  simp only [CollatzResearch.WordTrace]
  refine ⟨71044236013743190958045339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189451296036648509221454237 71044236013743190958045339)
  ·
    refine ⟨106566354020614786437068009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71044236013743190958045339 106566354020614786437068009)
    ·
      refine ⟨79924765515461089827801007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106566354020614786437068009 79924765515461089827801007)
      ·
        refine ⟨119887148273191634741701511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79924765515461089827801007 119887148273191634741701511)
        ·
          refine ⟨179830722409787452112552267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119887148273191634741701511 179830722409787452112552267)
          ·
            refine ⟨269746083614681178168828401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179830722409787452112552267 269746083614681178168828401)
            ·
              refine ⟨202309562711010883626621301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269746083614681178168828401 202309562711010883626621301)
              ·
                refine ⟨18966521504157270339995747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202309562711010883626621301 18966521504157270339995747)
                ·
                  refine ⟨28449782256235905509993621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18966521504157270339995747 28449782256235905509993621)
                  ·
                    refine ⟨1333583543261058070780951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28449782256235905509993621 1333583543261058070780951)
                    ·
                      rfl

theorem cell23_7791434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_7791434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791434 prefixEnd_7791434 := by exact prefixLift 7791434
  have htrace : WordTrace (prefixWord ++ tailWord_7791434) baseStart_7791434 baseEnd_7791434 := by
    simpa [prefixWord, tailWord_7791434, baseEnd_7791434] using wordTrace_append hprefix tailTrace_7791434
  have hstable : (prefixWord ++ tailWord_7791434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791434).length < 2 ^ (prefixWord ++ tailWord_7791434).sum := by decide
  have hdescent : baseEnd_7791434 < baseStart_7791434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791452 : List Nat := [2, 2, 4, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_7791452 : Nat := 118140960795 + 7791452 * 2 ^ 59
def prefixEnd_7791452 : Nat := 4983230072969 + 3 ^ 40 * 7791452 * 2
def baseEnd_7791452 : Nat := 4000759872434955141917771

theorem tailTrace_7791452 : CollatzResearch.WordTrace tailWord_7791452 prefixEnd_7791452 4000759872434955141917771 := by
  unfold tailWord_7791452
  simp only [CollatzResearch.WordTrace]
  refine ⟨142088800284453776453168305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189451733712605035270891073 142088800284453776453168305)
  ·
    refine ⟨106566600213340332339876229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142088800284453776453168305 106566600213340332339876229)
    ·
      refine ⟨19981237540001312313726793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106566600213340332339876229 19981237540001312313726793)
      ·
        refine ⟨14985928155000984235295095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19981237540001312313726793 14985928155000984235295095)
        ·
          refine ⟨22478892232501476352942643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14985928155000984235295095 22478892232501476352942643)
          ·
            refine ⟨33718338348752214529413965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22478892232501476352942643 33718338348752214529413965)
            ·
              refine ⟨12644376880782080448530237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33718338348752214529413965 12644376880782080448530237)
              ·
                refine ⟨4741641330293280168198839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12644376880782080448530237 4741641330293280168198839)
                ·
                  refine ⟨7112461995439920252298259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741641330293280168198839 7112461995439920252298259)
                  ·
                    refine ⟨10668692993159880378447389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7112461995439920252298259 10668692993159880378447389)
                    ·
                      refine ⟨4000759872434955141917771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10668692993159880378447389 4000759872434955141917771)
                      ·
                        rfl

theorem cell23_7791452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_7791452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791452 prefixEnd_7791452 := by exact prefixLift 7791452
  have htrace : WordTrace (prefixWord ++ tailWord_7791452) baseStart_7791452 baseEnd_7791452 := by
    simpa [prefixWord, tailWord_7791452, baseEnd_7791452] using wordTrace_append hprefix tailTrace_7791452
  have hstable : (prefixWord ++ tailWord_7791452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791452).length < 2 ^ (prefixWord ++ tailWord_7791452).sum := by decide
  have hdescent : baseEnd_7791452 < baseStart_7791452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791464 : List Nat := [2, 1, 4, 2, 1, 2, 11]
def baseStart_7791464 : Nat := 118140960795 + 7791464 * 2 ^ 59
def prefixEnd_7791464 : Nat := 4983230072969 + 3 ^ 40 * 7791464 * 2
def baseEnd_7791464 : Nat := 49392173261763075246515

theorem tailTrace_7791464 : CollatzResearch.WordTrace tailWord_7791464 prefixEnd_7791464 49392173261763075246515 := by
  unfold tailWord_7791464
  simp only [CollatzResearch.WordTrace]
  refine ⟨142089019122432039477886723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189452025496576052637182297 142089019122432039477886723)
  ·
    refine ⟨213133528683648059216830085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142089019122432039477886723 213133528683648059216830085)
    ·
      refine ⟨39962536628184011103155641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213133528683648059216830085 39962536628184011103155641)
      ·
        refine ⟨29971902471138008327366731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39962536628184011103155641 29971902471138008327366731)
        ·
          refine ⟨44957853706707012491050097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29971902471138008327366731 44957853706707012491050097)
          ·
            refine ⟨33718390280030259368287573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44957853706707012491050097 33718390280030259368287573)
            ·
              refine ⟨49392173261763075246515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33718390280030259368287573 49392173261763075246515)
              ·
                rfl

theorem cell23_7791464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 11].length) (baseStart_7791464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791464 prefixEnd_7791464 := by exact prefixLift 7791464
  have htrace : WordTrace (prefixWord ++ tailWord_7791464) baseStart_7791464 baseEnd_7791464 := by
    simpa [prefixWord, tailWord_7791464, baseEnd_7791464] using wordTrace_append hprefix tailTrace_7791464
  have hstable : (prefixWord ++ tailWord_7791464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791464).length < 2 ^ (prefixWord ++ tailWord_7791464).sum := by decide
  have hdescent : baseEnd_7791464 < baseStart_7791464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791475 : List Nat := [1, 1, 1, 2, 2, 1, 4, 6, 1, 2, 2]
def baseStart_7791475 : Nat := 118140960795 + 7791475 * 2 ^ 59
def prefixEnd_7791475 : Nat := 4983230072969 + 3 ^ 40 * 7791475 * 2
def baseEnd_7791475 : Nat := 4000771682490008551930165

theorem tailTrace_7791475 : CollatzResearch.WordTrace tailWord_7791475 prefixEnd_7791475 4000771682490008551930165 := by
  unfold tailWord_7791475
  simp only [CollatzResearch.WordTrace]
  refine ⟨284178439447824227834423879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189452292965216151889615919 284178439447824227834423879)
  ·
    refine ⟨426267659171736341751635819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284178439447824227834423879 426267659171736341751635819)
    ·
      refine ⟨639401488757604512627453729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426267659171736341751635819 639401488757604512627453729)
      ·
        refine ⟨479551116568203384470590297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639401488757604512627453729 479551116568203384470590297)
        ·
          refine ⟨359663337426152538352942723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479551116568203384470590297 359663337426152538352942723)
          ·
            refine ⟨539495006139228807529414085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359663337426152538352942723 539495006139228807529414085)
            ·
              refine ⟨101155313651105401411765141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 539495006139228807529414085 101155313651105401411765141)
              ·
                refine ⟨4741655327395565691176491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101155313651105401411765141 4741655327395565691176491)
                ·
                  refine ⟨7112482991093348536764737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741655327395565691176491 7112482991093348536764737)
                  ·
                    refine ⟨5334362243320011402573553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7112482991093348536764737 5334362243320011402573553)
                    ·
                      refine ⟨4000771682490008551930165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5334362243320011402573553 4000771682490008551930165)
                      ·
                        rfl

theorem cell23_7791475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 1, 2, 2].length) (baseStart_7791475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791475 prefixEnd_7791475 := by exact prefixLift 7791475
  have htrace : WordTrace (prefixWord ++ tailWord_7791475) baseStart_7791475 baseEnd_7791475 := by
    simpa [prefixWord, tailWord_7791475, baseEnd_7791475] using wordTrace_append hprefix tailTrace_7791475
  have hstable : (prefixWord ++ tailWord_7791475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791475).length < 2 ^ (prefixWord ++ tailWord_7791475).sum := by decide
  have hdescent : baseEnd_7791475 < baseStart_7791475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791478 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_7791478 : Nat := 118140960795 + 7791478 * 2 ^ 59
def prefixEnd_7791478 : Nat := 4983230072969 + 3 ^ 40 * 7791478 * 2
def baseEnd_7791478 : Nat := 4000773222931972040192651

theorem tailTrace_7791478 : CollatzResearch.WordTrace tailWord_7791478 prefixEnd_7791478 4000773222931972040192651 := by
  unfold tailWord_7791478
  simp only [CollatzResearch.WordTrace]
  refine ⟨17761159304175834959173943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189452365911208906231188725 17761159304175834959173943)
  ·
    refine ⟨26641738956263752438760915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17761159304175834959173943 26641738956263752438760915)
    ·
      refine ⟨39962608434395628658141373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26641738956263752438760915 39962608434395628658141373)
      ·
        refine ⟨14985978162898360746803015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39962608434395628658141373 14985978162898360746803015)
        ·
          refine ⟨22478967244347541120204523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14985978162898360746803015 22478967244347541120204523)
          ·
            refine ⟨33718450866521311680306785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22478967244347541120204523 33718450866521311680306785)
            ·
              refine ⟨25288838149890983760230089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33718450866521311680306785 25288838149890983760230089)
              ·
                refine ⟨18966628612418237820172567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25288838149890983760230089 18966628612418237820172567)
                ·
                  refine ⟨28449942918627356730258851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18966628612418237820172567 28449942918627356730258851)
                  ·
                    refine ⟨42674914377941035095388277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28449942918627356730258851 42674914377941035095388277)
                    ·
                      refine ⟨4000773222931972040192651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42674914377941035095388277 4000773222931972040192651)
                      ·
                        rfl

theorem cell23_7791478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_7791478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791478 prefixEnd_7791478 := by exact prefixLift 7791478
  have htrace : WordTrace (prefixWord ++ tailWord_7791478) baseStart_7791478 baseEnd_7791478 := by
    simpa [prefixWord, tailWord_7791478, baseEnd_7791478] using wordTrace_append hprefix tailTrace_7791478
  have hstable : (prefixWord ++ tailWord_7791478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791478).length < 2 ^ (prefixWord ++ tailWord_7791478).sum := by decide
  have hdescent : baseEnd_7791478 < baseStart_7791478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791491 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 3]
def baseStart_7791491 : Nat := 118140960795 + 7791491 * 2 ^ 59
def prefixEnd_7791491 : Nat := 4983230072969 + 3 ^ 40 * 7791491 * 2
def baseEnd_7791491 : Nat := 4000779898180480489330091

theorem tailTrace_7791491 : CollatzResearch.WordTrace tailWord_7791491 prefixEnd_7791491 4000779898180480489330091 := by
  unfold tailWord_7791491
  simp only [CollatzResearch.WordTrace]
  refine ⟨284179023015766262567006327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189452682010510841711337551 284179023015766262567006327)
  ·
    refine ⟨426268534523649393850509491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284179023015766262567006327 426268534523649393850509491)
    ·
      refine ⟨639402801785474090775764237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426268534523649393850509491 639402801785474090775764237)
      ·
        refine ⟨239776050669552784040911589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639402801785474090775764237 239776050669552784040911589)
        ·
          refine ⟨44958009500541147007670923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239776050669552784040911589 44958009500541147007670923)
          ·
            refine ⟨67437014250811720511506385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44958009500541147007670923 67437014250811720511506385)
            ·
              refine ⟨50577760688108790383629789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67437014250811720511506385 50577760688108790383629789)
              ·
                refine ⟨18966660258040796393861171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50577760688108790383629789 18966660258040796393861171)
                ·
                  refine ⟨28449990387061194590791757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18966660258040796393861171 28449990387061194590791757)
                  ·
                    refine ⟨10668746395147947971546909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28449990387061194590791757 10668746395147947971546909)
                    ·
                      refine ⟨4000779898180480489330091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10668746395147947971546909 4000779898180480489330091)
                      ·
                        rfl

theorem cell23_7791491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_7791491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791491 prefixEnd_7791491 := by exact prefixLift 7791491
  have htrace : WordTrace (prefixWord ++ tailWord_7791491) baseStart_7791491 baseEnd_7791491 := by
    simpa [prefixWord, tailWord_7791491, baseEnd_7791491] using wordTrace_append hprefix tailTrace_7791491
  have hstable : (prefixWord ++ tailWord_7791491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791491).length < 2 ^ (prefixWord ++ tailWord_7791491).sum := by decide
  have hdescent : baseEnd_7791491 < baseStart_7791491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791495 : List Nat := [1, 1, 4, 2, 3, 3, 1, 2, 1, 2, 3]
def baseStart_7791495 : Nat := 118140960795 + 7791495 * 2 ^ 59
def prefixEnd_7791495 : Nat := 4983230072969 + 3 ^ 40 * 7791495 * 2
def baseEnd_7791495 : Nat := 4000781952103098473680073

theorem tailTrace_7791495 : CollatzResearch.WordTrace tailWord_7791495 prefixEnd_7791495 4000781952103098473680073 := by
  unfold tailWord_7791495
  simp only [CollatzResearch.WordTrace]
  refine ⟨284179168907751771250151939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189452779271834514166767959 284179168907751771250151939)
  ·
    refine ⟨426268753361627656875227909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284179168907751771250151939 426268753361627656875227909)
    ·
      refine ⟨79925391255305185664105233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 426268753361627656875227909 79925391255305185664105233)
      ·
        refine ⟨59944043441478889248078925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79925391255305185664105233 59944043441478889248078925)
        ·
          refine ⟨22479016290554583468029597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59944043441478889248078925 22479016290554583468029597)
          ·
            refine ⟨8429631108957968800511099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22479016290554583468029597 8429631108957968800511099)
            ·
              refine ⟨12644446663436953200766649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8429631108957968800511099 12644446663436953200766649)
              ·
                refine ⟨9483334997577714900574987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12644446663436953200766649 9483334997577714900574987)
                ·
                  refine ⟨14225002496366572350862481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9483334997577714900574987 14225002496366572350862481)
                  ·
                    refine ⟨10668751872274929263146861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14225002496366572350862481 10668751872274929263146861)
                    ·
                      refine ⟨4000781952103098473680073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10668751872274929263146861 4000781952103098473680073)
                      ·
                        rfl

theorem cell23_7791495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_7791495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791495 prefixEnd_7791495 := by exact prefixLift 7791495
  have htrace : WordTrace (prefixWord ++ tailWord_7791495) baseStart_7791495 baseEnd_7791495 := by
    simpa [prefixWord, tailWord_7791495, baseEnd_7791495] using wordTrace_append hprefix tailTrace_7791495
  have hstable : (prefixWord ++ tailWord_7791495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791495).length < 2 ^ (prefixWord ++ tailWord_7791495).sum := by decide
  have hdescent : baseEnd_7791495 < baseStart_7791495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791508 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_7791508 : Nat := 118140960795 + 7791508 * 2 ^ 59
def prefixEnd_7791508 : Nat := 4983230072969 + 3 ^ 40 * 7791508 * 2
def baseEnd_7791508 : Nat := 4000788627351606922817513

theorem tailTrace_7791508 : CollatzResearch.WordTrace tailWord_7791508 prefixEnd_7791508 4000788627351606922817513 := by
  unfold tailWord_7791508
  simp only [CollatzResearch.WordTrace]
  refine ⟨142089821528352337235187589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189453095371136449646916785 142089821528352337235187589)
  ·
    refine ⟨26641841536566063231597673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142089821528352337235187589 26641841536566063231597673)
    ·
      refine ⟨19981381152424547423698255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26641841536566063231597673 19981381152424547423698255)
      ·
        refine ⟨29972071728636821135547383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19981381152424547423698255 29972071728636821135547383)
        ·
          refine ⟨44958107592955231703321075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29972071728636821135547383 44958107592955231703321075)
          ·
            refine ⟨67437161389432847554981613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44958107592955231703321075 67437161389432847554981613)
            ·
              refine ⟨25288935521037317833118105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67437161389432847554981613 25288935521037317833118105)
              ·
                refine ⟨18966701640777988374838579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25288935521037317833118105 18966701640777988374838579)
                ·
                  refine ⟨28450052461166982562257869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18966701640777988374838579 28450052461166982562257869)
                  ·
                    refine ⟨10668769672937618460846701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28450052461166982562257869 10668769672937618460846701)
                    ·
                      refine ⟨4000788627351606922817513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10668769672937618460846701 4000788627351606922817513)
                      ·
                        rfl

theorem cell23_7791508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_7791508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791508 prefixEnd_7791508 := by exact prefixLift 7791508
  have htrace : WordTrace (prefixWord ++ tailWord_7791508) baseStart_7791508 baseEnd_7791508 := by
    simpa [prefixWord, tailWord_7791508, baseEnd_7791508] using wordTrace_append hprefix tailTrace_7791508
  have hstable : (prefixWord ++ tailWord_7791508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791508).length < 2 ^ (prefixWord ++ tailWord_7791508).sum := by decide
  have hdescent : baseEnd_7791508 < baseStart_7791508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791541 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 2, 6]
def baseStart_7791541 : Nat := 118140960795 + 7791541 * 2 ^ 59
def prefixEnd_7791541 : Nat := 4983230072969 + 3 ^ 40 * 7791541 * 2
def baseEnd_7791541 : Nat := 1333601857404401764568287

theorem tailTrace_7791541 : CollatzResearch.WordTrace tailWord_7791541 prefixEnd_7791541 1333601857404401764568287 := by
  unfold tailWord_7791541
  simp only [CollatzResearch.WordTrace]
  refine ⟨284180846665585121106326477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189453897777056747404217651 284180846665585121106326477)
  ·
    refine ⟨106567817499594420414872429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284180846665585121106326477 106567817499594420414872429)
    ·
      refine ⟨39962931562347907655577161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106567817499594420414872429 39962931562347907655577161)
      ·
        refine ⟨29972198671760930741682871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39962931562347907655577161 29972198671760930741682871)
        ·
          refine ⟨44958298007641396112524307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29972198671760930741682871 44958298007641396112524307)
          ·
            refine ⟨67437447011462094168786461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44958298007641396112524307 67437447011462094168786461)
            ·
              refine ⟨25289042629298285313294923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67437447011462094168786461 25289042629298285313294923)
              ·
                refine ⟨37933563943947427969942385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25289042629298285313294923 37933563943947427969942385)
                ·
                  refine ⟨28450172957960570977456789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37933563943947427969942385 28450172957960570977456789)
                  ·
                    refine ⟨1333601857404401764568287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28450172957960570977456789 1333601857404401764568287)
                    ·
                      rfl

theorem cell23_7791541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_7791541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791541 prefixEnd_7791541 := by exact prefixLift 7791541
  have htrace : WordTrace (prefixWord ++ tailWord_7791541) baseStart_7791541 baseEnd_7791541 := by
    simpa [prefixWord, tailWord_7791541, baseEnd_7791541] using wordTrace_append hprefix tailTrace_7791541
  have hstable : (prefixWord ++ tailWord_7791541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791541).length < 2 ^ (prefixWord ++ tailWord_7791541).sum := by decide
  have hdescent : baseEnd_7791541 < baseStart_7791541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791601 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 1, 7]
def baseStart_7791601 : Nat := 118140960795 + 7791601 * 2 ^ 59
def prefixEnd_7791601 : Nat := 4983230072969 + 3 ^ 40 * 7791601 * 2
def baseEnd_7791601 : Nat := 1333612127017491686318195

theorem tailTrace_7791601 : CollatzResearch.WordTrace tailWord_7791601 prefixEnd_7791601 1333612127017491686318195 := by
  unfold tailWord_7791601
  simp only [CollatzResearch.WordTrace]
  refine ⟨284183035045367751353510657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189455356696911834235673771 284183035045367751353510657)
  ·
    refine ⟨213137276284025813515132993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284183035045367751353510657 213137276284025813515132993)
    ·
      refine ⟨159852957213019360136349745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213137276284025813515132993 159852957213019360136349745)
      ·
        refine ⟨119889717909764520102262309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159852957213019360136349745 119889717909764520102262309)
        ·
          refine ⟨22479322108080847519174183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119889717909764520102262309 22479322108080847519174183)
          ·
            refine ⟨33718983162121271278761275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22479322108080847519174183 33718983162121271278761275)
            ·
              refine ⟨50578474743181906918141913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33718983162121271278761275 50578474743181906918141913)
              ·
                refine ⟨37933856057386430188606435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50578474743181906918141913 37933856057386430188606435)
                ·
                  refine ⟨56900784086079645282909653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37933856057386430188606435 56900784086079645282909653)
                  ·
                    refine ⟨1333612127017491686318195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56900784086079645282909653 1333612127017491686318195)
                    ·
                      rfl

theorem cell23_7791601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_7791601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791601 prefixEnd_7791601 := by exact prefixLift 7791601
  have htrace : WordTrace (prefixWord ++ tailWord_7791601) baseStart_7791601 baseEnd_7791601 := by
    simpa [prefixWord, tailWord_7791601, baseEnd_7791601] using wordTrace_append hprefix tailTrace_7791601
  have hstable : (prefixWord ++ tailWord_7791601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791601).length < 2 ^ (prefixWord ++ tailWord_7791601).sum := by decide
  have hdescent : baseEnd_7791601 < baseStart_7791601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791621 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_7791621 : Nat := 118140960795 + 7791621 * 2 ^ 59
def prefixEnd_7791621 : Nat := 4983230072969 + 3 ^ 40 * 7791621 * 2
def baseEnd_7791621 : Nat := 4000846650665564980704493

theorem tailTrace_7791621 : CollatzResearch.WordTrace tailWord_7791621 prefixEnd_7791621 4000846650665564980704493 := by
  unfold tailWord_7791621
  simp only [CollatzResearch.WordTrace]
  refine ⟨284183764505295294769238717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189455843003530196512825811 284183764505295294769238717)
  ·
    refine ⟨106568911689485735538464519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284183764505295294769238717 106568911689485735538464519)
    ·
      refine ⟨159853367534228603307696779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106568911689485735538464519 159853367534228603307696779)
      ·
        refine ⟨239780051301342904961545169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159853367534228603307696779 239780051301342904961545169)
        ·
          refine ⟨179835038476007178721158877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239780051301342904961545169 179835038476007178721158877)
          ·
            refine ⟨67438139428502692020434579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179835038476007178721158877 67438139428502692020434579)
            ·
              refine ⟨101157209142754038030651869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67438139428502692020434579 101157209142754038030651869)
              ·
                refine ⟨37933953428532764261494451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101157209142754038030651869 37933953428532764261494451)
                ·
                  refine ⟨56900930142799146392241677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37933953428532764261494451 56900930142799146392241677)
                  ·
                    refine ⟨21337848803549679897090629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56900930142799146392241677 21337848803549679897090629)
                    ·
                      refine ⟨4000846650665564980704493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21337848803549679897090629 4000846650665564980704493)
                      ·
                        rfl

theorem cell23_7791621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_7791621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791621 prefixEnd_7791621 := by exact prefixLift 7791621
  have htrace : WordTrace (prefixWord ++ tailWord_7791621) baseStart_7791621 baseEnd_7791621 := by
    simpa [prefixWord, tailWord_7791621, baseEnd_7791621] using wordTrace_append hprefix tailTrace_7791621
  have hstable : (prefixWord ++ tailWord_7791621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791621).length < 2 ^ (prefixWord ++ tailWord_7791621).sum := by decide
  have hdescent : baseEnd_7791621 < baseStart_7791621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791691 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 7, 5]
def baseStart_7791691 : Nat := 118140960795 + 7791691 * 2 ^ 59
def prefixEnd_7791691 : Nat := 4983230072969 + 3 ^ 40 * 7791691 * 2
def baseEnd_7791691 : Nat := 1333627531437126568943057

theorem tailTrace_7791691 : CollatzResearch.WordTrace tailWord_7791691 prefixEnd_7791691 1333627531437126568943057 := by
  unfold tailWord_7791691
  simp only [CollatzResearch.WordTrace]
  refine ⟨284186317615041696724286927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189457545076694464482857951 284186317615041696724286927)
  ·
    refine ⟨426279476422562545086430391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284186317615041696724286927 426279476422562545086430391)
    ·
      refine ⟨639419214633843817629645587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426279476422562545086430391 639419214633843817629645587)
      ·
        refine ⟨959128821950765726444468381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639419214633843817629645587 959128821950765726444468381)
        ·
          refine ⟨359673308231537147416675643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 959128821950765726444468381 359673308231537147416675643)
          ·
            refine ⟨539509962347305721125013465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359673308231537147416675643 539509962347305721125013465)
            ·
              refine ⟨404632471760479290843760099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539509962347305721125013465 404632471760479290843760099)
              ·
                refine ⟨606948707640718936265640149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404632471760479290843760099 606948707640718936265640149)
                ·
                  refine ⟨14225360335329350068725941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 606948707640718936265640149 14225360335329350068725941)
                  ·
                    refine ⟨1333627531437126568943057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14225360335329350068725941 1333627531437126568943057)
                    ·
                      rfl

theorem cell23_7791691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 5].length) (baseStart_7791691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791691 prefixEnd_7791691 := by exact prefixLift 7791691
  have htrace : WordTrace (prefixWord ++ tailWord_7791691) baseStart_7791691 baseEnd_7791691 := by
    simpa [prefixWord, tailWord_7791691, baseEnd_7791691] using wordTrace_append hprefix tailTrace_7791691
  have hstable : (prefixWord ++ tailWord_7791691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791691).length < 2 ^ (prefixWord ++ tailWord_7791691).sum := by decide
  have hdescent : baseEnd_7791691 < baseStart_7791691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791708 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 5, 5]
def baseStart_7791708 : Nat := 118140960795 + 7791708 * 2 ^ 59
def prefixEnd_7791708 : Nat := 4983230072969 + 3 ^ 40 * 7791708 * 2
def baseEnd_7791708 : Nat := 1333630441160835380105531

theorem tailTrace_7791708 : CollatzResearch.WordTrace tailWord_7791708 prefixEnd_7791708 1333630441160835380105531 := by
  unfold tailWord_7791708
  simp only [CollatzResearch.WordTrace]
  refine ⟨142093468827990054313827889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189457958437320072418437185 142093468827990054313827889)
  ·
    refine ⟨106570101620992540735370917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142093468827990054313827889 106570101620992540735370917)
    ·
      refine ⟨19981894053936101387882047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106570101620992540735370917 19981894053936101387882047)
      ·
        refine ⟨29972841080904152081823071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19981894053936101387882047 29972841080904152081823071)
        ·
          refine ⟨44959261621356228122734607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29972841080904152081823071 44959261621356228122734607)
          ·
            refine ⟨67438892432034342184101911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44959261621356228122734607 67438892432034342184101911)
            ·
              refine ⟨101158338648051513276152867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67438892432034342184101911 101158338648051513276152867)
              ·
                refine ⟨151737507972077269914229301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101158338648051513276152867 151737507972077269914229301)
                ·
                  refine ⟨14225391372382244054458997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151737507972077269914229301 14225391372382244054458997)
                  ·
                    refine ⟨1333630441160835380105531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14225391372382244054458997 1333630441160835380105531)
                    ·
                      rfl

theorem cell23_7791708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_7791708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791708 prefixEnd_7791708 := by exact prefixLift 7791708
  have htrace : WordTrace (prefixWord ++ tailWord_7791708) baseStart_7791708 baseEnd_7791708 := by
    simpa [prefixWord, tailWord_7791708, baseEnd_7791708] using wordTrace_append hprefix tailTrace_7791708
  have hstable : (prefixWord ++ tailWord_7791708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791708).length < 2 ^ (prefixWord ++ tailWord_7791708).sum := by decide
  have hdescent : baseEnd_7791708 < baseStart_7791708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791722 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_7791722 : Nat := 118140960795 + 7791722 * 2 ^ 59
def prefixEnd_7791722 : Nat := 4983230072969 + 3 ^ 40 * 7791722 * 2
def baseEnd_7791722 : Nat := 4000898512211669085541529

theorem tailTrace_7791722 : CollatzResearch.WordTrace tailWord_7791722 prefixEnd_7791722 4000898512211669085541529 := by
  unfold tailWord_7791722
  simp only [CollatzResearch.WordTrace]
  refine ⟨71046862069482347254666355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189458298851952926012443613 71046862069482347254666355)
  ·
    refine ⟨106570293104223520881999533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71046862069482347254666355 106570293104223520881999533)
    ·
      refine ⟨39963859914083820330749825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106570293104223520881999533 39963859914083820330749825)
      ·
        refine ⟨29972894935562865248062369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39963859914083820330749825 29972894935562865248062369)
        ·
          refine ⟨22479671201672148936046777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29972894935562865248062369 22479671201672148936046777)
          ·
            refine ⟨16859753401254111702035083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22479671201672148936046777 16859753401254111702035083)
            ·
              refine ⟨25289630101881167553052625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16859753401254111702035083 25289630101881167553052625)
              ·
                refine ⟨18967222576410875664789469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25289630101881167553052625 18967222576410875664789469)
                ·
                  refine ⟨7112708466154078374296051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18967222576410875664789469 7112708466154078374296051)
                  ·
                    refine ⟨10669062699231117561444077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7112708466154078374296051 10669062699231117561444077)
                    ·
                      refine ⟨4000898512211669085541529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10669062699231117561444077 4000898512211669085541529)
                      ·
                        rfl

theorem cell23_7791722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_7791722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791722 prefixEnd_7791722 := by exact prefixLift 7791722
  have htrace : WordTrace (prefixWord ++ tailWord_7791722) baseStart_7791722 baseEnd_7791722 := by
    simpa [prefixWord, tailWord_7791722, baseEnd_7791722] using wordTrace_append hprefix tailTrace_7791722
  have hstable : (prefixWord ++ tailWord_7791722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791722).length < 2 ^ (prefixWord ++ tailWord_7791722).sum := by decide
  have hdescent : baseEnd_7791722 < baseStart_7791722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791728 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 4]
def baseStart_7791728 : Nat := 118140960795 + 7791728 * 2 ^ 59
def prefixEnd_7791728 : Nat := 4983230072969 + 3 ^ 40 * 7791728 * 2
def baseEnd_7791728 : Nat := 4000901593095596062066501

theorem tailTrace_7791728 : CollatzResearch.WordTrace tailWord_7791728 prefixEnd_7791728 4000901593095596062066501 := by
  unfold tailWord_7791728
  simp only [CollatzResearch.WordTrace]
  refine ⟨142093833557953826021691919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189458444743938434695589225 142093833557953826021691919)
  ·
    refine ⟨213140750336930739032537879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142093833557953826021691919 213140750336930739032537879)
    ·
      refine ⟨319711125505396108548806819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213140750336930739032537879 319711125505396108548806819)
      ·
        refine ⟨479566688258094162823210229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319711125505396108548806819 479566688258094162823210229)
        ·
          refine ⟨44959377024196327764675959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 479566688258094162823210229 44959377024196327764675959)
          ·
            refine ⟨67439065536294491647013939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44959377024196327764675959 67439065536294491647013939)
            ·
              refine ⟨101158598304441737470520909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67439065536294491647013939 101158598304441737470520909)
              ·
                refine ⟨37934474364165651551445341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101158598304441737470520909 37934474364165651551445341)
                ·
                  refine ⟨14225427886562119331792003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37934474364165651551445341 14225427886562119331792003)
                  ·
                    refine ⟨21338141829843178997688005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14225427886562119331792003 21338141829843178997688005)
                    ·
                      refine ⟨4000901593095596062066501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21338141829843178997688005 4000901593095596062066501)
                      ·
                        rfl

theorem cell23_7791728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_7791728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791728 prefixEnd_7791728 := by exact prefixLift 7791728
  have htrace : WordTrace (prefixWord ++ tailWord_7791728) baseStart_7791728 baseEnd_7791728 := by
    simpa [prefixWord, tailWord_7791728, baseEnd_7791728] using wordTrace_append hprefix tailTrace_7791728
  have hstable : (prefixWord ++ tailWord_7791728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791728).length < 2 ^ (prefixWord ++ tailWord_7791728).sum := by decide
  have hdescent : baseEnd_7791728 < baseStart_7791728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791775 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 6]
def baseStart_7791775 : Nat := 118140960795 + 7791775 * 2 ^ 59
def prefixEnd_7791775 : Nat := 4983230072969 + 3 ^ 40 * 7791775 * 2
def baseEnd_7791775 : Nat := 4000925726686357378178785

theorem tailTrace_7791775 : CollatzResearch.WordTrace tailWord_7791775 prefixEnd_7791775 4000925726686357378178785 := by
  unfold tailWord_7791775
  simp only [CollatzResearch.WordTrace]
  refine ⟨284189381346737379070344779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189459587564491586046896519 284189381346737379070344779)
  ·
    refine ⟨426284072020106068605517169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284189381346737379070344779 426284072020106068605517169)
    ·
      refine ⟨319713054015079551454137877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426284072020106068605517169 319713054015079551454137877)
      ·
        refine ⟨14986549406956853974412713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 319713054015079551454137877 14986549406956853974412713)
        ·
          refine ⟨11239912055217640480809535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14986549406956853974412713 11239912055217640480809535)
          ·
            refine ⟨16859868082826460721214303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11239912055217640480809535 16859868082826460721214303)
            ·
              refine ⟨25289802124239691081821455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16859868082826460721214303 25289802124239691081821455)
              ·
                refine ⟨37934703186359536622732183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25289802124239691081821455 37934703186359536622732183)
                ·
                  refine ⟨56902054779539304934098275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37934703186359536622732183 56902054779539304934098275)
                  ·
                    refine ⟨85353082169308957401147413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56902054779539304934098275 85353082169308957401147413)
                    ·
                      refine ⟨4000925726686357378178785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85353082169308957401147413 4000925726686357378178785)
                      ·
                        rfl

theorem cell23_7791775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_7791775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791775 prefixEnd_7791775 := by exact prefixLift 7791775
  have htrace : WordTrace (prefixWord ++ tailWord_7791775) baseStart_7791775 baseEnd_7791775 := by
    simpa [prefixWord, tailWord_7791775, baseEnd_7791775] using wordTrace_append hprefix tailTrace_7791775
  have hstable : (prefixWord ++ tailWord_7791775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791775).length < 2 ^ (prefixWord ++ tailWord_7791775).sum := by decide
  have hdescent : baseEnd_7791775 < baseStart_7791775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791795 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 4, 1, 3]
def baseStart_7791795 : Nat := 118140960795 + 7791795 * 2 ^ 59
def prefixEnd_7791795 : Nat := 4983230072969 + 3 ^ 40 * 7791795 * 2
def baseEnd_7791795 : Nat := 4000935996299447299928693

theorem tailTrace_7791795 : CollatzResearch.WordTrace tailWord_7791795 prefixEnd_7791795 4000935996299447299928693 := by
  unfold tailWord_7791795
  simp only [CollatzResearch.WordTrace]
  refine ⟨284190110806664922486072839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189460073871109948324048559 284190110806664922486072839)
  ·
    refine ⟨426285166209997383729109259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284190110806664922486072839 426285166209997383729109259)
    ·
      refine ⟨639427749314996075593663889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426285166209997383729109259 639427749314996075593663889)
      ·
        refine ⟨479570811986247056695247917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639427749314996075593663889 479570811986247056695247917)
        ·
          refine ⟨179839054494842646260717969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479570811986247056695247917 179839054494842646260717969)
          ·
            refine ⟨134879290871131984695538477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179839054494842646260717969 134879290871131984695538477)
            ·
              refine ⟨50579734076674494260826929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134879290871131984695538477 50579734076674494260826929)
              ·
                refine ⟨37934800557505870695620197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50579734076674494260826929 37934800557505870695620197)
                ·
                  refine ⟨7112775104532350755428787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37934800557505870695620197 7112775104532350755428787)
                  ·
                    refine ⟨10669162656798526133143181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7112775104532350755428787 10669162656798526133143181)
                    ·
                      refine ⟨4000935996299447299928693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10669162656798526133143181 4000935996299447299928693)
                      ·
                        rfl

theorem cell23_7791795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 1, 3].length) (baseStart_7791795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791795 prefixEnd_7791795 := by exact prefixLift 7791795
  have htrace : WordTrace (prefixWord ++ tailWord_7791795) baseStart_7791795 baseEnd_7791795 := by
    simpa [prefixWord, tailWord_7791795, baseEnd_7791795] using wordTrace_append hprefix tailTrace_7791795
  have hstable : (prefixWord ++ tailWord_7791795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791795).length < 2 ^ (prefixWord ++ tailWord_7791795).sum := by decide
  have hdescent : baseEnd_7791795 < baseStart_7791795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791829 : List Nat := [1, 3, 2, 4, 1, 2, 1, 3, 2, 1, 3]
def baseStart_7791829 : Nat := 118140960795 + 7791829 * 2 ^ 59
def prefixEnd_7791829 : Nat := 4983230072969 + 3 ^ 40 * 7791829 * 2
def baseEnd_7791829 : Nat := 4000953454641700166903537

theorem tailTrace_7791829 : CollatzResearch.WordTrace tailWord_7791829 prefixEnd_7791829 4000953454641700166903537 := by
  unfold tailWord_7791829
  simp only [CollatzResearch.WordTrace]
  refine ⟨284191350888541746292810541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189460900592361164195207027 284191350888541746292810541)
  ·
    refine ⟨106571756583203154859803953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284191350888541746292810541 106571756583203154859803953)
    ·
      refine ⟨79928817437402366144852965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106571756583203154859803953 79928817437402366144852965)
      ·
        refine ⟨14986653269512943652159931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79928817437402366144852965 14986653269512943652159931)
        ·
          refine ⟨22479979904269415478239897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14986653269512943652159931 22479979904269415478239897)
          ·
            refine ⟨16859984928202061608679923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22479979904269415478239897 16859984928202061608679923)
            ·
              refine ⟨25289977392303092413019885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16859984928202061608679923 25289977392303092413019885)
              ·
                refine ⟨9483741522113659654882457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25289977392303092413019885 9483741522113659654882457)
                ·
                  refine ⟨7112806141585244741161843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9483741522113659654882457 7112806141585244741161843)
                  ·
                    refine ⟨10669209212377867111742765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7112806141585244741161843 10669209212377867111742765)
                    ·
                      refine ⟨4000953454641700166903537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10669209212377867111742765 4000953454641700166903537)
                      ·
                        rfl

theorem cell23_7791829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_7791829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791829 prefixEnd_7791829 := by exact prefixLift 7791829
  have htrace : WordTrace (prefixWord ++ tailWord_7791829) baseStart_7791829 baseEnd_7791829 := by
    simpa [prefixWord, tailWord_7791829, baseEnd_7791829] using wordTrace_append hprefix tailTrace_7791829
  have hstable : (prefixWord ++ tailWord_7791829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791829).length < 2 ^ (prefixWord ++ tailWord_7791829).sum := by decide
  have hdescent : baseEnd_7791829 < baseStart_7791829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791852 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 1, 4, 2]
def baseStart_7791852 : Nat := 118140960795 + 7791852 * 2 ^ 59
def prefixEnd_7791852 : Nat := 4983230072969 + 3 ^ 40 * 7791852 * 2
def baseEnd_7791852 : Nat := 4000965264696753576915931

theorem tailTrace_7791852 : CollatzResearch.WordTrace tailWord_7791852 prefixEnd_7791852 4000965264696753576915931 := by
  unfold tailWord_7791852
  simp only [CollatzResearch.WordTrace]
  refine ⟨142096094883729210610448905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189461459844972280813931873 142096094883729210610448905)
  ·
    refine ⟨106572071162796907957836679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142096094883729210610448905 106572071162796907957836679)
    ·
      refine ⟨159858106744195361936755019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106572071162796907957836679 159858106744195361936755019)
      ·
        refine ⟨239787160116293042905132529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159858106744195361936755019 239787160116293042905132529)
        ·
          refine ⟨179840370087219782178849397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239787160116293042905132529 179840370087219782178849397)
          ·
            refine ⟨16860034695676854579267131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179840370087219782178849397 16860034695676854579267131)
            ·
              refine ⟨25290052043515281868900697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16860034695676854579267131 25290052043515281868900697)
              ·
                refine ⟨18967539032636461401675523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25290052043515281868900697 18967539032636461401675523)
                ·
                  refine ⟨28451308548954692102513285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18967539032636461401675523 28451308548954692102513285)
                  ·
                    refine ⟨5334620352929004769221241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28451308548954692102513285 5334620352929004769221241)
                    ·
                      refine ⟨4000965264696753576915931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5334620352929004769221241 4000965264696753576915931)
                      ·
                        rfl

theorem cell23_7791852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 4, 2].length) (baseStart_7791852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791852 prefixEnd_7791852 := by exact prefixLift 7791852
  have htrace : WordTrace (prefixWord ++ tailWord_7791852) baseStart_7791852 baseEnd_7791852 := by
    simpa [prefixWord, tailWord_7791852, baseEnd_7791852] using wordTrace_append hprefix tailTrace_7791852
  have hstable : (prefixWord ++ tailWord_7791852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791852).length < 2 ^ (prefixWord ++ tailWord_7791852).sum := by decide
  have hdescent : baseEnd_7791852 < baseStart_7791852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791945 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 1, 4, 3]
def baseStart_7791945 : Nat := 118140960795 + 7791945 * 2 ^ 59
def prefixEnd_7791945 : Nat := 4983230072969 + 3 ^ 40 * 7791945 * 2
def baseEnd_7791945 : Nat := 4001013018397621713053003

theorem tailTrace_7791945 : CollatzResearch.WordTrace tailWord_7791945 prefixEnd_7791945 4001013018397621713053003 := by
  unfold tailWord_7791945
  simp only [CollatzResearch.WordTrace]
  refine ⟨284195581756121498104033289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189463721170747665402688859 284195581756121498104033289)
  ·
    refine ⟨213146686317091123578024967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284195581756121498104033289 213146686317091123578024967)
    ·
      refine ⟨319720029475636685367037451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213146686317091123578024967 319720029475636685367037451)
      ·
        refine ⟨479580044213455028050556177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319720029475636685367037451 479580044213455028050556177)
        ·
          refine ⟨359685033160091271037917133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479580044213455028050556177 359685033160091271037917133)
          ·
            refine ⟨134881887435034226639218925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359685033160091271037917133 134881887435034226639218925)
            ·
              refine ⟨50580707788137834989707097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134881887435034226639218925 50580707788137834989707097)
              ·
                refine ⟨37935530841103376242280323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50580707788137834989707097 37935530841103376242280323)
                ·
                  refine ⟨56903296261655064363420485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37935530841103376242280323 56903296261655064363420485)
                  ·
                    refine ⟨10669368049060324568141341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56903296261655064363420485 10669368049060324568141341)
                    ·
                      refine ⟨4001013018397621713053003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10669368049060324568141341 4001013018397621713053003)
                      ·
                        rfl

theorem cell23_7791945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 4, 3].length) (baseStart_7791945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791945 prefixEnd_7791945 := by exact prefixLift 7791945
  have htrace : WordTrace (prefixWord ++ tailWord_7791945) baseStart_7791945 baseEnd_7791945 := by
    simpa [prefixWord, tailWord_7791945, baseEnd_7791945] using wordTrace_append hprefix tailTrace_7791945
  have hstable : (prefixWord ++ tailWord_7791945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791945).length < 2 ^ (prefixWord ++ tailWord_7791945).sum := by decide
  have hdescent : baseEnd_7791945 < baseStart_7791945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791986 : List Nat := [3, 2, 1, 2, 1, 2, 5, 2, 1, 4]
def baseStart_7791986 : Nat := 118140960795 + 7791986 * 2 ^ 59
def prefixEnd_7791986 : Nat := 4983230072969 + 3 ^ 40 * 7791986 * 2
def baseEnd_7791986 : Nat := 1333678023701485350880105

theorem tailTrace_7791986 : CollatzResearch.WordTrace tailWord_7791986 prefixEnd_7791986 1333678023701485350880105 := by
  unfold tailWord_7791986
  simp only [CollatzResearch.WordTrace]
  refine ⟨71049269287243240526568953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189464718099315308070850541 71049269287243240526568953)
  ·
    refine ⟨53286951965432430394926715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71049269287243240526568953 53286951965432430394926715)
    ·
      refine ⟨79930427948148645592390073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53286951965432430394926715 79930427948148645592390073)
      ·
        refine ⟨59947820961111484194292555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79930427948148645592390073 59947820961111484194292555)
        ·
          refine ⟨89921731441667226291438833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59947820961111484194292555 89921731441667226291438833)
          ·
            refine ⟨67441298581250419718579125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89921731441667226291438833 67441298581250419718579125)
            ·
              refine ⟨6322621741992226848616793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67441298581250419718579125 6322621741992226848616793)
              ·
                refine ⟨4741966306494170136462595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6322621741992226848616793 4741966306494170136462595)
                ·
                  refine ⟨7112949459741255204693893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741966306494170136462595 7112949459741255204693893)
                  ·
                    refine ⟨1333678023701485350880105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7112949459741255204693893 1333678023701485350880105)
                    ·
                      rfl

theorem cell23_7791986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_7791986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791986 prefixEnd_7791986 := by exact prefixLift 7791986
  have htrace : WordTrace (prefixWord ++ tailWord_7791986) baseStart_7791986 baseEnd_7791986 := by
    simpa [prefixWord, tailWord_7791986, baseEnd_7791986] using wordTrace_append hprefix tailTrace_7791986
  have hstable : (prefixWord ++ tailWord_7791986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791986).length < 2 ^ (prefixWord ++ tailWord_7791986).sum := by decide
  have hdescent : baseEnd_7791986 < baseStart_7791986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791995 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 3, 5]
def baseStart_7791995 : Nat := 118140960795 + 7791995 * 2 ^ 59
def prefixEnd_7791995 : Nat := 4983230072969 + 3 ^ 40 * 7791995 * 2
def baseEnd_7791995 : Nat := 1333679564143448839142591

theorem tailTrace_7791995 : CollatzResearch.WordTrace tailWord_7791995 prefixEnd_7791995 1333679564143448839142591 := by
  unfold tailWord_7791995
  simp only [CollatzResearch.WordTrace]
  refine ⟨284197405405940356643353439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189464936937293571095568959 284197405405940356643353439)
  ·
    refine ⟨426296108108910534965030159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284197405405940356643353439 426296108108910534965030159)
    ·
      refine ⟨639444162163365802447545239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426296108108910534965030159 639444162163365802447545239)
      ·
        refine ⟨959166243245048703671317859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639444162163365802447545239 959166243245048703671317859)
        ·
          refine ⟨1438749364867573055506976789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959166243245048703671317859 1438749364867573055506976789)
          ·
            refine ⟨67441376478167486976889537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1438749364867573055506976789 67441376478167486976889537)
            ·
              refine ⟨50581032358625615232667153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67441376478167486976889537 50581032358625615232667153)
              ·
                refine ⟨37935774268969211424500365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50581032358625615232667153 37935774268969211424500365)
                ·
                  refine ⟨14225915350863454284187637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37935774268969211424500365 14225915350863454284187637)
                  ·
                    refine ⟨1333679564143448839142591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14225915350863454284187637 1333679564143448839142591)
                    ·
                      rfl

theorem cell23_7791995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 5].length) (baseStart_7791995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7791995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7791995 prefixEnd_7791995 := by exact prefixLift 7791995
  have htrace : WordTrace (prefixWord ++ tailWord_7791995) baseStart_7791995 baseEnd_7791995 := by
    simpa [prefixWord, tailWord_7791995, baseEnd_7791995] using wordTrace_append hprefix tailTrace_7791995
  have hstable : (prefixWord ++ tailWord_7791995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791995).length < 2 ^ (prefixWord ++ tailWord_7791995).sum := by decide
  have hdescent : baseEnd_7791995 < baseStart_7791995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792025 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 3, 6]
def baseStart_7792025 : Nat := 118140960795 + 7792025 * 2 ^ 59
def prefixEnd_7792025 : Nat := 4983230072969 + 3 ^ 40 * 7792025 * 2
def baseEnd_7792025 : Nat := 1333684698949993800017545

theorem tailTrace_7792025 : CollatzResearch.WordTrace tailWord_7792025 prefixEnd_7792025 1333684698949993800017545 := by
  unfold tailWord_7792025
  simp only [CollatzResearch.WordTrace]
  refine ⟨284198499595831671766945529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189465666397221114511297019 284198499595831671766945529)
  ·
    refine ⟨213148874696873753825209147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284198499595831671766945529 213148874696873753825209147)
    ·
      refine ⟨319723312045310630737813721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213148874696873753825209147 319723312045310630737813721)
      ·
        refine ⟨239792484033982973053360291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319723312045310630737813721 239792484033982973053360291)
        ·
          refine ⟨359688726050974459580040437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239792484033982973053360291 359688726050974459580040437)
          ·
            refine ⟨33720818067278855585628791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 359688726050974459580040437 33720818067278855585628791)
            ·
              refine ⟨50581227100918283378443187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33720818067278855585628791 50581227100918283378443187)
              ·
                refine ⟨75871840651377425067664781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50581227100918283378443187 75871840651377425067664781)
                ·
                  refine ⟨28451940244266534400374293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75871840651377425067664781 28451940244266534400374293)
                  ·
                    refine ⟨1333684698949993800017545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28451940244266534400374293 1333684698949993800017545)
                    ·
                      rfl

theorem cell23_7792025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 6].length) (baseStart_7792025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792025 prefixEnd_7792025 := by exact prefixLift 7792025
  have htrace : WordTrace (prefixWord ++ tailWord_7792025) baseStart_7792025 baseEnd_7792025 := by
    simpa [prefixWord, tailWord_7792025, baseEnd_7792025] using wordTrace_append hprefix tailTrace_7792025
  have hstable : (prefixWord ++ tailWord_7792025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792025).length < 2 ^ (prefixWord ++ tailWord_7792025).sum := by decide
  have hdescent : baseEnd_7792025 < baseStart_7792025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792026 : List Nat := [3, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3]
def baseStart_7792026 : Nat := 118140960795 + 7792026 * 2 ^ 59
def prefixEnd_7792026 : Nat := 4983230072969 + 3 ^ 40 * 7792026 * 2
def baseEnd_7792026 : Nat := 4001054610330635896140131

theorem tailTrace_7792026 : CollatzResearch.WordTrace tailWord_7792026 prefixEnd_7792026 4001054610330635896140131 := by
  unfold tailWord_7792026
  simp only [CollatzResearch.WordTrace]
  refine ⟨71049634017207012234432983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189465690712552032625154621 71049634017207012234432983)
  ·
    refine ⟨106574451025810518351649475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71049634017207012234432983 106574451025810518351649475)
    ·
      refine ⟨159861676538715777527474213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106574451025810518351649475 159861676538715777527474213)
      ·
        refine ⟨29974064351009208286401415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159861676538715777527474213 29974064351009208286401415)
        ·
          refine ⟨44961096526513812429602123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29974064351009208286401415 44961096526513812429602123)
          ·
            refine ⟨67441644789770718644403185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44961096526513812429602123 67441644789770718644403185)
            ·
              refine ⟨50581233592328038983302389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67441644789770718644403185 50581233592328038983302389)
              ·
                refine ⟨4741990649280753654684599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50581233592328038983302389 4741990649280753654684599)
                ·
                  refine ⟨7112985973921130482026899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741990649280753654684599 7112985973921130482026899)
                  ·
                    refine ⟨10669478960881695723040349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7112985973921130482026899 10669478960881695723040349)
                    ·
                      refine ⟨4001054610330635896140131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10669478960881695723040349 4001054610330635896140131)
                      ·
                        rfl

theorem cell23_7792026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_7792026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792026 prefixEnd_7792026 := by exact prefixLift 7792026
  have htrace : WordTrace (prefixWord ++ tailWord_7792026) baseStart_7792026 baseEnd_7792026 := by
    simpa [prefixWord, tailWord_7792026, baseEnd_7792026] using wordTrace_append hprefix tailTrace_7792026
  have hstable : (prefixWord ++ tailWord_7792026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792026).length < 2 ^ (prefixWord ++ tailWord_7792026).sum := by decide
  have hdescent : baseEnd_7792026 < baseStart_7792026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792072 : List Nat := [2, 1, 3, 1, 3, 1, 5, 7]
def baseStart_7792072 : Nat := 118140960795 + 7792072 * 2 ^ 59
def prefixEnd_7792072 : Nat := 4983230072969 + 3 ^ 40 * 7792072 * 2
def baseEnd_7792072 : Nat := 148188082608916396894997

theorem tailTrace_7792072 : CollatzResearch.WordTrace tailWord_7792072 prefixEnd_7792072 148188082608916396894997 := by
  unfold tailWord_7792072
  simp only [CollatzResearch.WordTrace]
  refine ⟨142100106913330699396953235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189466809217774265862604313 142100106913330699396953235)
  ·
    refine ⟨213150160369996049095429853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142100106913330699396953235 213150160369996049095429853)
    ·
      refine ⟨79931310138748518410786195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213150160369996049095429853 79931310138748518410786195)
      ·
        refine ⟨119896965208122777616179293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79931310138748518410786195 119896965208122777616179293)
        ·
          refine ⟨44961361953046041606067235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119896965208122777616179293 44961361953046041606067235)
          ·
            refine ⟨67442042929569062409100853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44961361953046041606067235 67442042929569062409100853)
            ·
              refine ⟨6322691524647099600853205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67442042929569062409100853 6322691524647099600853205)
              ·
                refine ⟨148188082608916396894997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6322691524647099600853205 148188082608916396894997)
                ·
                  rfl

theorem cell23_7792072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 7].length) (baseStart_7792072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792072 prefixEnd_7792072 := by exact prefixLift 7792072
  have htrace : WordTrace (prefixWord ++ tailWord_7792072) baseStart_7792072 baseEnd_7792072 := by
    simpa [prefixWord, tailWord_7792072, baseEnd_7792072] using wordTrace_append hprefix tailTrace_7792072
  have hstable : (prefixWord ++ tailWord_7792072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792072).length < 2 ^ (prefixWord ++ tailWord_7792072).sum := by decide
  have hdescent : baseEnd_7792072 < baseStart_7792072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792115 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 1, 8]
def baseStart_7792115 : Nat := 118140960795 + 7792115 * 2 ^ 59
def prefixEnd_7792115 : Nat := 4983230072969 + 3 ^ 40 * 7792115 * 2
def baseEnd_7792115 : Nat := 1333700103369628682642407

theorem tailTrace_7792115 : CollatzResearch.WordTrace tailWord_7792115 prefixEnd_7792115 1333700103369628682642407 := by
  unfold tailWord_7792115
  simp only [CollatzResearch.WordTrace]
  refine ⟨284201782165505617137721799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189467854777003744758481199 284201782165505617137721799)
  ·
    refine ⟨426302673248258425706582699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284201782165505617137721799 426302673248258425706582699)
    ·
      refine ⟨639454009872387638559874049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426302673248258425706582699 639454009872387638559874049)
      ·
        refine ⟨479590507404290728919905537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639454009872387638559874049 479590507404290728919905537)
        ·
          refine ⟨359692880553218046689929153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479590507404290728919905537 359692880553218046689929153)
          ·
            refine ⟨269769660414913535017446865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359692880553218046689929153 269769660414913535017446865)
            ·
              refine ⟨202327245311185151263085149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269769660414913535017446865 202327245311185151263085149)
              ·
                refine ⟨75872716991694431723656931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202327245311185151263085149 75872716991694431723656931)
                ·
                  refine ⟨113809075487541647585485397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75872716991694431723656931 113809075487541647585485397)
                  ·
                    refine ⟨1333700103369628682642407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113809075487541647585485397 1333700103369628682642407)
                    ·
                      rfl

theorem cell23_7792115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 8].length) (baseStart_7792115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792115 prefixEnd_7792115 := by exact prefixLift 7792115
  have htrace : WordTrace (prefixWord ++ tailWord_7792115) baseStart_7792115 baseEnd_7792115 := by
    simpa [prefixWord, tailWord_7792115, baseEnd_7792115] using wordTrace_append hprefix tailTrace_7792115
  have hstable : (prefixWord ++ tailWord_7792115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792115).length < 2 ^ (prefixWord ++ tailWord_7792115).sum := by decide
  have hdescent : baseEnd_7792115 < baseStart_7792115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792156 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_7792156 : Nat := 118140960795 + 7792156 * 2 ^ 59
def prefixEnd_7792156 : Nat := 4983230072969 + 3 ^ 40 * 7792156 * 2
def baseEnd_7792156 : Nat := 4001121362815720387514533

theorem tailTrace_7792156 : CollatzResearch.WordTrace tailWord_7792156 prefixEnd_7792156 4001121362815720387514533 := by
  unfold tailWord_7792156
  simp only [CollatzResearch.WordTrace]
  refine ⟨142101638779178540569982161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189468851705571387426642881 142101638779178540569982161)
  ·
    refine ⟨106576229084383905427486621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142101638779178540569982161 106576229084383905427486621)
    ·
      refine ⟨39966085906643964535307483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106576229084383905427486621 39966085906643964535307483)
      ·
        refine ⟨59949128859965946802961225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39966085906643964535307483 59949128859965946802961225)
        ·
          refine ⟨44961846644974460102220919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59949128859965946802961225 44961846644974460102220919)
          ·
            refine ⟨67442769967461690153331379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44961846644974460102220919 67442769967461690153331379)
            ·
              refine ⟨101164154951192535229997069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67442769967461690153331379 101164154951192535229997069)
              ·
                refine ⟨37936558106697200711248901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101164154951192535229997069 37936558106697200711248901)
                ·
                  refine ⟨7113104645005725133359169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37936558106697200711248901 7113104645005725133359169)
                  ·
                    refine ⟨5334828483754293850019377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7113104645005725133359169 5334828483754293850019377)
                    ·
                      refine ⟨4001121362815720387514533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5334828483754293850019377 4001121362815720387514533)
                      ·
                        rfl

theorem cell23_7792156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_7792156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792156 prefixEnd_7792156 := by exact prefixLift 7792156
  have htrace : WordTrace (prefixWord ++ tailWord_7792156) baseStart_7792156 baseEnd_7792156 := by
    simpa [prefixWord, tailWord_7792156, baseEnd_7792156] using wordTrace_append hprefix tailTrace_7792156
  have hstable : (prefixWord ++ tailWord_7792156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792156).length < 2 ^ (prefixWord ++ tailWord_7792156).sum := by decide
  have hdescent : baseEnd_7792156 < baseStart_7792156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792202 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_7792202 : Nat := 118140960795 + 7792202 * 2 ^ 59
def prefixEnd_7792202 : Nat := 4983230072969 + 3 ^ 40 * 7792202 * 2
def baseEnd_7792202 : Nat := 4001144982925827207539321

theorem tailTrace_7792202 : CollatzResearch.WordTrace tailWord_7792202 prefixEnd_7792202 4001144982925827207539321 := by
  unfold tailWord_7792202
  simp only [CollatzResearch.WordTrace]
  refine ⟨71051238829047607749034715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189469970210793620664092573 71051238829047607749034715)
  ·
    refine ⟨106576858243571411623552073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71051238829047607749034715 106576858243571411623552073)
    ·
      refine ⟨79932643682678558717664055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106576858243571411623552073 79932643682678558717664055)
      ·
        refine ⟨119898965524017838076496083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79932643682678558717664055 119898965524017838076496083)
        ·
          refine ⟨179848448286026757114744125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119898965524017838076496083 179848448286026757114744125)
          ·
            refine ⟨67443168107260033918029047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179848448286026757114744125 67443168107260033918029047)
            ·
              refine ⟨101164752160890050877043571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67443168107260033918029047 101164752160890050877043571)
              ·
                refine ⟨151747128241335076315565357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101164752160890050877043571 151747128241335076315565357)
                ·
                  refine ⟨56905173090500653618337009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151747128241335076315565357 56905173090500653618337009)
                  ·
                    refine ⟨42678879817875490213752757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56905173090500653618337009 42678879817875490213752757)
                    ·
                      refine ⟨4001144982925827207539321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42678879817875490213752757 4001144982925827207539321)
                      ·
                        rfl

theorem cell23_7792202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_7792202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792202 prefixEnd_7792202 := by exact prefixLift 7792202
  have htrace : WordTrace (prefixWord ++ tailWord_7792202) baseStart_7792202 baseEnd_7792202 := by
    simpa [prefixWord, tailWord_7792202, baseEnd_7792202] using wordTrace_append hprefix tailTrace_7792202
  have hstable : (prefixWord ++ tailWord_7792202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792202).length < 2 ^ (prefixWord ++ tailWord_7792202).sum := by decide
  have hdescent : baseEnd_7792202 < baseStart_7792202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792246 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_7792246 : Nat := 118140960795 + 7792246 * 2 ^ 59
def prefixEnd_7792246 : Nat := 4983230072969 + 3 ^ 40 * 7792246 * 2
def baseEnd_7792246 : Nat := 4001167576074625035389119

theorem tailTrace_7792246 : CollatzResearch.WordTrace tailWord_7792246 prefixEnd_7792246 4001167576074625035389119 := by
  unfold tailWord_7792246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17762910008001939156921287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189471040085354017673827061 17762910008001939156921287)
  ·
    refine ⟨26644365012002908735381931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17762910008001939156921287 26644365012002908735381931)
    ·
      refine ⟨39966547518004363103072897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26644365012002908735381931 39966547518004363103072897)
      ·
        refine ⟨29974910638503272327304673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39966547518004363103072897 29974910638503272327304673)
        ·
          refine ⟨22481182978877454245478505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29974910638503272327304673 22481182978877454245478505)
          ·
            refine ⟨16860887234158090684108879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22481182978877454245478505 16860887234158090684108879)
            ·
              refine ⟨25291330851237136026163319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16860887234158090684108879 25291330851237136026163319)
              ·
                refine ⟨37936996276855704039244979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25291330851237136026163319 37936996276855704039244979)
                ·
                  refine ⟨56905494415283556058867469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37936996276855704039244979 56905494415283556058867469)
                  ·
                    refine ⟨21339560405731333522075301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56905494415283556058867469 21339560405731333522075301)
                    ·
                      refine ⟨4001167576074625035389119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21339560405731333522075301 4001167576074625035389119)
                      ·
                        rfl

theorem cell23_7792246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_7792246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792246 prefixEnd_7792246 := by exact prefixLift 7792246
  have htrace : WordTrace (prefixWord ++ tailWord_7792246) baseStart_7792246 baseEnd_7792246 := by
    simpa [prefixWord, tailWord_7792246, baseEnd_7792246] using wordTrace_append hprefix tailTrace_7792246
  have hstable : (prefixWord ++ tailWord_7792246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792246).length < 2 ^ (prefixWord ++ tailWord_7792246).sum := by decide
  have hdescent : baseEnd_7792246 < baseStart_7792246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792249 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 1, 4, 3]
def baseStart_7792249 : Nat := 118140960795 + 7792249 * 2 ^ 59
def prefixEnd_7792249 : Nat := 4983230072969 + 3 ^ 40 * 7792249 * 2
def baseEnd_7792249 : Nat := 4001169116516588523651605

theorem tailTrace_7792249 : CollatzResearch.WordTrace tailWord_7792249 prefixEnd_7792249 4001169116516588523651605 := by
  unfold tailWord_7792249
  simp only [CollatzResearch.WordTrace]
  refine ⟨284206669547020158023099801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189471113031346772015399867 284206669547020158023099801)
  ·
    refine ⟨213155002160265118517324851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284206669547020158023099801 213155002160265118517324851)
    ·
      refine ⟨319732503240397677775987277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213155002160265118517324851 319732503240397677775987277)
      ·
        refine ⟨119899688715149129165995229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319732503240397677775987277 119899688715149129165995229)
        ·
          refine ⟨44962383268180923437248211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119899688715149129165995229 44962383268180923437248211)
          ·
            refine ⟨67443574902271385155872317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44962383268180923437248211 67443574902271385155872317)
            ·
              refine ⟨25291340588351769433452119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67443574902271385155872317 25291340588351769433452119)
              ·
                refine ⟨37937010882527654150178179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25291340588351769433452119 37937010882527654150178179)
                ·
                  refine ⟨56905516323791481225267269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37937010882527654150178179 56905516323791481225267269)
                  ·
                    refine ⟨10669784310710902729737613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56905516323791481225267269 10669784310710902729737613)
                    ·
                      refine ⟨4001169116516588523651605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10669784310710902729737613 4001169116516588523651605)
                      ·
                        rfl

theorem cell23_7792249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_7792249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792249 prefixEnd_7792249 := by exact prefixLift 7792249
  have htrace : WordTrace (prefixWord ++ tailWord_7792249) baseStart_7792249 baseEnd_7792249 := by
    simpa [prefixWord, tailWord_7792249, baseEnd_7792249] using wordTrace_append hprefix tailTrace_7792249
  have hstable : (prefixWord ++ tailWord_7792249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792249).length < 2 ^ (prefixWord ++ tailWord_7792249).sum := by decide
  have hdescent : baseEnd_7792249 < baseStart_7792249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792252 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 8]
def baseStart_7792252 : Nat := 118140960795 + 7792252 * 2 ^ 59
def prefixEnd_7792252 : Nat := 4983230072969 + 3 ^ 40 * 7792252 * 2
def baseEnd_7792252 : Nat := 444574517439839112434899

theorem tailTrace_7792252 : CollatzResearch.WordTrace tailWord_7792252 prefixEnd_7792252 444574517439839112434899 := by
  unfold tailWord_7792252
  simp only [CollatzResearch.WordTrace]
  refine ⟨142103389483004644767729505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189471185977339526356972673 142103389483004644767729505)
  ·
    refine ⟨106577542112253483575797129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142103389483004644767729505 106577542112253483575797129)
    ·
      refine ⟨79933156584190112681847847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106577542112253483575797129 79933156584190112681847847)
      ·
        refine ⟨119899734876285169022771771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79933156584190112681847847 119899734876285169022771771)
        ·
          refine ⟨179849602314427753534157657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119899734876285169022771771 179849602314427753534157657)
          ·
            refine ⟨134887201735820815150618243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179849602314427753534157657 134887201735820815150618243)
            ·
              refine ⟨202330802603731222725927365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134887201735820815150618243 202330802603731222725927365)
              ·
                refine ⟨37937025488199604261111381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202330802603731222725927365 37937025488199604261111381)
                ·
                  refine ⟨444574517439839112434899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37937025488199604261111381 444574517439839112434899)
                  ·
                    rfl

theorem cell23_7792252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_7792252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792252 prefixEnd_7792252 := by exact prefixLift 7792252
  have htrace : WordTrace (prefixWord ++ tailWord_7792252) baseStart_7792252 baseEnd_7792252 := by
    simpa [prefixWord, tailWord_7792252, baseEnd_7792252] using wordTrace_append hprefix tailTrace_7792252
  have hstable : (prefixWord ++ tailWord_7792252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792252).length < 2 ^ (prefixWord ++ tailWord_7792252).sum := by decide
  have hdescent : baseEnd_7792252 < baseStart_7792252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792306 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2]
def baseStart_7792306 : Nat := 118140960795 + 7792306 * 2 ^ 59
def prefixEnd_7792306 : Nat := 4983230072969 + 3 ^ 40 * 7792306 * 2
def baseEnd_7792306 : Nat := 4001198384913894800638843

theorem tailTrace_7792306 : CollatzResearch.WordTrace tailWord_7792306 prefixEnd_7792306 4001198384913894800638843 := by
  unfold tailWord_7792306
  simp only [CollatzResearch.WordTrace]
  refine ⟨71052187126953414189481193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189472499005209104505283181 71052187126953414189481193)
  ·
    refine ⟨53289140345215060642110895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71052187126953414189481193 53289140345215060642110895)
    ·
      refine ⟨79933710517822590963166343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53289140345215060642110895 79933710517822590963166343)
      ·
        refine ⟨119900565776733886444749515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79933710517822590963166343 119900565776733886444749515)
        ·
          refine ⟨179850848665100829667124273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119900565776733886444749515 179850848665100829667124273)
          ·
            refine ⟨134888136498825622250343205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179850848665100829667124273 134888136498825622250343205)
            ·
              refine ⟨25291525593529804171939351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134888136498825622250343205 25291525593529804171939351)
              ·
                refine ⟨37937288390294706257909027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25291525593529804171939351 37937288390294706257909027)
                ·
                  refine ⟨56905932585442059386863541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37937288390294706257909027 56905932585442059386863541)
                  ·
                    refine ⟨5334931179885193067518457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56905932585442059386863541 5334931179885193067518457)
                    ·
                      refine ⟨4001198384913894800638843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5334931179885193067518457 4001198384913894800638843)
                      ·
                        rfl

theorem cell23_7792306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_7792306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792306 prefixEnd_7792306 := by exact prefixLift 7792306
  have htrace : WordTrace (prefixWord ++ tailWord_7792306) baseStart_7792306 baseEnd_7792306 := by
    simpa [prefixWord, tailWord_7792306, baseEnd_7792306] using wordTrace_append hprefix tailTrace_7792306
  have hstable : (prefixWord ++ tailWord_7792306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792306).length < 2 ^ (prefixWord ++ tailWord_7792306).sum := by decide
  have hdescent : baseEnd_7792306 < baseStart_7792306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792316 : List Nat := [2, 2, 2, 3, 1, 2, 2, 3, 1, 5]
def baseStart_7792316 : Nat := 118140960795 + 7792316 * 2 ^ 59
def prefixEnd_7792316 : Nat := 4983230072969 + 3 ^ 40 * 7792316 * 2
def baseEnd_7792316 : Nat := 1333734506573479920504599

theorem tailTrace_7792316 : CollatzResearch.WordTrace tailWord_7792316 prefixEnd_7792316 1333734506573479920504599 := by
  unfold tailWord_7792316
  simp only [CollatzResearch.WordTrace]
  refine ⟨142104556618888714232894401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189472742158518285643859201 142104556618888714232894401)
  ·
    refine ⟨106578417464166535674670801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142104556618888714232894401 106578417464166535674670801)
    ·
      refine ⟨79933813098124901756003101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106578417464166535674670801 79933813098124901756003101)
      ·
        refine ⟨29975179911796838158501163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79933813098124901756003101 29975179911796838158501163)
        ·
          refine ⟨44962769867695257237751745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29975179911796838158501163 44962769867695257237751745)
          ·
            refine ⟨33722077400771442928313809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44962769867695257237751745 33722077400771442928313809)
            ·
              refine ⟨25291558050578582196235357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33722077400771442928313809 25291558050578582196235357)
              ·
                refine ⟨9484334268966968323588259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25291558050578582196235357 9484334268966968323588259)
                ·
                  refine ⟨14226501403450452485382389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9484334268966968323588259 14226501403450452485382389)
                  ·
                    refine ⟨1333734506573479920504599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14226501403450452485382389 1333734506573479920504599)
                    ·
                      rfl

theorem cell23_7792316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_7792316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792316 prefixEnd_7792316 := by exact prefixLift 7792316
  have htrace : WordTrace (prefixWord ++ tailWord_7792316) baseStart_7792316 baseEnd_7792316 := by
    simpa [prefixWord, tailWord_7792316, baseEnd_7792316] using wordTrace_append hprefix tailTrace_7792316
  have hstable : (prefixWord ++ tailWord_7792316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792316).length < 2 ^ (prefixWord ++ tailWord_7792316).sum := by decide
  have hdescent : baseEnd_7792316 < baseStart_7792316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792330 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 3, 1, 3]
def baseStart_7792330 : Nat := 118140960795 + 7792330 * 2 ^ 59
def prefixEnd_7792330 : Nat := 4983230072969 + 3 ^ 40 * 7792330 * 2
def baseEnd_7792330 : Nat := 4001210708449602706738733

theorem tailTrace_7792330 : CollatzResearch.WordTrace tailWord_7792330 prefixEnd_7792330 4001210708449602706738733 := by
  unfold tailWord_7792330
  simp only [CollatzResearch.WordTrace]
  refine ⟨71052405964931677214199611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189473082573151139237865629 71052405964931677214199611)
  ·
    refine ⟨106578608947397515821299417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71052405964931677214199611 106578608947397515821299417)
    ·
      refine ⟨79933956710548136865974563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106578608947397515821299417 79933956710548136865974563)
      ·
        refine ⟨119900935065822205298961845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79933956710548136865974563 119900935065822205298961845)
        ·
          refine ⟨11240712662420831746777673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119900935065822205298961845 11240712662420831746777673)
          ·
            refine ⟨8430534496815623810083255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11240712662420831746777673 8430534496815623810083255)
            ·
              refine ⟨12645801745223435715124883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8430534496815623810083255 12645801745223435715124883)
              ·
                refine ⟨18968702617835153572687325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12645801745223435715124883 18968702617835153572687325)
                ·
                  refine ⟨7113263481688182589757747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18968702617835153572687325 7113263481688182589757747)
                  ·
                    refine ⟨10669895222532273884636621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7113263481688182589757747 10669895222532273884636621)
                    ·
                      refine ⟨4001210708449602706738733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10669895222532273884636621 4001210708449602706738733)
                      ·
                        rfl

theorem cell23_7792330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_7792330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792330 prefixEnd_7792330 := by exact prefixLift 7792330
  have htrace : WordTrace (prefixWord ++ tailWord_7792330) baseStart_7792330 baseEnd_7792330 := by
    simpa [prefixWord, tailWord_7792330, baseEnd_7792330] using wordTrace_append hprefix tailTrace_7792330
  have hstable : (prefixWord ++ tailWord_7792330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792330).length < 2 ^ (prefixWord ++ tailWord_7792330).sum := by decide
  have hdescent : baseEnd_7792330 < baseStart_7792330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792356 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_7792356 : Nat := 118140960795 + 7792356 * 2 ^ 59
def prefixEnd_7792356 : Nat := 4983230072969 + 3 ^ 40 * 7792356 * 2
def baseEnd_7792356 : Nat := 4001224058946619605013613

theorem tailTrace_7792356 : CollatzResearch.WordTrace tailWord_7792356 prefixEnd_7792356 4001224058946619605013613 := by
  unfold tailWord_7792356
  simp only [CollatzResearch.WordTrace]
  refine ⟨142105286078816257648622461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189473714771755010198163281 142105286078816257648622461)
  ·
    refine ⟨53289482279556096618233423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142105286078816257648622461 53289482279556096618233423)
    ·
      refine ⟨79934223419334144927350135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53289482279556096618233423 79934223419334144927350135)
      ·
        refine ⟨119901335129001217391025203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79934223419334144927350135 119901335129001217391025203)
        ·
          refine ⟨179852002693501826086537805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119901335129001217391025203 179852002693501826086537805)
          ·
            refine ⟨67444501010063184782451677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179852002693501826086537805 67444501010063184782451677)
            ·
              refine ⟨25291687878773694293419379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67444501010063184782451677 25291687878773694293419379)
              ·
                refine ⟨37937531818160541440129069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25291687878773694293419379 37937531818160541440129069)
                ·
                  refine ⟨14226574431810203040048401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37937531818160541440129069 14226574431810203040048401)
                  ·
                    refine ⟨10669930823857652280036301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14226574431810203040048401 10669930823857652280036301)
                    ·
                      refine ⟨4001224058946619605013613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10669930823857652280036301 4001224058946619605013613)
                      ·
                        rfl

theorem cell23_7792356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_7792356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792356 prefixEnd_7792356 := by exact prefixLift 7792356
  have htrace : WordTrace (prefixWord ++ tailWord_7792356) baseStart_7792356 baseEnd_7792356 := by
    simpa [prefixWord, tailWord_7792356, baseEnd_7792356] using wordTrace_append hprefix tailTrace_7792356
  have hstable : (prefixWord ++ tailWord_7792356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792356).length < 2 ^ (prefixWord ++ tailWord_7792356).sum := by decide
  have hdescent : baseEnd_7792356 < baseStart_7792356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792366 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_7792366 : Nat := 118140960795 + 7792366 * 2 ^ 59
def prefixEnd_7792366 : Nat := 4983230072969 + 3 ^ 40 * 7792366 * 2
def baseEnd_7792366 : Nat := 4001229193753164565888567

theorem tailTrace_7792366 : CollatzResearch.WordTrace tailWord_7792366 prefixEnd_7792366 4001229193753164565888567 := by
  unfold tailWord_7792366
  simp only [CollatzResearch.WordTrace]
  refine ⟨35526367110949535875638619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189473957925064191336739301 35526367110949535875638619)
  ·
    refine ⟨53289550666424303813457929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35526367110949535875638619 53289550666424303813457929)
    ·
      refine ⟨39967162999818227860093447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53289550666424303813457929 39967162999818227860093447)
      ·
        refine ⟨59950744499727341790140171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39967162999818227860093447 59950744499727341790140171)
        ·
          refine ⟨89926116749591012685210257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59950744499727341790140171 89926116749591012685210257)
          ·
            refine ⟨67444587562193259513907693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89926116749591012685210257 67444587562193259513907693)
            ·
              refine ⟨25291720335822472317715385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67444587562193259513907693 25291720335822472317715385)
              ·
                refine ⟨18968790251866854238286539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25291720335822472317715385 18968790251866854238286539)
                ·
                  refine ⟨28453185377800281357429809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18968790251866854238286539 28453185377800281357429809)
                  ·
                    refine ⟨21339889033350211018072357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28453185377800281357429809 21339889033350211018072357)
                    ·
                      refine ⟨4001229193753164565888567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21339889033350211018072357 4001229193753164565888567)
                      ·
                        rfl

theorem cell23_7792366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_7792366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792366 prefixEnd_7792366 := by exact prefixLift 7792366
  have htrace : WordTrace (prefixWord ++ tailWord_7792366) baseStart_7792366 baseEnd_7792366 := by
    simpa [prefixWord, tailWord_7792366, baseEnd_7792366] using wordTrace_append hprefix tailTrace_7792366
  have hstable : (prefixWord ++ tailWord_7792366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792366).length < 2 ^ (prefixWord ++ tailWord_7792366).sum := by decide
  have hdescent : baseEnd_7792366 < baseStart_7792366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792387 : List Nat := [1, 1, 1, 3, 2, 2, 6, 2, 1, 2, 2]
def baseStart_7792387 : Nat := 118140960795 + 7792387 * 2 ^ 59
def prefixEnd_7792387 : Nat := 4983230072969 + 3 ^ 40 * 7792387 * 2
def baseEnd_7792387 : Nat := 4001239976846908983725971

theorem tailTrace_7792387 : CollatzResearch.WordTrace tailWord_7792387 prefixEnd_7792387 4001239976846908983725971 := by
  unfold tailWord_7792387
  simp only [CollatzResearch.WordTrace]
  refine ⟨284211702820520207591623415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189474468547013471727748943 284211702820520207591623415)
  ·
    refine ⟨426317554230780311387435123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284211702820520207591623415 426317554230780311387435123)
    ·
      refine ⟨639476331346170467081152685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426317554230780311387435123 639476331346170467081152685)
      ·
        refine ⟨239803624254813925155432257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639476331346170467081152685 239803624254813925155432257)
        ·
          refine ⟨179852718191110443866574193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239803624254813925155432257 179852718191110443866574193)
          ·
            refine ⟨134889538643332832899930645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179852718191110443866574193 134889538643332832899930645)
            ·
              refine ⟨6322947123906226542184249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134889538643332832899930645 6322947123906226542184249)
              ·
                refine ⟨4742210342929669906638187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6322947123906226542184249 4742210342929669906638187)
                ·
                  refine ⟨7113315514394504859957281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4742210342929669906638187 7113315514394504859957281)
                  ·
                    refine ⟨5334986635795878644967961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7113315514394504859957281 5334986635795878644967961)
                    ·
                      refine ⟨4001239976846908983725971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5334986635795878644967961 4001239976846908983725971)
                      ·
                        rfl

theorem cell23_7792387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 1, 2, 2].length) (baseStart_7792387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792387 prefixEnd_7792387 := by exact prefixLift 7792387
  have htrace : WordTrace (prefixWord ++ tailWord_7792387) baseStart_7792387 baseEnd_7792387 := by
    simpa [prefixWord, tailWord_7792387, baseEnd_7792387] using wordTrace_append hprefix tailTrace_7792387
  have hstable : (prefixWord ++ tailWord_7792387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792387).length < 2 ^ (prefixWord ++ tailWord_7792387).sum := by decide
  have hdescent : baseEnd_7792387 < baseStart_7792387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792437 : List Nat := [1, 3, 3, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_7792437 : Nat := 118140960795 + 7792437 * 2 ^ 59
def prefixEnd_7792437 : Nat := 4983230072969 + 3 ^ 40 * 7792437 * 2
def baseEnd_7792437 : Nat := 4001265650879633788100741

theorem tailTrace_7792437 : CollatzResearch.WordTrace tailWord_7792437 prefixEnd_7792437 4001265650879633788100741 := by
  unfold tailWord_7792437
  simp only [CollatzResearch.WordTrace]
  refine ⟨284213526470339066130943565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189475684313559377420629043 284213526470339066130943565)
  ·
    refine ⟨106580072426377149799103837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284213526470339066130943565 106580072426377149799103837)
    ·
      refine ⟨39967527159891431174663939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106580072426377149799103837 39967527159891431174663939)
      ·
        refine ⟨59951290739837146761995909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39967527159891431174663939 59951290739837146761995909)
        ·
          refine ⟨11240867013719465017874233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59951290739837146761995909 11240867013719465017874233)
          ·
            refine ⟨8430650260289598763405675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11240867013719465017874233 8430650260289598763405675)
            ·
              refine ⟨12645975390434398145108513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8430650260289598763405675 12645975390434398145108513)
              ·
                refine ⟨9484481542825798608831385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12645975390434398145108513 9484481542825798608831385)
                ·
                  refine ⟨7113361157119348956623539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9484481542825798608831385 7113361157119348956623539)
                  ·
                    refine ⟨10670041735679023434935309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7113361157119348956623539 10670041735679023434935309)
                    ·
                      refine ⟨4001265650879633788100741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10670041735679023434935309 4001265650879633788100741)
                      ·
                        rfl

theorem cell23_7792437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_7792437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792437 prefixEnd_7792437 := by exact prefixLift 7792437
  have htrace : WordTrace (prefixWord ++ tailWord_7792437) baseStart_7792437 baseEnd_7792437 := by
    simpa [prefixWord, tailWord_7792437, baseEnd_7792437] using wordTrace_append hprefix tailTrace_7792437
  have hstable : (prefixWord ++ tailWord_7792437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792437).length < 2 ^ (prefixWord ++ tailWord_7792437).sum := by decide
  have hdescent : baseEnd_7792437 < baseStart_7792437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792456 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_7792456 : Nat := 118140960795 + 7792456 * 2 ^ 59
def prefixEnd_7792456 : Nat := 4983230072969 + 3 ^ 40 * 7792456 * 2
def baseEnd_7792456 : Nat := 4001275407012069213763153

theorem tailTrace_7792456 : CollatzResearch.WordTrace tailWord_7792456 prefixEnd_7792456 4001275407012069213763153 := by
  unfold tailWord_7792456
  simp only [CollatzResearch.WordTrace]
  refine ⟨142107109728635116187942611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189476146304846821583923481 142107109728635116187942611)
  ·
    refine ⟨213160664592952674281913917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142107109728635116187942611 213160664592952674281913917)
    ·
      refine ⟨79935249222357252855717719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213160664592952674281913917 79935249222357252855717719)
      ·
        refine ⟨119902873833535879283576579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79935249222357252855717719 119902873833535879283576579)
        ·
          refine ⟨179854310750303818925364869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119902873833535879283576579 179854310750303818925364869)
          ·
            refine ⟨33722683265681966048505913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179854310750303818925364869 33722683265681966048505913)
            ·
              refine ⟨25292012449261474536379435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33722683265681966048505913 25292012449261474536379435)
              ·
                refine ⟨37938018673892211804569153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25292012449261474536379435 37938018673892211804569153)
                ·
                  refine ⟨28453514005419158853426865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37938018673892211804569153 28453514005419158853426865)
                  ·
                    refine ⟨21340135504064369140070149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28453514005419158853426865 21340135504064369140070149)
                    ·
                      refine ⟨4001275407012069213763153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21340135504064369140070149 4001275407012069213763153)
                      ·
                        rfl

theorem cell23_7792456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_7792456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792456 prefixEnd_7792456 := by exact prefixLift 7792456
  have htrace : WordTrace (prefixWord ++ tailWord_7792456) baseStart_7792456 baseEnd_7792456 := by
    simpa [prefixWord, tailWord_7792456, baseEnd_7792456] using wordTrace_append hprefix tailTrace_7792456
  have hstable : (prefixWord ++ tailWord_7792456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792456).length < 2 ^ (prefixWord ++ tailWord_7792456).sum := by decide
  have hdescent : baseEnd_7792456 < baseStart_7792456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792466 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 7]
def baseStart_7792466 : Nat := 118140960795 + 7792466 * 2 ^ 59
def prefixEnd_7792466 : Nat := 4983230072969 + 3 ^ 40 * 7792466 * 2
def baseEnd_7792466 : Nat := 444586726868734908293123

theorem tailTrace_7792466 : CollatzResearch.WordTrace tailWord_7792466 prefixEnd_7792466 444586726868734908293123 := by
  unfold tailWord_7792466
  simp only [CollatzResearch.WordTrace]
  refine ⟨71053646046808501020937313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189476389458156002722499501 71053646046808501020937313)
  ·
    refine ⟨53290234535106375765702985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71053646046808501020937313 53290234535106375765702985)
    ·
      refine ⟨39967675901329781824277239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53290234535106375765702985 39967675901329781824277239)
      ·
        refine ⟨59951513851994672736415859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39967675901329781824277239 59951513851994672736415859)
        ·
          refine ⟨89927270777992009104623789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59951513851994672736415859 89927270777992009104623789)
          ·
            refine ⟨33722726541747003414233921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89927270777992009104623789 33722726541747003414233921)
            ·
              refine ⟨25292044906310252560675441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33722726541747003414233921 25292044906310252560675441)
              ·
                refine ⟨18969033679732689420506581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25292044906310252560675441 18969033679732689420506581)
                ·
                  refine ⟨444586726868734908293123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18969033679732689420506581 444586726868734908293123)
                  ·
                    rfl

theorem cell23_7792466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_7792466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792466 prefixEnd_7792466 := by exact prefixLift 7792466
  have htrace : WordTrace (prefixWord ++ tailWord_7792466) baseStart_7792466 baseEnd_7792466 := by
    simpa [prefixWord, tailWord_7792466, baseEnd_7792466] using wordTrace_append hprefix tailTrace_7792466
  have hstable : (prefixWord ++ tailWord_7792466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792466).length < 2 ^ (prefixWord ++ tailWord_7792466).sum := by decide
  have hdescent : baseEnd_7792466 < baseStart_7792466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792489 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 7]
def baseStart_7792489 : Nat := 118140960795 + 7792489 * 2 ^ 59
def prefixEnd_7792489 : Nat := 4983230072969 + 3 ^ 40 * 7792489 * 2
def baseEnd_7792489 : Nat := 4001292351873667584650501

theorem tailTrace_7792489 : CollatzResearch.WordTrace tailWord_7792489 prefixEnd_7792489 4001292351873667584650501 := by
  unfold tailWord_7792489
  simp only [CollatzResearch.WordTrace]
  refine ⟨284215423066150679011836521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189476948710767119341224347 284215423066150679011836521)
  ·
    refine ⟨213161567299613009258877391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284215423066150679011836521 213161567299613009258877391)
    ·
      refine ⟨319742350949419513888316087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213161567299613009258877391 319742350949419513888316087)
      ·
        refine ⟨479613526424129270832474131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319742350949419513888316087 479613526424129270832474131)
        ·
          refine ⟨719420289636193906248711197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479613526424129270832474131 719420289636193906248711197)
          ·
            refine ⟨269782608613572714843266699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 719420289636193906248711197 269782608613572714843266699)
            ·
              refine ⟨404673912920359072264900049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269782608613572714843266699 404673912920359072264900049)
              ·
                refine ⟨303505434690269304198675037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404673912920359072264900049 303505434690269304198675037)
                ·
                  refine ⟨113814538008850989074503139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303505434690269304198675037 113814538008850989074503139)
                  ·
                    refine ⟨170721807013276483611754709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113814538008850989074503139 170721807013276483611754709)
                    ·
                      refine ⟨4001292351873667584650501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170721807013276483611754709 4001292351873667584650501)
                      ·
                        rfl

theorem cell23_7792489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_7792489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792489 prefixEnd_7792489 := by exact prefixLift 7792489
  have htrace : WordTrace (prefixWord ++ tailWord_7792489) baseStart_7792489 baseEnd_7792489 := by
    simpa [prefixWord, tailWord_7792489, baseEnd_7792489] using wordTrace_append hprefix tailTrace_7792489
  have hstable : (prefixWord ++ tailWord_7792489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792489).length < 2 ^ (prefixWord ++ tailWord_7792489).sum := by decide
  have hdescent : baseEnd_7792489 < baseStart_7792489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792516 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_7792516 : Nat := 118140960795 + 7792516 * 2 ^ 59
def prefixEnd_7792516 : Nat := 4983230072969 + 3 ^ 40 * 7792516 * 2
def baseEnd_7792516 : Nat := 4001306215851338979012877

theorem tailTrace_7792516 : CollatzResearch.WordTrace tailWord_7792516 prefixEnd_7792516 4001306215851338979012877 := by
  unfold tailWord_7792516
  simp only [CollatzResearch.WordTrace]
  refine ⟨142108203918526431311534701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189477605224701908415379601 142108203918526431311534701)
  ·
    refine ⟨53290576469447411741825513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142108203918526431311534701 53290576469447411741825513)
    ·
      refine ⟨39967932352085558806369135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53290576469447411741825513 39967932352085558806369135)
      ·
        refine ⟨59951898528128338209553703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39967932352085558806369135 59951898528128338209553703)
        ·
          refine ⟨89927847792192507314330555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59951898528128338209553703 89927847792192507314330555)
          ·
            refine ⟨134891771688288760971495833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89927847792192507314330555 134891771688288760971495833)
            ·
              refine ⟨101168828766216570728621875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134891771688288760971495833 101168828766216570728621875)
              ·
                refine ⟨151753243149324856092932813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101168828766216570728621875 151753243149324856092932813)
                ·
                  refine ⟨56907466180996821034849805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151753243149324856092932813 56907466180996821034849805)
                  ·
                    refine ⟨21340299817873807888068677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56907466180996821034849805 21340299817873807888068677)
                    ·
                      refine ⟨4001306215851338979012877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21340299817873807888068677 4001306215851338979012877)
                      ·
                        rfl

theorem cell23_7792516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_7792516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792516 prefixEnd_7792516 := by exact prefixLift 7792516
  have htrace : WordTrace (prefixWord ++ tailWord_7792516) baseStart_7792516 baseEnd_7792516 := by
    simpa [prefixWord, tailWord_7792516, baseEnd_7792516] using wordTrace_append hprefix tailTrace_7792516
  have hstable : (prefixWord ++ tailWord_7792516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792516).length < 2 ^ (prefixWord ++ tailWord_7792516).sum := by decide
  have hdescent : baseEnd_7792516 < baseStart_7792516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792530 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_7792530 : Nat := 118140960795 + 7792530 * 2 ^ 59
def prefixEnd_7792530 : Nat := 4983230072969 + 3 ^ 40 * 7792530 * 2
def baseEnd_7792530 : Nat := 1333771134860167308079271

theorem tailTrace_7792530 : CollatzResearch.WordTrace tailWord_7792530 prefixEnd_7792530 1333771134860167308079271 := by
  unfold tailWord_7792530
  simp only [CollatzResearch.WordTrace]
  refine ⟨71054229614750535753519761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189477945639334762009386029 71054229614750535753519761)
  ·
    refine ⟨53290672211062901815139821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71054229614750535753519761 53290672211062901815139821)
    ·
      refine ⟨19984002079148588180677433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53290672211062901815139821 19984002079148588180677433)
      ·
        refine ⟨14988001559361441135508075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19984002079148588180677433 14988001559361441135508075)
        ·
          refine ⟨22482002339042161703262113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14988001559361441135508075 22482002339042161703262113)
          ·
            refine ⟨16861501754281621277446585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22482002339042161703262113 16861501754281621277446585)
            ·
              refine ⟨12646126315711215958084939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16861501754281621277446585 12646126315711215958084939)
              ·
                refine ⟨18969189473566823937127409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12646126315711215958084939 18969189473566823937127409)
                ·
                  refine ⟨14226892105175117952845557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18969189473566823937127409 14226892105175117952845557)
                  ·
                    refine ⟨1333771134860167308079271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14226892105175117952845557 1333771134860167308079271)
                    ·
                      rfl

theorem cell23_7792530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_7792530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792530 prefixEnd_7792530 := by exact prefixLift 7792530
  have htrace : WordTrace (prefixWord ++ tailWord_7792530) baseStart_7792530 baseEnd_7792530 := by
    simpa [prefixWord, tailWord_7792530, baseEnd_7792530] using wordTrace_append hprefix tailTrace_7792530
  have hstable : (prefixWord ++ tailWord_7792530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792530).length < 2 ^ (prefixWord ++ tailWord_7792530).sum := by decide
  have hdescent : baseEnd_7792530 < baseStart_7792530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792533 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_7792533 : Nat := 118140960795 + 7792533 * 2 ^ 59
def prefixEnd_7792533 : Nat := 4983230072969 + 3 ^ 40 * 7792533 * 2
def baseEnd_7792533 : Nat := 4001314945022465412500299

theorem tailTrace_7792533 : CollatzResearch.WordTrace tailWord_7792533 prefixEnd_7792533 4001314945022465412500299 := by
  unfold tailWord_7792533
  simp only [CollatzResearch.WordTrace]
  refine ⟨284217027877991274526438253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189478018585327516350958835 284217027877991274526438253)
  ·
    refine ⟨106581385454246727947414345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284217027877991274526438253 106581385454246727947414345)
    ·
      refine ⟨79936039090685045960560759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106581385454246727947414345 79936039090685045960560759)
      ·
        refine ⟨119904058636027568940841139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79936039090685045960560759 119904058636027568940841139)
        ·
          refine ⟨179856087954041353411261709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119904058636027568940841139 179856087954041353411261709)
          ·
            refine ⟨67446032982765507529223141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179856087954041353411261709 67446032982765507529223141)
            ·
              refine ⟨12646131184268532661729339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67446032982765507529223141 12646131184268532661729339)
              ·
                refine ⟨18969196776402798992594009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12646131184268532661729339 18969196776402798992594009)
                ·
                  refine ⟨14226897582302099244445507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18969196776402798992594009 14226897582302099244445507)
                  ·
                    refine ⟨21340346373453148866668261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14226897582302099244445507 21340346373453148866668261)
                    ·
                      refine ⟨4001314945022465412500299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21340346373453148866668261 4001314945022465412500299)
                      ·
                        rfl

theorem cell23_7792533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_7792533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792533 prefixEnd_7792533 := by exact prefixLift 7792533
  have htrace : WordTrace (prefixWord ++ tailWord_7792533) baseStart_7792533 baseEnd_7792533 := by
    simpa [prefixWord, tailWord_7792533, baseEnd_7792533] using wordTrace_append hprefix tailTrace_7792533
  have hstable : (prefixWord ++ tailWord_7792533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792533).length < 2 ^ (prefixWord ++ tailWord_7792533).sum := by decide
  have hdescent : baseEnd_7792533 < baseStart_7792533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792573 : List Nat := [1, 4, 1, 2, 3, 1, 2, 3, 6]
def baseStart_7792573 : Nat := 118140960795 + 7792573 * 2 ^ 59
def prefixEnd_7792573 : Nat := 4983230072969 + 3 ^ 40 * 7792573 * 2
def baseEnd_7792573 : Nat := 444592831583182806222235

theorem tailTrace_7792573 : CollatzResearch.WordTrace tailWord_7792573 prefixEnd_7792573 444592831583182806222235 := by
  unfold tailWord_7792573
  simp only [CollatzResearch.WordTrace]
  refine ⟨284218486797846361357894373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189478991198564240905262915 284218486797846361357894373)
  ·
    refine ⟨53290966274596192754605195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284218486797846361357894373 53290966274596192754605195)
    ·
      refine ⟨79936449411894289131907793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53290966274596192754605195 79936449411894289131907793)
      ·
        refine ⟨59952337058920716848930845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79936449411894289131907793 59952337058920716848930845)
        ·
          refine ⟨22482126397095268818349067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59952337058920716848930845 22482126397095268818349067)
          ·
            refine ⟨33723189595642903227523601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22482126397095268818349067 33723189595642903227523601)
            ·
              refine ⟨25292392196732177420642701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33723189595642903227523601 25292392196732177420642701)
              ·
                refine ⟨9484647073774566532741013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25292392196732177420642701 9484647073774566532741013)
                ·
                  refine ⟨444592831583182806222235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9484647073774566532741013 444592831583182806222235)
                  ·
                    rfl

theorem cell23_7792573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_7792573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792573 prefixEnd_7792573 := by exact prefixLift 7792573
  have htrace : WordTrace (prefixWord ++ tailWord_7792573) baseStart_7792573 baseEnd_7792573 := by
    simpa [prefixWord, tailWord_7792573, baseEnd_7792573] using wordTrace_append hprefix tailTrace_7792573
  have hstable : (prefixWord ++ tailWord_7792573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792573).length < 2 ^ (prefixWord ++ tailWord_7792573).sum := by decide
  have hdescent : baseEnd_7792573 < baseStart_7792573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792594 : List Nat := [3, 2, 2, 3, 2, 1, 2, 3, 1, 4]
def baseStart_7792594 : Nat := 118140960795 + 7792594 * 2 ^ 59
def prefixEnd_7792594 : Nat := 4983230072969 + 3 ^ 40 * 7792594 * 2
def baseEnd_7792594 : Nat := 1333782089114129891279173

theorem tailTrace_7792594 : CollatzResearch.WordTrace tailWord_7792594 prefixEnd_7792594 1333782089114129891279173 := by
  unfold tailWord_7792594
  simp only [CollatzResearch.WordTrace]
  refine ⟨71054813182692570486102209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189479501820513521296272557 71054813182692570486102209)
  ·
    refine ⟨53291109887019427864576657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71054813182692570486102209 53291109887019427864576657)
    ·
      refine ⟨39968332415264570898432493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53291109887019427864576657 39968332415264570898432493)
      ·
        refine ⟨14988124655724214086912185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39968332415264570898432493 14988124655724214086912185)
        ·
          refine ⟨11241093491793160565184139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14988124655724214086912185 11241093491793160565184139)
          ·
            refine ⟨16861640237689740847776209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11241093491793160565184139 16861640237689740847776209)
            ·
              refine ⟨12646230178267305635832157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16861640237689740847776209 12646230178267305635832157)
              ·
                refine ⟨4742336316850239613437059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12646230178267305635832157 4742336316850239613437059)
                ·
                  refine ⟨7113504475275359420155589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4742336316850239613437059 7113504475275359420155589)
                  ·
                    refine ⟨1333782089114129891279173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7113504475275359420155589 1333782089114129891279173)
                    ·
                      rfl

theorem cell23_7792594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_7792594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792594 prefixEnd_7792594 := by exact prefixLift 7792594
  have htrace : WordTrace (prefixWord ++ tailWord_7792594) baseStart_7792594 baseEnd_7792594 := by
    simpa [prefixWord, tailWord_7792594, baseEnd_7792594] using wordTrace_append hprefix tailTrace_7792594
  have hstable : (prefixWord ++ tailWord_7792594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792594).length < 2 ^ (prefixWord ++ tailWord_7792594).sum := by decide
  have hdescent : baseEnd_7792594 < baseStart_7792594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792633 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 1, 6]
def baseStart_7792633 : Nat := 118140960795 + 7792633 * 2 ^ 59
def prefixEnd_7792633 : Nat := 4983230072969 + 3 ^ 40 * 7792633 * 2
def baseEnd_7792633 : Nat := 1333788764362638340416613

theorem tailTrace_7792633 : CollatzResearch.WordTrace tailWord_7792633 prefixEnd_7792633 1333788764362638340416613 := by
  unfold tailWord_7792633
  simp only [CollatzResearch.WordTrace]
  refine ⟨284220675177628991605078553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189480450118419327736719035 284220675177628991605078553)
  ·
    refine ⟨213165506383221743703808915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284220675177628991605078553 213165506383221743703808915)
    ·
      refine ⟨319748259574832615555713373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213165506383221743703808915 319748259574832615555713373)
      ·
        refine ⟨119905597340562230833392515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319748259574832615555713373 119905597340562230833392515)
        ·
          refine ⟨179858396010843346250088773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119905597340562230833392515 179858396010843346250088773)
          ·
            refine ⟨33723449252033127421891645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179858396010843346250088773 33723449252033127421891645)
            ·
              refine ⟨12646293469512422783209367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33723449252033127421891645 12646293469512422783209367)
              ·
                refine ⟨18969440204268634174814051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12646293469512422783209367 18969440204268634174814051)
                ·
                  refine ⟨28454160306402951262221077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18969440204268634174814051 28454160306402951262221077)
                  ·
                    refine ⟨1333788764362638340416613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28454160306402951262221077 1333788764362638340416613)
                    ·
                      rfl

theorem cell23_7792633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 6].length) (baseStart_7792633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792633 prefixEnd_7792633 := by exact prefixLift 7792633
  have htrace : WordTrace (prefixWord ++ tailWord_7792633) baseStart_7792633 baseEnd_7792633 := by
    simpa [prefixWord, tailWord_7792633, baseEnd_7792633] using wordTrace_append hprefix tailTrace_7792633
  have hstable : (prefixWord ++ tailWord_7792633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792633).length < 2 ^ (prefixWord ++ tailWord_7792633).sum := by decide
  have hdescent : baseEnd_7792633 < baseStart_7792633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792640 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 5, 2, 2]
def baseStart_7792640 : Nat := 118140960795 + 7792640 * 2 ^ 59
def prefixEnd_7792640 : Nat := 4983230072969 + 3 ^ 40 * 7792640 * 2
def baseEnd_7792640 : Nat := 4001369887452496493862307

theorem tailTrace_7792640 : CollatzResearch.WordTrace tailWord_7792640 prefixEnd_7792640 4001369887452496493862307 := by
  unfold tailWord_7792640
  simp only [CollatzResearch.WordTrace]
  refine ⟨142110465244301815900291687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189480620325735754533722249 142110465244301815900291687)
  ·
    refine ⟨213165697866452723850437531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142110465244301815900291687 213165697866452723850437531)
    ·
      refine ⟨319748546799679085775656297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213165697866452723850437531 319748546799679085775656297)
      ·
        refine ⟨239811410099759314331742223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319748546799679085775656297 239811410099759314331742223)
        ·
          refine ⟨359717115149638971497613335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239811410099759314331742223 359717115149638971497613335)
          ·
            refine ⟨539575672724458457246420003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359717115149638971497613335 539575672724458457246420003)
            ·
              refine ⟨809363509086687685869630005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539575672724458457246420003 809363509086687685869630005)
              ·
                refine ⟨75877828976876970550277813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 809363509086687685869630005 75877828976876970550277813)
                ·
                  refine ⟨7113546466582215989088545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75877828976876970550277813 7113546466582215989088545)
                  ·
                    refine ⟨5335159849936661991816409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7113546466582215989088545 5335159849936661991816409)
                    ·
                      refine ⟨4001369887452496493862307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5335159849936661991816409 4001369887452496493862307)
                      ·
                        rfl

theorem cell23_7792640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 5, 2, 2].length) (baseStart_7792640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792640 prefixEnd_7792640 := by exact prefixLift 7792640
  have htrace : WordTrace (prefixWord ++ tailWord_7792640) baseStart_7792640 baseEnd_7792640 := by
    simpa [prefixWord, tailWord_7792640, baseEnd_7792640] using wordTrace_append hprefix tailTrace_7792640
  have hstable : (prefixWord ++ tailWord_7792640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792640).length < 2 ^ (prefixWord ++ tailWord_7792640).sum := by decide
  have hdescent : baseEnd_7792640 < baseStart_7792640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792643 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 3]
def baseStart_7792643 : Nat := 118140960795 + 7792643 * 2 ^ 59
def prefixEnd_7792643 : Nat := 4983230072969 + 3 ^ 40 * 7792643 * 2
def baseEnd_7792643 : Nat := 4001371427894459982124793

theorem tailTrace_7792643 : CollatzResearch.WordTrace tailWord_7792643 prefixEnd_7792643 4001371427894459982124793 := by
  unfold tailWord_7792643
  simp only [CollatzResearch.WordTrace]
  refine ⟨284221039907592763312942583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189480693271728508875295055 284221039907592763312942583)
  ·
    refine ⟨426331559861389144969413875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284221039907592763312942583 426331559861389144969413875)
    ·
      refine ⟨639497339792083717454120813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426331559861389144969413875 639497339792083717454120813)
      ·
        refine ⟨239811502422031394045295305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639497339792083717454120813 239811502422031394045295305)
        ·
          refine ⟨179858626816523545533971479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239811502422031394045295305 179858626816523545533971479)
          ·
            refine ⟨269787940224785318300957219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179858626816523545533971479 269787940224785318300957219)
            ·
              refine ⟨404681910337177977451435829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269787940224785318300957219 404681910337177977451435829)
              ·
                refine ⟨37938929094110435386072109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 404681910337177977451435829 37938929094110435386072109)
                ·
                  refine ⟨14227098410291413269777041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37938929094110435386072109 14227098410291413269777041)
                  ·
                    refine ⟨10670323807718559952332781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14227098410291413269777041 10670323807718559952332781)
                    ·
                      refine ⟨4001371427894459982124793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10670323807718559952332781 4001371427894459982124793)
                      ·
                        rfl

theorem cell23_7792643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_7792643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792643 prefixEnd_7792643 := by exact prefixLift 7792643
  have htrace : WordTrace (prefixWord ++ tailWord_7792643) baseStart_7792643 baseEnd_7792643 := by
    simpa [prefixWord, tailWord_7792643, baseEnd_7792643] using wordTrace_append hprefix tailTrace_7792643
  have hstable : (prefixWord ++ tailWord_7792643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792643).length < 2 ^ (prefixWord ++ tailWord_7792643).sum := by decide
  have hdescent : baseEnd_7792643 < baseStart_7792643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792730 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2]
def baseStart_7792730 : Nat := 118140960795 + 7792730 * 2 ^ 59
def prefixEnd_7792730 : Nat := 4983230072969 + 3 ^ 40 * 7792730 * 2
def baseEnd_7792730 : Nat := 4001416100711401141736893

theorem tailTrace_7792730 : CollatzResearch.WordTrace tailWord_7792730 prefixEnd_7792730 4001416100711401141736893 := by
  unfold tailWord_7792730
  simp only [CollatzResearch.WordTrace]
  refine ⟨71056053264569394292839911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189482808705518384780906429 71056053264569394292839911)
  ·
    refine ⟨106584079896854091439259867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71056053264569394292839911 106584079896854091439259867)
    ·
      refine ⟨159876119845281137158889801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106584079896854091439259867 159876119845281137158889801)
      ·
        refine ⟨119907089883960852869167351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159876119845281137158889801 119907089883960852869167351)
        ·
          refine ⟨179860634825941279303751027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119907089883960852869167351 179860634825941279303751027)
          ·
            refine ⟨269790952238911918955626541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179860634825941279303751027 269790952238911918955626541)
            ·
              refine ⟨101171607089591969608359953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269790952238911918955626541 101171607089591969608359953)
              ·
                refine ⟨75878705317193977206269965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101171607089591969608359953 75878705317193977206269965)
                ·
                  refine ⟨28454514493947741452351237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75878705317193977206269965 28454514493947741452351237)
                  ·
                    refine ⟨5335221467615201522315857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28454514493947741452351237 5335221467615201522315857)
                    ·
                      refine ⟨4001416100711401141736893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5335221467615201522315857 4001416100711401141736893)
                      ·
                        rfl

theorem cell23_7792730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_7792730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792730 prefixEnd_7792730 := by exact prefixLift 7792730
  have htrace : WordTrace (prefixWord ++ tailWord_7792730) baseStart_7792730 baseEnd_7792730 := by
    simpa [prefixWord, tailWord_7792730, baseEnd_7792730] using wordTrace_append hprefix tailTrace_7792730
  have hstable : (prefixWord ++ tailWord_7792730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792730).length < 2 ^ (prefixWord ++ tailWord_7792730).sum := by decide
  have hdescent : baseEnd_7792730 < baseStart_7792730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792750 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_7792750 : Nat := 118140960795 + 7792750 * 2 ^ 59
def prefixEnd_7792750 : Nat := 4983230072969 + 3 ^ 40 * 7792750 * 2
def baseEnd_7792750 : Nat := 4001426370324491063486801

theorem tailTrace_7792750 : CollatzResearch.WordTrace tailWord_7792750 prefixEnd_7792750 4001426370324491063486801 := by
  unfold tailWord_7792750
  simp only [CollatzResearch.WordTrace]
  refine ⟨35528117814775640073385963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189483295012136747058058469 35528117814775640073385963)
  ·
    refine ⟨53292176722163460110078945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35528117814775640073385963 53292176722163460110078945)
    ·
      refine ⟨39969132541622595082559209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53292176722163460110078945 39969132541622595082559209)
      ·
        refine ⟨29976849406216946311919407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39969132541622595082559209 29976849406216946311919407)
        ·
          refine ⟨44965274109325419467879111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29976849406216946311919407 44965274109325419467879111)
          ·
            refine ⟨67447911163988129201818667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44965274109325419467879111 67447911163988129201818667)
            ·
              refine ⟨101171866745982193802728001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67447911163988129201818667 101171866745982193802728001)
              ·
                refine ⟨75878900059486645352046001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101171866745982193802728001 75878900059486645352046001)
                ·
                  refine ⟨56909175044614984014034501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75878900059486645352046001 56909175044614984014034501)
                  ·
                    refine ⟨10670470320865309502631469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56909175044614984014034501 10670470320865309502631469)
                    ·
                      refine ⟨4001426370324491063486801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10670470320865309502631469 4001426370324491063486801)
                      ·
                        rfl

theorem cell23_7792750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_7792750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792750 prefixEnd_7792750 := by exact prefixLift 7792750
  have htrace : WordTrace (prefixWord ++ tailWord_7792750) baseStart_7792750 baseEnd_7792750 := by
    simpa [prefixWord, tailWord_7792750, baseEnd_7792750] using wordTrace_append hprefix tailTrace_7792750
  have hstable : (prefixWord ++ tailWord_7792750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792750).length < 2 ^ (prefixWord ++ tailWord_7792750).sum := by decide
  have hdescent : baseEnd_7792750 < baseStart_7792750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792753 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 7]
def baseStart_7792753 : Nat := 118140960795 + 7792753 * 2 ^ 59
def prefixEnd_7792753 : Nat := 4983230072969 + 3 ^ 40 * 7792753 * 2
def baseEnd_7792753 : Nat := 444603101196272727972143

theorem tailTrace_7792753 : CollatzResearch.WordTrace tailWord_7792753 prefixEnd_7792753 444603101196272727972143 := by
  unfold tailWord_7792753
  simp only [CollatzResearch.WordTrace]
  refine ⟨284225051937194252099446913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189483367958129501399631275 284225051937194252099446913)
  ·
    refine ⟨213168788952895689074585185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284225051937194252099446913 213168788952895689074585185)
    ·
      refine ⟨159876591714671766805938889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213168788952895689074585185 159876591714671766805938889)
      ·
        refine ⟨119907443786003825104454167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159876591714671766805938889 119907443786003825104454167)
        ·
          refine ⟨179861165679005737656681251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119907443786003825104454167 179861165679005737656681251)
          ·
            refine ⟨269791748518508606485021877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179861165679005737656681251 269791748518508606485021877)
            ·
              refine ⟨25292976423610181857970801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269791748518508606485021877 25292976423610181857970801)
              ·
                refine ⟨18969732317707636393478101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25292976423610181857970801 18969732317707636393478101)
                ·
                  refine ⟨444603101196272727972143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18969732317707636393478101 444603101196272727972143)
                  ·
                    rfl

theorem cell23_7792753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 7].length) (baseStart_7792753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792753 prefixEnd_7792753 := by exact prefixLift 7792753
  have htrace : WordTrace (prefixWord ++ tailWord_7792753) baseStart_7792753 baseEnd_7792753 := by
    simpa [prefixWord, tailWord_7792753, baseEnd_7792753] using wordTrace_append hprefix tailTrace_7792753
  have hstable : (prefixWord ++ tailWord_7792753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792753).length < 2 ^ (prefixWord ++ tailWord_7792753).sum := by decide
  have hdescent : baseEnd_7792753 < baseStart_7792753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792793 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 1, 2, 5]
def baseStart_7792793 : Nat := 118140960795 + 7792793 * 2 ^ 59
def prefixEnd_7792793 : Nat := 4983230072969 + 3 ^ 40 * 7792793 * 2
def baseEnd_7792793 : Nat := 4001448449992634395249103

theorem tailTrace_7792793 : CollatzResearch.WordTrace tailWord_7792793 prefixEnd_7792793 4001448449992634395249103 := by
  unfold tailWord_7792793
  simp only [CollatzResearch.WordTrace]
  refine ⟨284226510857049338930903033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189484340571366225953935355 284226510857049338930903033)
  ·
    refine ⟨213169883142787004198177275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284226510857049338930903033 213169883142787004198177275)
    ·
      refine ⟨319754824714180506297265913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213169883142787004198177275 319754824714180506297265913)
      ·
        refine ⟨239816118535635379722949435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319754824714180506297265913 239816118535635379722949435)
        ·
          refine ⟨359724177803453069584424153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239816118535635379722949435 359724177803453069584424153)
          ·
            refine ⟨269793133352589802188318115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359724177803453069584424153 269793133352589802188318115)
            ·
              refine ⟨404689700028884703282477173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269793133352589802188318115 404689700028884703282477173)
              ·
                refine ⟨37939659377707940932732235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 404689700028884703282477173 37939659377707940932732235)
                ·
                  refine ⟨56909489066561911399098353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37939659377707940932732235 56909489066561911399098353)
                  ·
                    refine ⟨42682116799921433549323765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56909489066561911399098353 42682116799921433549323765)
                    ·
                      refine ⟨4001448449992634395249103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42682116799921433549323765 4001448449992634395249103)
                      ·
                        rfl

theorem cell23_7792793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_7792793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792793 prefixEnd_7792793 := by exact prefixLift 7792793
  have htrace : WordTrace (prefixWord ++ tailWord_7792793) baseStart_7792793 baseEnd_7792793 := by
    simpa [prefixWord, tailWord_7792793, baseEnd_7792793] using wordTrace_append hprefix tailTrace_7792793
  have hstable : (prefixWord ++ tailWord_7792793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792793).length < 2 ^ (prefixWord ++ tailWord_7792793).sum := by decide
  have hdescent : baseEnd_7792793 < baseStart_7792793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792798 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_7792798 : Nat := 118140960795 + 7792798 * 2 ^ 59
def prefixEnd_7792798 : Nat := 4983230072969 + 3 ^ 40 * 7792798 * 2
def baseEnd_7792798 : Nat := 4001451017395906875686581

theorem tailTrace_7792798 : CollatzResearch.WordTrace tailWord_7792798 prefixEnd_7792798 4001451017395906875686581 := by
  unfold tailWord_7792798
  simp only [CollatzResearch.WordTrace]
  refine ⟨35528336652753903098104381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189484462148020816523223365 35528336652753903098104381)
  ·
    refine ⟨13323126244782713661789143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35528336652753903098104381 13323126244782713661789143)
    ·
      refine ⟨19984689367174070492683715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13323126244782713661789143 19984689367174070492683715)
      ·
        refine ⟨29977034050761105739025573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19984689367174070492683715 29977034050761105739025573)
        ·
          refine ⟨5620693884517707326067295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29977034050761105739025573 5620693884517707326067295)
          ·
            refine ⟨8431040826776560989100943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5620693884517707326067295 8431040826776560989100943)
            ·
              refine ⟨12646561240164841483651415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8431040826776560989100943 12646561240164841483651415)
              ·
                refine ⟨18969841860247262225477123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12646561240164841483651415 18969841860247262225477123)
                ·
                  refine ⟨28454762790370893338215685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18969841860247262225477123 28454762790370893338215685)
                  ·
                    refine ⟨5335268023194542500915441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28454762790370893338215685 5335268023194542500915441)
                    ·
                      refine ⟨4001451017395906875686581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5335268023194542500915441 4001451017395906875686581)
                      ·
                        rfl

theorem cell23_7792798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_7792798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792798 prefixEnd_7792798 := by exact prefixLift 7792798
  have htrace : WordTrace (prefixWord ++ tailWord_7792798) baseStart_7792798 baseEnd_7792798 := by
    simpa [prefixWord, tailWord_7792798, baseEnd_7792798] using wordTrace_append hprefix tailTrace_7792798
  have hstable : (prefixWord ++ tailWord_7792798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792798).length < 2 ^ (prefixWord ++ tailWord_7792798).sum := by decide
  have hdescent : baseEnd_7792798 < baseStart_7792798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792821 : List Nat := [1, 3, 3, 4, 1, 2, 1, 3, 5]
def baseStart_7792821 : Nat := 118140960795 + 7792821 * 2 ^ 59
def prefixEnd_7792821 : Nat := 4983230072969 + 3 ^ 40 * 7792821 * 2
def baseEnd_7792821 : Nat := 444606980827884476188775

theorem tailTrace_7792821 : CollatzResearch.WordTrace tailWord_7792821 prefixEnd_7792821 444606980827884476188775 := by
  unfold tailWord_7792821
  simp only [CollatzResearch.WordTrace]
  refine ⟨284227532100947899712922317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189485021400631933141948211 284227532100947899712922317)
  ·
    refine ⟨106585324537855462392345869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284227532100947899712922317 106585324537855462392345869)
    ·
      refine ⟨39969496701695798397129701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106585324537855462392345869 39969496701695798397129701)
      ·
        refine ⟨7494280631567962199461819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39969496701695798397129701 7494280631567962199461819)
        ·
          refine ⟨11241420947351943299192729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7494280631567962199461819 11241420947351943299192729)
          ·
            refine ⟨8431065710513957474394547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11241420947351943299192729 8431065710513957474394547)
            ·
              refine ⟨12646598565770936211591821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8431065710513957474394547 12646598565770936211591821)
              ·
                refine ⟨4742474462164101079346933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12646598565770936211591821 4742474462164101079346933)
                ·
                  refine ⟨444606980827884476188775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4742474462164101079346933 444606980827884476188775)
                  ·
                    rfl

theorem cell23_7792821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 5].length) (baseStart_7792821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792821 prefixEnd_7792821 := by exact prefixLift 7792821
  have htrace : WordTrace (prefixWord ++ tailWord_7792821) baseStart_7792821 baseEnd_7792821 := by
    simpa [prefixWord, tailWord_7792821, baseEnd_7792821] using wordTrace_append hprefix tailTrace_7792821
  have hstable : (prefixWord ++ tailWord_7792821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792821).length < 2 ^ (prefixWord ++ tailWord_7792821).sum := by decide
  have hdescent : baseEnd_7792821 < baseStart_7792821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792834 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_7792834 : Nat := 118140960795 + 7792834 * 2 ^ 59
def prefixEnd_7792834 : Nat := 4983230072969 + 3 ^ 40 * 7792834 * 2
def baseEnd_7792834 : Nat := 1333823167566489578278805

theorem tailTrace_7792834 : CollatzResearch.WordTrace tailWord_7792834 prefixEnd_7792834 1333823167566489578278805 := by
  unfold tailWord_7792834
  simp only [CollatzResearch.WordTrace]
  refine ⟨71057001562475200733286389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189485337499933868622097037 71057001562475200733286389)
  ·
    refine ⟨6661593896482050068745599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71057001562475200733286389 6661593896482050068745599)
    ·
      refine ⟨9992390844723075103118399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6661593896482050068745599 9992390844723075103118399)
      ·
        refine ⟨14988586267084612654677599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9992390844723075103118399 14988586267084612654677599)
        ·
          refine ⟨22482879400626918982016399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14988586267084612654677599 22482879400626918982016399)
          ·
            refine ⟨33724319100940378473024599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22482879400626918982016399 33724319100940378473024599)
            ·
              refine ⟨50586478651410567709536899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33724319100940378473024599 50586478651410567709536899)
              ·
                refine ⟨75879717977115851564305349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50586478651410567709536899 75879717977115851564305349)
                ·
                  refine ⟨14227447120709222168307253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75879717977115851564305349 14227447120709222168307253)
                  ·
                    refine ⟨1333823167566489578278805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14227447120709222168307253 1333823167566489578278805)
                    ·
                      rfl

theorem cell23_7792834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_7792834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792834 prefixEnd_7792834 := by exact prefixLift 7792834
  have htrace : WordTrace (prefixWord ++ tailWord_7792834) baseStart_7792834 baseEnd_7792834 := by
    simpa [prefixWord, tailWord_7792834, baseEnd_7792834] using wordTrace_append hprefix tailTrace_7792834
  have hstable : (prefixWord ++ tailWord_7792834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792834).length < 2 ^ (prefixWord ++ tailWord_7792834).sum := by decide
  have hdescent : baseEnd_7792834 < baseStart_7792834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792843 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 8]
def baseStart_7792843 : Nat := 118140960795 + 7792843 * 2 ^ 59
def prefixEnd_7792843 : Nat := 4983230072969 + 3 ^ 40 * 7792843 * 2
def baseEnd_7792843 : Nat := 444608236002817688847097

theorem tailTrace_7792843 : CollatzResearch.WordTrace tailWord_7792843 prefixEnd_7792843 444608236002817688847097 := by
  unfold tailWord_7792843
  simp only [CollatzResearch.WordTrace]
  refine ⟨284228334506868197470223183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189485556337912131646815455 284228334506868197470223183)
  ·
    refine ⟨426342501760302296205334775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284228334506868197470223183 426342501760302296205334775)
    ·
      refine ⟨639513752640453444308002163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426342501760302296205334775 639513752640453444308002163)
      ·
        refine ⟨959270628960680166462003245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639513752640453444308002163 959270628960680166462003245)
        ·
          refine ⟨359726485860255062423251217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 959270628960680166462003245 359726485860255062423251217)
          ·
            refine ⟨269794864395191296817438413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359726485860255062423251217 269794864395191296817438413)
            ·
              refine ⟨101173074148196736306539405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269794864395191296817438413 101173074148196736306539405)
              ·
                refine ⟨37939902805573776114952277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101173074148196736306539405 37939902805573776114952277)
                ·
                  refine ⟨444608236002817688847097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37939902805573776114952277 444608236002817688847097)
                  ·
                    rfl

theorem cell23_7792843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 8].length) (baseStart_7792843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792843 prefixEnd_7792843 := by exact prefixLift 7792843
  have htrace : WordTrace (prefixWord ++ tailWord_7792843) baseStart_7792843 baseEnd_7792843 := by
    simpa [prefixWord, tailWord_7792843, baseEnd_7792843] using wordTrace_append hprefix tailTrace_7792843
  have hstable : (prefixWord ++ tailWord_7792843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792843).length < 2 ^ (prefixWord ++ tailWord_7792843).sum := by decide
  have hdescent : baseEnd_7792843 < baseStart_7792843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792873 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 2, 9]
def baseStart_7792873 : Nat := 118140960795 + 7792873 * 2 ^ 59
def prefixEnd_7792873 : Nat := 4983230072969 + 3 ^ 40 * 7792873 * 2
def baseEnd_7792873 : Nat := 1333829842814998027416245

theorem tailTrace_7792873 : CollatzResearch.WordTrace tailWord_7792873 prefixEnd_7792873 1333829842814998027416245 := by
  unfold tailWord_7792873
  simp only [CollatzResearch.WordTrace]
  refine ⟨284229428696759512593815273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189486285797839675062543515 284229428696759512593815273)
  ·
    refine ⟨213172071522569634445361455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284229428696759512593815273 213172071522569634445361455)
    ·
      refine ⟨319758107283854451668042183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213172071522569634445361455 319758107283854451668042183)
      ·
        refine ⟨479637160925781677502063275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319758107283854451668042183 479637160925781677502063275)
        ·
          refine ⟨719455741388672516253094913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479637160925781677502063275 719455741388672516253094913)
          ·
            refine ⟨539591806041504387189821185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 719455741388672516253094913 539591806041504387189821185)
            ·
              refine ⟨404693854531128290392365889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539591806041504387189821185 404693854531128290392365889)
              ·
                refine ⟨303520390898346217794274417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404693854531128290392365889 303520390898346217794274417)
                ·
                  refine ⟨227640293173759663345705813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303520390898346217794274417 227640293173759663345705813)
                  ·
                    refine ⟨1333829842814998027416245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 227640293173759663345705813 1333829842814998027416245)
                    ·
                      rfl

theorem cell23_7792873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_7792873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792873 prefixEnd_7792873 := by exact prefixLift 7792873
  have htrace : WordTrace (prefixWord ++ tailWord_7792873) baseStart_7792873 baseEnd_7792873 := by
    simpa [prefixWord, tailWord_7792873, baseEnd_7792873] using wordTrace_append hprefix tailTrace_7792873
  have hstable : (prefixWord ++ tailWord_7792873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792873).length < 2 ^ (prefixWord ++ tailWord_7792873).sum := by decide
  have hdescent : baseEnd_7792873 < baseStart_7792873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792898 : List Nat := [3, 4, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_7792898 : Nat := 118140960795 + 7792898 * 2 ^ 59
def prefixEnd_7792898 : Nat := 4983230072969 + 3 ^ 40 * 7792898 * 2
def baseEnd_7792898 : Nat := 1333834121820452161478707

theorem tailTrace_7792898 : CollatzResearch.WordTrace tailWord_7792898 prefixEnd_7792898 1333834121820452161478707 := by
  unfold tailWord_7792898
  simp only [CollatzResearch.WordTrace]
  refine ⟨71057585130417235465868837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189486893681112627908983565 71057585130417235465868837)
  ·
    refine ⟨13323297211953231649850407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71057585130417235465868837 13323297211953231649850407)
    ·
      refine ⟨19984945817929847474775611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13323297211953231649850407 19984945817929847474775611)
      ·
        refine ⟨29977418726894771212163417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19984945817929847474775611 29977418726894771212163417)
        ·
          refine ⟨22483064045171078409122563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29977418726894771212163417 22483064045171078409122563)
          ·
            refine ⟨33724596067756617613683845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22483064045171078409122563 33724596067756617613683845)
            ·
              refine ⟨6323361762704365802565721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33724596067756617613683845 6323361762704365802565721)
              ·
                refine ⟨4742521322028274351924291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6323361762704365802565721 4742521322028274351924291)
                ·
                  refine ⟨7113781983042411527886437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4742521322028274351924291 7113781983042411527886437)
                  ·
                    refine ⟨1333834121820452161478707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7113781983042411527886437 1333834121820452161478707)
                    ·
                      rfl

theorem cell23_7792898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_7792898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792898 prefixEnd_7792898 := by exact prefixLift 7792898
  have htrace : WordTrace (prefixWord ++ tailWord_7792898) baseStart_7792898 baseEnd_7792898 := by
    simpa [prefixWord, tailWord_7792898, baseEnd_7792898] using wordTrace_append hprefix tailTrace_7792898
  have hstable : (prefixWord ++ tailWord_7792898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792898).length < 2 ^ (prefixWord ++ tailWord_7792898).sum := by decide
  have hdescent : baseEnd_7792898 < baseStart_7792898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792927 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 4]
def baseStart_7792927 : Nat := 118140960795 + 7792927 * 2 ^ 59
def prefixEnd_7792927 : Nat := 4983230072969 + 3 ^ 40 * 7792927 * 2
def baseEnd_7792927 : Nat := 4001517256400336870973487

theorem tailTrace_7792927 : CollatzResearch.WordTrace tailWord_7792927 prefixEnd_7792927 4001517256400336870973487 := by
  unfold tailWord_7792927
  simp only [CollatzResearch.WordTrace]
  refine ⟨284231398238563879816281035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189487598825709253210854023 284231398238563879816281035)
  ·
    refine ⟨426347097357845819724421553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284231398238563879816281035 426347097357845819724421553)
    ·
      refine ⟨319760323018384364793316165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426347097357845819724421553 319760323018384364793316165)
      ·
        refine ⟨59955060565947068398746781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319760323018384364793316165 59955060565947068398746781)
        ·
          refine ⟨22483147712230150649530043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59955060565947068398746781 22483147712230150649530043)
          ·
            refine ⟨33724721568345225974295065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22483147712230150649530043 33724721568345225974295065)
            ·
              refine ⟨25293541176258919480721299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33724721568345225974295065 25293541176258919480721299)
              ·
                refine ⟨37940311764388379221081949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25293541176258919480721299 37940311764388379221081949)
                ·
                  refine ⟨14227616911645642207905731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37940311764388379221081949 14227616911645642207905731)
                  ·
                    refine ⟨21341425367468463311858597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14227616911645642207905731 21341425367468463311858597)
                    ·
                      refine ⟨4001517256400336870973487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21341425367468463311858597 4001517256400336870973487)
                      ·
                        rfl

theorem cell23_7792927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_7792927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792927 prefixEnd_7792927 := by exact prefixLift 7792927
  have htrace : WordTrace (prefixWord ++ tailWord_7792927) baseStart_7792927 baseEnd_7792927 := by
    simpa [prefixWord, tailWord_7792927, baseEnd_7792927] using wordTrace_append hprefix tailTrace_7792927
  have hstable : (prefixWord ++ tailWord_7792927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792927).length < 2 ^ (prefixWord ++ tailWord_7792927).sum := by decide
  have hdescent : baseEnd_7792927 < baseStart_7792927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792941 : List Nat := [1, 5, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_7792941 : Nat := 118140960795 + 7792941 * 2 ^ 59
def prefixEnd_7792941 : Nat := 4983230072969 + 3 ^ 40 * 7792941 * 2
def baseEnd_7792941 : Nat := 1333841481709833272066141

theorem tailTrace_7792941 : CollatzResearch.WordTrace tailWord_7792941 prefixEnd_7792941 1333841481709833272066141 := by
  unfold tailWord_7792941
  simp only [CollatzResearch.WordTrace]
  refine ⟨284231908860513160207290677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189487939240342106804860451 284231908860513160207290677)
  ·
    refine ⟨26646741455673108769433501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284231908860513160207290677 26646741455673108769433501)
    ·
      refine ⟨9992528045877415788537563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26646741455673108769433501 9992528045877415788537563)
      ·
        refine ⟨14988792068816123682806345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9992528045877415788537563 14988792068816123682806345)
        ·
          refine ⟨11241594051612092762104759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14988792068816123682806345 11241594051612092762104759)
          ·
            refine ⟨16862391077418139143157139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11241594051612092762104759 16862391077418139143157139)
            ·
              refine ⟨25293586616127208714735709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16862391077418139143157139 25293586616127208714735709)
              ·
                refine ⟨9485094981047703268025891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25293586616127208714735709 9485094981047703268025891)
                ·
                  refine ⟨14227642471571554902038837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9485094981047703268025891 14227642471571554902038837)
                  ·
                    refine ⟨1333841481709833272066141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14227642471571554902038837 1333841481709833272066141)
                    ·
                      rfl

theorem cell23_7792941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_7792941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792941 prefixEnd_7792941 := by exact prefixLift 7792941
  have htrace : WordTrace (prefixWord ++ tailWord_7792941) baseStart_7792941 baseEnd_7792941 := by
    simpa [prefixWord, tailWord_7792941, baseEnd_7792941] using wordTrace_append hprefix tailTrace_7792941
  have hstable : (prefixWord ++ tailWord_7792941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792941).length < 2 ^ (prefixWord ++ tailWord_7792941).sum := by decide
  have hdescent : baseEnd_7792941 < baseStart_7792941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792954 : List Nat := [3, 1, 1, 1, 4, 2, 3, 2, 2, 4]
def baseStart_7792954 : Nat := 118140960795 + 7792954 * 2 ^ 59
def prefixEnd_7792954 : Nat := 4983230072969 + 3 ^ 40 * 7792954 * 2
def baseEnd_7792954 : Nat := 1333843706792669421778621

theorem tailTrace_7792954 : CollatzResearch.WordTrace tailWord_7792954 prefixEnd_7792954 1333843706792669421778621 := by
  unfold tailWord_7792954
  simp only [CollatzResearch.WordTrace]
  refine ⟨71058095752366515856878479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189488255339644042285009277 71058095752366515856878479)
  ·
    refine ⟨106587143628549773785317719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71058095752366515856878479 106587143628549773785317719)
    ·
      refine ⟨159880715442824660677976579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106587143628549773785317719 159880715442824660677976579)
      ·
        refine ⟨239821073164236991016964869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159880715442824660677976579 239821073164236991016964869)
        ·
          refine ⟨44966451218294435815680913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239821073164236991016964869 44966451218294435815680913)
          ·
            refine ⟨33724838413720826861760685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44966451218294435815680913 33724838413720826861760685)
            ·
              refine ⟨12646814405145310073160257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33724838413720826861760685 12646814405145310073160257)
              ·
                refine ⟨9485110803858982554870193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12646814405145310073160257 9485110803858982554870193)
                ·
                  refine ⟨7113833102894236916152645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9485110803858982554870193 7113833102894236916152645)
                  ·
                    refine ⟨1333843706792669421778621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7113833102894236916152645 1333843706792669421778621)
                    ·
                      rfl

theorem cell23_7792954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_7792954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792954 prefixEnd_7792954 := by exact prefixLift 7792954
  have htrace : WordTrace (prefixWord ++ tailWord_7792954) baseStart_7792954 baseEnd_7792954 := by
    simpa [prefixWord, tailWord_7792954, baseEnd_7792954] using wordTrace_append hprefix tailTrace_7792954
  have hstable : (prefixWord ++ tailWord_7792954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792954).length < 2 ^ (prefixWord ++ tailWord_7792954).sum := by decide
  have hdescent : baseEnd_7792954 < baseStart_7792954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792981 : List Nat := [1, 3, 2, 2, 4, 1, 2, 2, 1, 2, 3]
def baseStart_7792981 : Nat := 118140960795 + 7792981 * 2 ^ 59
def prefixEnd_7792981 : Nat := 4983230072969 + 3 ^ 40 * 7792981 * 2
def baseEnd_7792981 : Nat := 4001544984355679659698239

theorem tailTrace_7792981 : CollatzResearch.WordTrace tailWord_7792981 prefixEnd_7792981 4001544984355679659698239 := by
  unfold tailWord_7792981
  simp only [CollatzResearch.WordTrace]
  refine ⟨284233367780368247038746797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189488911853578831359164531 284233367780368247038746797)
  ·
    refine ⟨106587512917638092639530049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284233367780368247038746797 106587512917638092639530049)
    ·
      refine ⟨79940634688228569479647537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106587512917638092639530049 79940634688228569479647537)
      ·
        refine ⟨59955476016171427109735653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79940634688228569479647537 59955476016171427109735653)
        ·
          refine ⟨11241651753032142583075435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59955476016171427109735653 11241651753032142583075435)
          ·
            refine ⟨16862477629548213874613153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11241651753032142583075435 16862477629548213874613153)
            ·
              refine ⟨12646858222161160405959865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16862477629548213874613153 12646858222161160405959865)
              ·
                refine ⟨9485143666620870304469899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12646858222161160405959865 9485143666620870304469899)
                ·
                  refine ⟨14227715499931305456704849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9485143666620870304469899 14227715499931305456704849)
                  ·
                    refine ⟨10670786624948479092528637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14227715499931305456704849 10670786624948479092528637)
                    ·
                      refine ⟨4001544984355679659698239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10670786624948479092528637 4001544984355679659698239)
                      ·
                        rfl

theorem cell23_7792981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_7792981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792981 prefixEnd_7792981 := by exact prefixLift 7792981
  have htrace : WordTrace (prefixWord ++ tailWord_7792981) baseStart_7792981 baseEnd_7792981 := by
    simpa [prefixWord, tailWord_7792981, baseEnd_7792981] using wordTrace_append hprefix tailTrace_7792981
  have hstable : (prefixWord ++ tailWord_7792981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792981).length < 2 ^ (prefixWord ++ tailWord_7792981).sum := by decide
  have hdescent : baseEnd_7792981 < baseStart_7792981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793038 : List Nat := [4, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2]
def baseStart_7793038 : Nat := 118140960795 + 7793038 * 2 ^ 59
def prefixEnd_7793038 : Nat := 4983230072969 + 3 ^ 40 * 7793038 * 2
def baseEnd_7793038 : Nat := 4001574252752985936685477

theorem tailTrace_7793038 : CollatzResearch.WordTrace tailWord_7793038 prefixEnd_7793038 4001574252752985936685477 := by
  unfold tailWord_7793038
  simp only [CollatzResearch.WordTrace]
  refine ⟨35529430842645218221696471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189490297827441163849047845 35529430842645218221696471)
  ·
    refine ⟨53294146263967827332544707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35529430842645218221696471 53294146263967827332544707)
    ·
      refine ⟨79941219395951740998817061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53294146263967827332544707 79941219395951740998817061)
      ·
        refine ⟨14988978636740951437278199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79941219395951740998817061 14988978636740951437278199)
        ·
          refine ⟨22483467955111427155917299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14988978636740951437278199 22483467955111427155917299)
          ·
            refine ⟨33725201932667140733875949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22483467955111427155917299 33725201932667140733875949)
            ·
              refine ⟨12646950724750177775203481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33725201932667140733875949 12646950724750177775203481)
              ·
                refine ⟨9485213043562633331402611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12646950724750177775203481 9485213043562633331402611)
                ·
                  refine ⟨14227819565343949997103917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9485213043562633331402611 14227819565343949997103917)
                  ·
                    refine ⟨5335432337003981248913969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14227819565343949997103917 5335432337003981248913969)
                    ·
                      refine ⟨4001574252752985936685477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5335432337003981248913969 4001574252752985936685477)
                      ·
                        rfl

theorem cell23_7793038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_7793038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793038 prefixEnd_7793038 := by exact prefixLift 7793038
  have htrace : WordTrace (prefixWord ++ tailWord_7793038) baseStart_7793038 baseEnd_7793038 := by
    simpa [prefixWord, tailWord_7793038, baseEnd_7793038] using wordTrace_append hprefix tailTrace_7793038
  have hstable : (prefixWord ++ tailWord_7793038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793038).length < 2 ^ (prefixWord ++ tailWord_7793038).sum := by decide
  have hdescent : baseEnd_7793038 < baseStart_7793038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793074 : List Nat := [3, 2, 1, 1, 1, 1, 5, 4, 5]
def baseStart_7793074 : Nat := 118140960795 + 7793074 * 2 ^ 59
def prefixEnd_7793074 : Nat := 4983230072969 + 3 ^ 40 * 7793074 * 2
def baseEnd_7793074 : Nat := 444621415339616421759479

theorem tailTrace_7793074 : CollatzResearch.WordTrace tailWord_7793074 prefixEnd_7793074 444621415339616421759479 := by
  unfold tailWord_7793074
  simp only [CollatzResearch.WordTrace]
  refine ⟨71059189942257830980470569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189491173179354215947921517 71059189942257830980470569)
  ·
    refine ⟨53294392456693373235352927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71059189942257830980470569 53294392456693373235352927)
    ·
      refine ⟨79941588685040059853029391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53294392456693373235352927 79941588685040059853029391)
      ·
        refine ⟨119912383027560089779544087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79941588685040059853029391 119912383027560089779544087)
        ·
          refine ⟨179868574541340134669316131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119912383027560089779544087 179868574541340134669316131)
          ·
            refine ⟨269802861812010202003974197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179868574541340134669316131 269802861812010202003974197)
            ·
              refine ⟨25294018294875956437872581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269802861812010202003974197 25294018294875956437872581)
              ·
                refine ⟨4742628430289241832101109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25294018294875956437872581 4742628430289241832101109)
                ·
                  refine ⟨444621415339616421759479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4742628430289241832101109 444621415339616421759479)
                  ·
                    rfl

theorem cell23_7793074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_7793074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793074 prefixEnd_7793074 := by exact prefixLift 7793074
  have htrace : WordTrace (prefixWord ++ tailWord_7793074) baseStart_7793074 baseEnd_7793074 := by
    simpa [prefixWord, tailWord_7793074, baseEnd_7793074] using wordTrace_append hprefix tailTrace_7793074
  have hstable : (prefixWord ++ tailWord_7793074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793074).length < 2 ^ (prefixWord ++ tailWord_7793074).sum := by decide
  have hdescent : baseEnd_7793074 < baseStart_7793074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793084 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_7793084 : Nat := 118140960795 + 7793084 * 2 ^ 59
def prefixEnd_7793084 : Nat := 4983230072969 + 3 ^ 40 * 7793084 * 2
def baseEnd_7793084 : Nat := 4001597872863092756710265

theorem tailTrace_7793084 : CollatzResearch.WordTrace tailWord_7793084 prefixEnd_7793084 4001597872863092756710265 := by
  unfold tailWord_7793084
  simp only [CollatzResearch.WordTrace]
  refine ⟨142118562249497547814873153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189491416332663397086497537 142118562249497547814873153)
  ·
    refine ⟨106588921687123160861154865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142118562249497547814873153 106588921687123160861154865)
    ·
      refine ⟨79941691265342370645866149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106588921687123160861154865 79941691265342370645866149)
      ·
        refine ⟨14989067112251694496099903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79941691265342370645866149 14989067112251694496099903)
        ·
          refine ⟨22483600668377541744149855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14989067112251694496099903 22483600668377541744149855)
          ·
            refine ⟨33725401002566312616224783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22483600668377541744149855 33725401002566312616224783)
            ·
              refine ⟨50588101503849468924337175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33725401002566312616224783 50588101503849468924337175)
              ·
                refine ⟨75882152255774203386505763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50588101503849468924337175 75882152255774203386505763)
                ·
                  refine ⟨113823228383661305079758645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75882152255774203386505763 113823228383661305079758645)
                  ·
                    refine ⟨10670927660968247351227373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113823228383661305079758645 10670927660968247351227373)
                    ·
                      refine ⟨4001597872863092756710265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10670927660968247351227373 4001597872863092756710265)
                      ·
                        rfl

theorem cell23_7793084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_7793084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793084 prefixEnd_7793084 := by exact prefixLift 7793084
  have htrace : WordTrace (prefixWord ++ tailWord_7793084) baseStart_7793084 baseEnd_7793084 := by
    simpa [prefixWord, tailWord_7793084, baseEnd_7793084] using wordTrace_append hprefix tailTrace_7793084
  have hstable : (prefixWord ++ tailWord_7793084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793084).length < 2 ^ (prefixWord ++ tailWord_7793084).sum := by decide
  have hdescent : baseEnd_7793084 < baseStart_7793084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793137 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_7793137 : Nat := 118140960795 + 7793137 * 2 ^ 59
def prefixEnd_7793137 : Nat := 4983230072969 + 3 ^ 40 * 7793137 * 2
def baseEnd_7793137 : Nat := 4001625087337781049347521

theorem tailTrace_7793137 : CollatzResearch.WordTrace tailWord_7793137 prefixEnd_7793137 4001625087337781049347521 := by
  unfold tailWord_7793137
  simp only [CollatzResearch.WordTrace]
  refine ⟨284239057567803085681425665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189492705045202057120950443 284239057567803085681425665)
  ·
    refine ⟨213179293175852314261069249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284239057567803085681425665 213179293175852314261069249)
    ·
      refine ⟨159884469881889235695801937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213179293175852314261069249 159884469881889235695801937)
      ·
        refine ⟨119913352411416926771851453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159884469881889235695801937 119913352411416926771851453)
        ·
          refine ⟨44967507154281347539444295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119913352411416926771851453 44967507154281347539444295)
          ·
            refine ⟨67451260731422021309166443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44967507154281347539444295 67451260731422021309166443)
            ·
              refine ⟨101176891097133031963749665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67451260731422021309166443 101176891097133031963749665)
              ·
                refine ⟨75882668322849773972812249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101176891097133031963749665 75882668322849773972812249)
                ·
                  refine ⟨56912001242137330479609187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75882668322849773972812249 56912001242137330479609187)
                  ·
                    refine ⟨85368001863205995719413781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56912001242137330479609187 85368001863205995719413781)
                    ·
                      refine ⟨4001625087337781049347521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85368001863205995719413781 4001625087337781049347521)
                      ·
                        rfl

theorem cell23_7793137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_7793137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793137 prefixEnd_7793137 := by exact prefixLift 7793137
  have htrace : WordTrace (prefixWord ++ tailWord_7793137) baseStart_7793137 baseEnd_7793137 := by
    simpa [prefixWord, tailWord_7793137, baseEnd_7793137] using wordTrace_append hprefix tailTrace_7793137
  have hstable : (prefixWord ++ tailWord_7793137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793137).length < 2 ^ (prefixWord ++ tailWord_7793137).sum := by decide
  have hdescent : baseEnd_7793137 < baseStart_7793137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793224 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 6, 4]
def baseStart_7793224 : Nat := 118140960795 + 7793224 * 2 ^ 59
def prefixEnd_7793224 : Nat := 4983230072969 + 3 ^ 40 * 7793224 * 2
def baseEnd_7793224 : Nat := 1333889920051574069653207

theorem tailTrace_7793224 : CollatzResearch.WordTrace tailWord_7793224 prefixEnd_7793224 1333889920051574069653207 := by
  unfold tailWord_7793224
  simp only [CollatzResearch.WordTrace]
  refine ⟨142121115359243949769921363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189494820478991933026561817 142121115359243949769921363)
  ·
    refine ⟨213181673038865924654882045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142121115359243949769921363 213181673038865924654882045)
    ·
      refine ⟨79943127389574721745580767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213181673038865924654882045 79943127389574721745580767)
      ·
        refine ⟨119914691084362082618371151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79943127389574721745580767 119914691084362082618371151)
        ·
          refine ⟨179872036626543123927556727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119914691084362082618371151 179872036626543123927556727)
          ·
            refine ⟨269808054939814685891335091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179872036626543123927556727 269808054939814685891335091)
            ·
              refine ⟨404712082409722028837002637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269808054939814685891335091 404712082409722028837002637)
              ·
                refine ⟨151767030903645760813875989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404712082409722028837002637 151767030903645760813875989)
                ·
                  refine ⟨7114079573608395038150437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151767030903645760813875989 7114079573608395038150437)
                  ·
                    refine ⟨1333889920051574069653207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7114079573608395038150437 1333889920051574069653207)
                    ·
                      rfl

theorem cell23_7793224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_7793224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793224 prefixEnd_7793224 := by exact prefixLift 7793224
  have htrace : WordTrace (prefixWord ++ tailWord_7793224) baseStart_7793224 baseEnd_7793224 := by
    simpa [prefixWord, tailWord_7793224, baseEnd_7793224] using wordTrace_append hprefix tailTrace_7793224
  have hstable : (prefixWord ++ tailWord_7793224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793224).length < 2 ^ (prefixWord ++ tailWord_7793224).sum := by decide
  have hdescent : baseEnd_7793224 < baseStart_7793224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793261 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_7793261 : Nat := 118140960795 + 7793261 * 2 ^ 59
def prefixEnd_7793261 : Nat := 4983230072969 + 3 ^ 40 * 7793261 * 2
def baseEnd_7793261 : Nat := 4001688758938938564196951

theorem tailTrace_7793261 : CollatzResearch.WordTrace tailWord_7793261 prefixEnd_7793261 4001688758938938564196951 := by
  unfold tailWord_7793261
  simp only [CollatzResearch.WordTrace]
  refine ⟨284243580219353854858939637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189495720146235903239293091 284243580219353854858939637)
  ·
    refine ⟨26647835645564423893025591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284243580219353854858939637 26647835645564423893025591)
    ·
      refine ⟨39971753468346635839538387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26647835645564423893025591 39971753468346635839538387)
      ·
        refine ⟨59957630202519953759307581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39971753468346635839538387 59957630202519953759307581)
        ·
          refine ⟨22484111325944982659740343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59957630202519953759307581 22484111325944982659740343)
          ·
            refine ⟨33726166988917473989610515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22484111325944982659740343 33726166988917473989610515)
            ·
              refine ⟨50589250483376210984415773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33726166988917473989610515 50589250483376210984415773)
              ·
                refine ⟨18970968931266079119155915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50589250483376210984415773 18970968931266079119155915)
                ·
                  refine ⟨28456453396899118678733873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18970968931266079119155915 28456453396899118678733873)
                  ·
                    refine ⟨21342340047674339009050405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28456453396899118678733873 21342340047674339009050405)
                    ·
                      refine ⟨4001688758938938564196951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21342340047674339009050405 4001688758938938564196951)
                      ·
                        rfl

theorem cell23_7793261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_7793261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793261 prefixEnd_7793261 := by exact prefixLift 7793261
  have htrace : WordTrace (prefixWord ++ tailWord_7793261) baseStart_7793261 baseEnd_7793261 := by
    simpa [prefixWord, tailWord_7793261, baseEnd_7793261] using wordTrace_append hprefix tailTrace_7793261
  have hstable : (prefixWord ++ tailWord_7793261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793261).length < 2 ^ (prefixWord ++ tailWord_7793261).sum := by decide
  have hdescent : baseEnd_7793261 < baseStart_7793261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793281 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_7793281 : Nat := 118140960795 + 7793281 * 2 ^ 59
def prefixEnd_7793281 : Nat := 4983230072969 + 3 ^ 40 * 7793281 * 2
def baseEnd_7793281 : Nat := 4001699028552028485946859

theorem tailTrace_7793281 : CollatzResearch.WordTrace tailWord_7793281 prefixEnd_7793281 4001699028552028485946859 := by
  unfold tailWord_7793281
  simp only [CollatzResearch.WordTrace]
  refine ⟨284244309679281398274667697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189496206452854265516445131 284244309679281398274667697)
  ·
    refine ⟨213183232259461048706000773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284244309679281398274667697 213183232259461048706000773)
    ·
      refine ⟨39971856048648946632375145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213183232259461048706000773 39971856048648946632375145)
      ·
        refine ⟨29978892036486709974281359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39971856048648946632375145 29978892036486709974281359)
        ·
          refine ⟨44968338054730064961422039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29978892036486709974281359 44968338054730064961422039)
          ·
            refine ⟨67452507082095097442133059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44968338054730064961422039 67452507082095097442133059)
            ·
              refine ⟨101178760623142646163199589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67452507082095097442133059 101178760623142646163199589)
              ·
                refine ⟨18971017616839246155599923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101178760623142646163199589 18971017616839246155599923)
                ·
                  refine ⟨28456526425258869233399885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18971017616839246155599923 28456526425258869233399885)
                  ·
                    refine ⟨10671197409472075962524957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28456526425258869233399885 10671197409472075962524957)
                    ·
                      refine ⟨4001699028552028485946859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10671197409472075962524957 4001699028552028485946859)
                      ·
                        rfl

theorem cell23_7793281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_7793281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793281 prefixEnd_7793281 := by exact prefixLift 7793281
  have htrace : WordTrace (prefixWord ++ tailWord_7793281) baseStart_7793281 baseEnd_7793281 := by
    simpa [prefixWord, tailWord_7793281, baseEnd_7793281] using wordTrace_append hprefix tailTrace_7793281
  have hstable : (prefixWord ++ tailWord_7793281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793281).length < 2 ^ (prefixWord ++ tailWord_7793281).sum := by decide
  have hdescent : baseEnd_7793281 < baseStart_7793281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793285 : List Nat := [1, 3, 1, 1, 4, 4, 2, 1, 1, 2, 3]
def baseStart_7793285 : Nat := 118140960795 + 7793285 * 2 ^ 59
def prefixEnd_7793285 : Nat := 4983230072969 + 3 ^ 40 * 7793285 * 2
def baseEnd_7793285 : Nat := 4001701082474646470296841

theorem tailTrace_7793285 : CollatzResearch.WordTrace tailWord_7793285 prefixEnd_7793285 4001701082474646470296841 := by
  unfold tailWord_7793285
  simp only [CollatzResearch.WordTrace]
  refine ⟨284244455571266906957813309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189496303714177937971875539 284244455571266906957813309)
  ·
    refine ⟨106591670839225090109179991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284244455571266906957813309 106591670839225090109179991)
    ·
      refine ⟨159887506258837635163769987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106591670839225090109179991 159887506258837635163769987)
      ·
        refine ⟨239831259388256452745654981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159887506258837635163769987 239831259388256452745654981)
        ·
          refine ⟨44968361135298084889810309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239831259388256452745654981 44968361135298084889810309)
          ·
            refine ⟨8431567712868390916839433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44968361135298084889810309 8431567712868390916839433)
            ·
              refine ⟨6323675784651293187629575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8431567712868390916839433 6323675784651293187629575)
              ·
                refine ⟨9485513676976939781444363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6323675784651293187629575 9485513676976939781444363)
                ·
                  refine ⟨14228270515465409672166545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9485513676976939781444363 14228270515465409672166545)
                  ·
                    refine ⟨10671202886599057254124909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14228270515465409672166545 10671202886599057254124909)
                    ·
                      refine ⟨4001701082474646470296841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10671202886599057254124909 4001701082474646470296841)
                      ·
                        rfl

theorem cell23_7793285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 1, 2, 3].length) (baseStart_7793285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793285 prefixEnd_7793285 := by exact prefixLift 7793285
  have htrace : WordTrace (prefixWord ++ tailWord_7793285) baseStart_7793285 baseEnd_7793285 := by
    simpa [prefixWord, tailWord_7793285, baseEnd_7793285] using wordTrace_append hprefix tailTrace_7793285
  have hstable : (prefixWord ++ tailWord_7793285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793285).length < 2 ^ (prefixWord ++ tailWord_7793285).sum := by decide
  have hdescent : baseEnd_7793285 < baseStart_7793285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793291 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 5, 3, 2]
def baseStart_7793291 : Nat := 118140960795 + 7793291 * 2 ^ 59
def prefixEnd_7793291 : Nat := 4983230072969 + 3 ^ 40 * 7793291 * 2
def baseEnd_7793291 : Nat := 4001704163358573446821813

theorem tailTrace_7793291 : CollatzResearch.WordTrace tailWord_7793291 prefixEnd_7793291 4001704163358573446821813 := by
  unfold tailWord_7793291
  simp only [CollatzResearch.WordTrace]
  refine ⟨284244674409245169982531727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189496449606163446655021151 284244674409245169982531727)
  ·
    refine ⟨426367011613867754973797591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284244674409245169982531727 426367011613867754973797591)
    ·
      refine ⟨639550517420801632460696387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426367011613867754973797591 639550517420801632460696387)
      ·
        refine ⟨959325776131202448691044581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639550517420801632460696387 959325776131202448691044581)
        ·
          refine ⟨179873583024600459129570859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 959325776131202448691044581 179873583024600459129570859)
          ·
            refine ⟨269810374536900688694356289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179873583024600459129570859 269810374536900688694356289)
            ·
              refine ⟨202357780902675516520767217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269810374536900688694356289 202357780902675516520767217)
              ·
                refine ⟨151768335677006637390575413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202357780902675516520767217 151768335677006637390575413)
                ·
                  refine ⟨14228281469719372255366445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151768335677006637390575413 14228281469719372255366445)
                  ·
                    refine ⟨5335605551144764595762417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14228281469719372255366445 5335605551144764595762417)
                    ·
                      refine ⟨4001704163358573446821813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5335605551144764595762417 4001704163358573446821813)
                      ·
                        rfl

theorem cell23_7793291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 3, 2].length) (baseStart_7793291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793291 prefixEnd_7793291 := by exact prefixLift 7793291
  have htrace : WordTrace (prefixWord ++ tailWord_7793291) baseStart_7793291 baseEnd_7793291 := by
    simpa [prefixWord, tailWord_7793291, baseEnd_7793291] using wordTrace_append hprefix tailTrace_7793291
  have hstable : (prefixWord ++ tailWord_7793291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793291).length < 2 ^ (prefixWord ++ tailWord_7793291).sum := by decide
  have hdescent : baseEnd_7793291 < baseStart_7793291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793322 : List Nat := [3, 1, 5, 2, 2, 1, 2, 7]
def baseStart_7793322 : Nat := 118140960795 + 7793322 * 2 ^ 59
def prefixEnd_7793322 : Nat := 4983230072969 + 3 ^ 40 * 7793322 * 2
def baseEnd_7793322 : Nat := 148211854861439363908673

theorem tailTrace_7793322 : CollatzResearch.WordTrace tailWord_7793322 prefixEnd_7793322 148211854861439363908673 := by
  unfold tailWord_7793322
  simp only [CollatzResearch.WordTrace]
  refine ⟨71061451268033215569227555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189497203381421908184606813 71061451268033215569227555)
  ·
    refine ⟨106592176902049823353841333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71061451268033215569227555 106592176902049823353841333)
    ·
      refine ⟨9993016584567170939422625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106592176902049823353841333 9993016584567170939422625)
      ·
        refine ⟨7494762438425378204566969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9993016584567170939422625 7494762438425378204566969)
        ·
          refine ⟨5621071828819033653425227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7494762438425378204566969 5621071828819033653425227)
          ·
            refine ⟨8431607743228550480137841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621071828819033653425227 8431607743228550480137841)
            ·
              refine ⟨6323705807421412860103381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8431607743228550480137841 6323705807421412860103381)
              ·
                refine ⟨148211854861439363908673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6323705807421412860103381 148211854861439363908673)
                ·
                  rfl

theorem cell23_7793322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 7].length) (baseStart_7793322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793322 prefixEnd_7793322 := by exact prefixLift 7793322
  have htrace : WordTrace (prefixWord ++ tailWord_7793322) baseStart_7793322 baseEnd_7793322 := by
    simpa [prefixWord, tailWord_7793322, baseEnd_7793322] using wordTrace_append hprefix tailTrace_7793322
  have hstable : (prefixWord ++ tailWord_7793322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793322).length < 2 ^ (prefixWord ++ tailWord_7793322).sum := by decide
  have hdescent : baseEnd_7793322 < baseStart_7793322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793325 : List Nat := [1, 5, 2, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_7793325 : Nat := 118140960795 + 7793325 * 2 ^ 59
def prefixEnd_7793325 : Nat := 4983230072969 + 3 ^ 40 * 7793325 * 2
def baseEnd_7793325 : Nat := 4001721621700826313796657

theorem tailTrace_7793325 : CollatzResearch.WordTrace tailWord_7793325 prefixEnd_7793325 4001721621700826313796657 := by
  unfold tailWord_7793325
  simp only [CollatzResearch.WordTrace]
  refine ⟨284245914491121993789269429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189497276327414662526179619 284245914491121993789269429)
  ·
    refine ⟨26648054483542686917744009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284245914491121993789269429 26648054483542686917744009)
    ·
      refine ⟨19986040862657015188308007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26648054483542686917744009 19986040862657015188308007)
      ·
        refine ⟨29979061293985522782462011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19986040862657015188308007 29979061293985522782462011)
        ·
          refine ⟨44968591940978284173693017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29979061293985522782462011 44968591940978284173693017)
          ·
            refine ⟨33726443955733713130269763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44968591940978284173693017 33726443955733713130269763)
            ·
              refine ⟨50589665933600569695404645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33726443955733713130269763 50589665933600569695404645)
              ·
                refine ⟨9485562362550106817888371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50589665933600569695404645 9485562362550106817888371)
                ·
                  refine ⟨14228343543825160226832557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9485562362550106817888371 14228343543825160226832557)
                  ·
                    refine ⟨5335628828934435085062209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14228343543825160226832557 5335628828934435085062209)
                    ·
                      refine ⟨4001721621700826313796657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5335628828934435085062209 4001721621700826313796657)
                      ·
                        rfl

theorem cell23_7793325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_7793325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793325 prefixEnd_7793325 := by exact prefixLift 7793325
  have htrace : WordTrace (prefixWord ++ tailWord_7793325) baseStart_7793325 baseEnd_7793325 := by
    simpa [prefixWord, tailWord_7793325, baseEnd_7793325] using wordTrace_append hprefix tailTrace_7793325
  have hstable : (prefixWord ++ tailWord_7793325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793325).length < 2 ^ (prefixWord ++ tailWord_7793325).sum := by decide
  have hdescent : baseEnd_7793325 < baseStart_7793325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793338 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2]
def baseStart_7793338 : Nat := 118140960795 + 7793338 * 2 ^ 59
def prefixEnd_7793338 : Nat := 4983230072969 + 3 ^ 40 * 7793338 * 2
def baseEnd_7793338 : Nat := 4001728296949334762934097

theorem tailTrace_7793338 : CollatzResearch.WordTrace tailWord_7793338 prefixEnd_7793338 4001728296949334762934097 := by
  unfold tailWord_7793338
  simp only [CollatzResearch.WordTrace]
  refine ⟨71061597160018724252373167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189497592426716598006328445 71061597160018724252373167)
  ·
    refine ⟨106592395740028086378559751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71061597160018724252373167 106592395740028086378559751)
    ·
      refine ⟨159888593610042129567839627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106592395740028086378559751 159888593610042129567839627)
      ·
        refine ⟨239832890415063194351759441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159888593610042129567839627 239832890415063194351759441)
        ·
          refine ⟨179874667811297395763819581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239832890415063194351759441 179874667811297395763819581)
          ·
            refine ⟨67453000429236523411432343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179874667811297395763819581 67453000429236523411432343)
            ·
              refine ⟨101179500643854785117148515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67453000429236523411432343 101179500643854785117148515)
              ·
                refine ⟨151769250965782177675722773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101179500643854785117148515 151769250965782177675722773)
                ·
                  refine ⟨7114183639021039578549505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151769250965782177675722773 7114183639021039578549505)
                  ·
                    refine ⟨5335637729265779683912129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7114183639021039578549505 5335637729265779683912129)
                    ·
                      refine ⟨4001728296949334762934097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5335637729265779683912129 4001728296949334762934097)
                      ·
                        rfl

theorem cell23_7793338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2].length) (baseStart_7793338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793338 prefixEnd_7793338 := by exact prefixLift 7793338
  have htrace : WordTrace (prefixWord ++ tailWord_7793338) baseStart_7793338 baseEnd_7793338 := by
    simpa [prefixWord, tailWord_7793338, baseEnd_7793338] using wordTrace_append hprefix tailTrace_7793338
  have hstable : (prefixWord ++ tailWord_7793338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793338).length < 2 ^ (prefixWord ++ tailWord_7793338).sum := by decide
  have hdescent : baseEnd_7793338 < baseStart_7793338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793341 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_7793341 : Nat := 118140960795 + 7793341 * 2 ^ 59
def prefixEnd_7793341 : Nat := 4983230072969 + 3 ^ 40 * 7793341 * 2
def baseEnd_7793341 : Nat := 4001729837391298251196583

theorem tailTrace_7793341 : CollatzResearch.WordTrace tailWord_7793341 prefixEnd_7793341 4001729837391298251196583 := by
  unfold tailWord_7793341
  simp only [CollatzResearch.WordTrace]
  refine ⟨284246498059064028521851877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189497665372709352347901251 284246498059064028521851877)
  ·
    refine ⟨53296218386074505347847227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284246498059064028521851877 53296218386074505347847227)
    ·
      refine ⟨79944327579111758021770841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53296218386074505347847227 79944327579111758021770841)
      ·
        refine ⟨59958245684333818516328131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79944327579111758021770841 59958245684333818516328131)
        ·
          refine ⟨89937368526500727774492197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59958245684333818516328131 89937368526500727774492197)
          ·
            refine ⟨16863256598718886457717287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89937368526500727774492197 16863256598718886457717287)
            ·
              refine ⟨25294884898078329686575931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16863256598718886457717287 25294884898078329686575931)
              ·
                refine ⟨37942327347117494529863897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25294884898078329686575931 37942327347117494529863897)
                ·
                  refine ⟨28456745510338120897397923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37942327347117494529863897 28456745510338120897397923)
                  ·
                    refine ⟨42685118265507181346096885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28456745510338120897397923 42685118265507181346096885)
                    ·
                      refine ⟨4001729837391298251196583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42685118265507181346096885 4001729837391298251196583)
                      ·
                        rfl

theorem cell23_7793341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_7793341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793341 prefixEnd_7793341 := by exact prefixLift 7793341
  have htrace : WordTrace (prefixWord ++ tailWord_7793341) baseStart_7793341 baseEnd_7793341 := by
    simpa [prefixWord, tailWord_7793341, baseEnd_7793341] using wordTrace_append hprefix tailTrace_7793341
  have hstable : (prefixWord ++ tailWord_7793341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793341).length < 2 ^ (prefixWord ++ tailWord_7793341).sum := by decide
  have hdescent : baseEnd_7793341 < baseStart_7793341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793391 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 2, 5]
def baseStart_7793391 : Nat := 118140960795 + 7793391 * 2 ^ 59
def prefixEnd_7793391 : Nat := 4983230072969 + 3 ^ 40 * 7793391 * 2
def baseEnd_7793391 : Nat := 1333918503808007685190451

theorem tailTrace_7793391 : CollatzResearch.WordTrace tailWord_7793391 prefixEnd_7793391 1333918503808007685190451 := by
  unfold tailWord_7793391
  simp only [CollatzResearch.WordTrace]
  refine ⟨284248321708882887061172027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189498881139255258040781351 284248321708882887061172027)
  ·
    refine ⟨426372482563324330591758041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284248321708882887061172027 426372482563324330591758041)
    ·
      refine ⟨319779361922493247943818531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426372482563324330591758041 319779361922493247943818531)
      ·
        refine ⟨479669042883739871915727797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319779361922493247943818531 479669042883739871915727797)
        ·
          refine ⟨44968972770350612992099481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 479669042883739871915727797 44968972770350612992099481)
          ·
            refine ⟨33726729577762959744074611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44968972770350612992099481 33726729577762959744074611)
            ·
              refine ⟨50590094366644439616111917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33726729577762959744074611 50590094366644439616111917)
              ·
                refine ⟨18971285387491664856041969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50590094366644439616111917 18971285387491664856041969)
                ·
                  refine ⟨14228464040618748642031477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18971285387491664856041969 14228464040618748642031477)
                  ·
                    refine ⟨1333918503808007685190451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14228464040618748642031477 1333918503808007685190451)
                    ·
                      rfl

theorem cell23_7793391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 5].length) (baseStart_7793391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793391 prefixEnd_7793391 := by exact prefixLift 7793391
  have htrace : WordTrace (prefixWord ++ tailWord_7793391) baseStart_7793391 baseEnd_7793391 := by
    simpa [prefixWord, tailWord_7793391, baseEnd_7793391] using wordTrace_append hprefix tailTrace_7793391
  have hstable : (prefixWord ++ tailWord_7793391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793391).length < 2 ^ (prefixWord ++ tailWord_7793391).sum := by decide
  have hdescent : baseEnd_7793391 < baseStart_7793391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793448 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_7793448 : Nat := 118140960795 + 7793448 * 2 ^ 59
def prefixEnd_7793448 : Nat := 4983230072969 + 3 ^ 40 * 7793448 * 2
def baseEnd_7793448 : Nat := 4001784779821329332558591

theorem tailTrace_7793448 : CollatzResearch.WordTrace tailWord_7793448 prefixEnd_7793448 4001784779821329332558591 := by
  unfold tailWord_7793448
  simp only [CollatzResearch.WordTrace]
  refine ⟨142125200334838192897998499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189500267113117590530664665 142125200334838192897998499)
  ·
    refine ⟨213187800502257289346997749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142125200334838192897998499 213187800502257289346997749)
    ·
      refine ⟨19986356297086620876281039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213187800502257289346997749 19986356297086620876281039)
      ·
        refine ⟨29979534445629931314421559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19986356297086620876281039 29979534445629931314421559)
        ·
          refine ⟨44969301668444896971632339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29979534445629931314421559 44969301668444896971632339)
          ·
            refine ⟨67453952502667345457448509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44969301668444896971632339 67453952502667345457448509)
            ·
              refine ⟨25295232188500254546543191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67453952502667345457448509 25295232188500254546543191)
              ·
                refine ⟨37942848282750381819814787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25295232188500254546543191 37942848282750381819814787)
                ·
                  refine ⟨56914272424125572729722181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37942848282750381819814787 56914272424125572729722181)
                  ·
                    refine ⟨10671426079523544886822909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56914272424125572729722181 10671426079523544886822909)
                    ·
                      refine ⟨4001784779821329332558591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10671426079523544886822909 4001784779821329332558591)
                      ·
                        rfl

theorem cell23_7793448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_7793448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793448 prefixEnd_7793448 := by exact prefixLift 7793448
  have htrace : WordTrace (prefixWord ++ tailWord_7793448) baseStart_7793448 baseEnd_7793448 := by
    simpa [prefixWord, tailWord_7793448, baseEnd_7793448] using wordTrace_append hprefix tailTrace_7793448
  have hstable : (prefixWord ++ tailWord_7793448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793448).length < 2 ^ (prefixWord ++ tailWord_7793448).sum := by decide
  have hdescent : baseEnd_7793448 < baseStart_7793448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793471 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 6]
def baseStart_7793471 : Nat := 118140960795 + 7793471 * 2 ^ 59
def prefixEnd_7793471 : Nat := 4983230072969 + 3 ^ 40 * 7793471 * 2
def baseEnd_7793471 : Nat := 4001796589876382742570985

theorem tailTrace_7793471 : CollatzResearch.WordTrace tailWord_7793471 prefixEnd_7793471 4001796589876382742570985 := by
  unfold tailWord_7793471
  simp only [CollatzResearch.WordTrace]
  refine ⟨284251239548593060724084267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189500826365728707149389511 284251239548593060724084267)
  ·
    refine ⟨426376859322889591086126401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284251239548593060724084267 426376859322889591086126401)
    ·
      refine ⟨319782644492167193314594801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426376859322889591086126401 319782644492167193314594801)
      ·
        refine ⟨239836983369125394985946101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319782644492167193314594801 239836983369125394985946101)
        ·
          refine ⟨22484717190855505779932447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239836983369125394985946101 22484717190855505779932447)
          ·
            refine ⟨33727075786283258669898671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22484717190855505779932447 33727075786283258669898671)
            ·
              refine ⟨50590613679424888004848007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33727075786283258669898671 50590613679424888004848007)
              ·
                refine ⟨75885920519137332007272011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50590613679424888004848007 75885920519137332007272011)
                ·
                  refine ⟨113828880778705998010908017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75885920519137332007272011 113828880778705998010908017)
                  ·
                    refine ⟨85371660584029498508181013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113828880778705998010908017 85371660584029498508181013)
                    ·
                      refine ⟨4001796589876382742570985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85371660584029498508181013 4001796589876382742570985)
                      ·
                        rfl

theorem cell23_7793471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_7793471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793471 prefixEnd_7793471 := by exact prefixLift 7793471
  have htrace : WordTrace (prefixWord ++ tailWord_7793471) baseStart_7793471 baseEnd_7793471 := by
    simpa [prefixWord, tailWord_7793471, baseEnd_7793471] using wordTrace_append hprefix tailTrace_7793471
  have hstable : (prefixWord ++ tailWord_7793471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793471).length < 2 ^ (prefixWord ++ tailWord_7793471).sum := by decide
  have hdescent : baseEnd_7793471 < baseStart_7793471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793488 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 1, 5, 2]
def baseStart_7793488 : Nat := 118140960795 + 7793488 * 2 ^ 59
def prefixEnd_7793488 : Nat := 4983230072969 + 3 ^ 40 * 7793488 * 2
def baseEnd_7793488 : Nat := 4001805319047509176058407

theorem tailTrace_7793488 : CollatzResearch.WordTrace tailWord_7793488 prefixEnd_7793488 4001805319047509176058407 := by
  unfold tailWord_7793488
  simp only [CollatzResearch.WordTrace]
  refine ⟨142125929794765736313726559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189501239726354315084968745 142125929794765736313726559)
  ·
    refine ⟨213188894692148604470589839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142125929794765736313726559 213188894692148604470589839)
    ·
      refine ⟨319783342038222906705884759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213188894692148604470589839 319783342038222906705884759)
      ·
        refine ⟨479675013057334360058827139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319783342038222906705884759 479675013057334360058827139)
        ·
          refine ⟨719512519586001540088240709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479675013057334360058827139 719512519586001540088240709)
          ·
            refine ⟨134908597422375288766545133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 719512519586001540088240709 134908597422375288766545133)
            ·
              refine ⟨50590724033390733287454425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134908597422375288766545133 50590724033390733287454425)
              ·
                refine ⟨37943043025043049965590819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50590724033390733287454425 37943043025043049965590819)
                ·
                  refine ⟨56914564537564574948386229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37943043025043049965590819 56914564537564574948386229)
                  ·
                    refine ⟨5335740425396678901411209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56914564537564574948386229 5335740425396678901411209)
                    ·
                      refine ⟨4001805319047509176058407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5335740425396678901411209 4001805319047509176058407)
                      ·
                        rfl

theorem cell23_7793488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 5, 2].length) (baseStart_7793488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793488 prefixEnd_7793488 := by exact prefixLift 7793488
  have htrace : WordTrace (prefixWord ++ tailWord_7793488) baseStart_7793488 baseEnd_7793488 := by
    simpa [prefixWord, tailWord_7793488, baseEnd_7793488] using wordTrace_append hprefix tailTrace_7793488
  have hstable : (prefixWord ++ tailWord_7793488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793488).length < 2 ^ (prefixWord ++ tailWord_7793488).sum := by decide
  have hdescent : baseEnd_7793488 < baseStart_7793488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793495 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 3, 1, 3]
def baseStart_7793495 : Nat := 118140960795 + 7793495 * 2 ^ 59
def prefixEnd_7793495 : Nat := 4983230072969 + 3 ^ 40 * 7793495 * 2
def baseEnd_7793495 : Nat := 4001808913412090648670875

theorem tailTrace_7793495 : CollatzResearch.WordTrace tailWord_7793495 prefixEnd_7793495 4001808913412090648670875 := by
  unfold tailWord_7793495
  simp only [CollatzResearch.WordTrace]
  refine ⟨284252114900506112822957939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189501409933670741881971959 284252114900506112822957939)
  ·
    refine ⟨426378172350759169234436909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284252114900506112822957939 426378172350759169234436909)
    ·
      refine ⟨159891814631534688462913841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426378172350759169234436909 159891814631534688462913841)
      ·
        refine ⟨119918860973651016347185381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159891814631534688462913841 119918860973651016347185381)
        ·
          refine ⟨22484786432559565565097259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119918860973651016347185381 22484786432559565565097259)
          ·
            refine ⟨33727179648839348347645889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22484786432559565565097259 33727179648839348347645889)
            ·
              refine ⟨25295384736629511260734417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33727179648839348347645889 25295384736629511260734417)
              ·
                refine ⟨18971538552472133445550813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25295384736629511260734417 18971538552472133445550813)
                ·
                  refine ⟨7114326957177050042081555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18971538552472133445550813 7114326957177050042081555)
                  ·
                    refine ⟨10671490435765575063122333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7114326957177050042081555 10671490435765575063122333)
                    ·
                      refine ⟨4001808913412090648670875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10671490435765575063122333 4001808913412090648670875)
                      ·
                        rfl

theorem cell23_7793495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_7793495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793495 prefixEnd_7793495 := by exact prefixLift 7793495
  have htrace : WordTrace (prefixWord ++ tailWord_7793495) baseStart_7793495 baseEnd_7793495 := by
    simpa [prefixWord, tailWord_7793495, baseEnd_7793495] using wordTrace_append hprefix tailTrace_7793495
  have hstable : (prefixWord ++ tailWord_7793495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793495).length < 2 ^ (prefixWord ++ tailWord_7793495).sum := by decide
  have hdescent : baseEnd_7793495 < baseStart_7793495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793498 : List Nat := [3, 1, 1, 2, 1, 4, 1, 4, 1, 5]
def baseStart_7793498 : Nat := 118140960795 + 7793498 * 2 ^ 59
def prefixEnd_7793498 : Nat := 4983230072969 + 3 ^ 40 * 7793498 * 2
def baseEnd_7793498 : Nat := 1333936817951351378977787

theorem tailTrace_7793498 : CollatzResearch.WordTrace tailWord_7793498 prefixEnd_7793498 1333936817951351378977787 := by
  unfold tailWord_7793498
  simp only [CollatzResearch.WordTrace]
  refine ⟨71063056079873811083829287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189501482879663496223544765 71063056079873811083829287)
  ·
    refine ⟨106594584119810716625743931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71063056079873811083829287 106594584119810716625743931)
    ·
      refine ⟨159891876179716074938615897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106594584119810716625743931 159891876179716074938615897)
      ·
        refine ⟨119918907134787056203961923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159891876179716074938615897 119918907134787056203961923)
        ·
          refine ⟨179878360702180584305942885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119918907134787056203961923 179878360702180584305942885)
          ·
            refine ⟨33727192631658859557364291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179878360702180584305942885 33727192631658859557364291)
            ·
              refine ⟨50590788947488289336046437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33727192631658859557364291 50590788947488289336046437)
              ·
                refine ⟨9485772927654054250508707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50590788947488289336046437 9485772927654054250508707)
                ·
                  refine ⟨14228659391481081375763061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9485772927654054250508707 14228659391481081375763061)
                  ·
                    refine ⟨1333936817951351378977787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14228659391481081375763061 1333936817951351378977787)
                    ·
                      rfl

theorem cell23_7793498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_7793498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793498 prefixEnd_7793498 := by exact prefixLift 7793498
  have htrace : WordTrace (prefixWord ++ tailWord_7793498) baseStart_7793498 baseEnd_7793498 := by
    simpa [prefixWord, tailWord_7793498, baseEnd_7793498] using wordTrace_append hprefix tailTrace_7793498
  have hstable : (prefixWord ++ tailWord_7793498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793498).length < 2 ^ (prefixWord ++ tailWord_7793498).sum := by decide
  have hdescent : baseEnd_7793498 < baseStart_7793498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793506 : List Nat := [3, 3, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_7793506 : Nat := 118140960795 + 7793506 * 2 ^ 59
def prefixEnd_7793506 : Nat := 4983230072969 + 3 ^ 40 * 7793506 * 2
def baseEnd_7793506 : Nat := 1333938187233096701877775

theorem tailTrace_7793506 : CollatzResearch.WordTrace tailWord_7793506 prefixEnd_7793506 1333938187233096701877775 := by
  unfold tailWord_7793506
  simp only [CollatzResearch.WordTrace]
  refine ⟨71063129025866565425402093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189501677402310841134405581 71063129025866565425402093)
  ·
    refine ⟨26648673384699962034525785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71063129025866565425402093 26648673384699962034525785)
    ·
      refine ⟨19986505038524971525894339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26648673384699962034525785 19986505038524971525894339)
      ·
        refine ⟨29979757557787457288841509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19986505038524971525894339 29979757557787457288841509)
        ·
          refine ⟨5621204542085148241657783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29979757557787457288841509 5621204542085148241657783)
          ·
            refine ⟨8431806813127722362486675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621204542085148241657783 8431806813127722362486675)
            ·
              refine ⟨12647710219691583543730013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8431806813127722362486675 12647710219691583543730013)
              ·
                refine ⟨4742891332384343828898755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12647710219691583543730013 4742891332384343828898755)
                ·
                  refine ⟨7114336998576515743348133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4742891332384343828898755 7114336998576515743348133)
                  ·
                    refine ⟨1333938187233096701877775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7114336998576515743348133 1333938187233096701877775)
                    ·
                      rfl

theorem cell23_7793506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_7793506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793506 prefixEnd_7793506 := by exact prefixLift 7793506
  have htrace : WordTrace (prefixWord ++ tailWord_7793506) baseStart_7793506 baseEnd_7793506 := by
    simpa [prefixWord, tailWord_7793506, baseEnd_7793506] using wordTrace_append hprefix tailTrace_7793506
  have hstable : (prefixWord ++ tailWord_7793506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793506).length < 2 ^ (prefixWord ++ tailWord_7793506).sum := by decide
  have hdescent : baseEnd_7793506 < baseStart_7793506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793529 : List Nat := [1, 2, 1, 3, 2, 4, 3, 2, 1, 1, 3]
def baseStart_7793529 : Nat := 118140960795 + 7793529 * 2 ^ 59
def prefixEnd_7793529 : Nat := 4983230072969 + 3 ^ 40 * 7793529 * 2
def baseEnd_7793529 : Nat := 4001826371754343515645719

theorem tailTrace_7793529 : CollatzResearch.WordTrace tailWord_7793529 prefixEnd_7793529 4001826371754343515645719 := by
  unfold tailWord_7793529
  simp only [CollatzResearch.WordTrace]
  refine ⟨284253354982382936629695641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189502236654921957753130427 284253354982382936629695641)
  ·
    refine ⟨213190016236787202472271731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284253354982382936629695641 213190016236787202472271731)
    ·
      refine ⟨319785024355180803708407597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213190016236787202472271731 319785024355180803708407597)
      ·
        refine ⟨119919384133192801390652849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319785024355180803708407597 119919384133192801390652849)
        ·
          refine ⟨89939538099894601042989637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119919384133192801390652849 89939538099894601042989637)
          ·
            refine ⟨16863663393730237695560557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89939538099894601042989637 16863663393730237695560557)
            ·
              refine ⟨6323873772648839135835209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16863663393730237695560557 6323873772648839135835209)
              ·
                refine ⟨4742905329486629351876407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6323873772648839135835209 4742905329486629351876407)
                ·
                  refine ⟨7114357994229944027814611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4742905329486629351876407 7114357994229944027814611)
                  ·
                    refine ⟨10671536991344916041721917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7114357994229944027814611 10671536991344916041721917)
                    ·
                      refine ⟨4001826371754343515645719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10671536991344916041721917 4001826371754343515645719)
                      ·
                        rfl

theorem cell23_7793529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_7793529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793529 prefixEnd_7793529 := by exact prefixLift 7793529
  have htrace : WordTrace (prefixWord ++ tailWord_7793529) baseStart_7793529 baseEnd_7793529 := by
    simpa [prefixWord, tailWord_7793529, baseEnd_7793529] using wordTrace_append hprefix tailTrace_7793529
  have hstable : (prefixWord ++ tailWord_7793529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793529).length < 2 ^ (prefixWord ++ tailWord_7793529).sum := by decide
  have hdescent : baseEnd_7793529 < baseStart_7793529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793531 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 6]
def baseStart_7793531 : Nat := 118140960795 + 7793531 * 2 ^ 59
def prefixEnd_7793531 : Nat := 4983230072969 + 3 ^ 40 * 7793531 * 2
def baseEnd_7793531 : Nat := 4001827398715652507820709

theorem tailTrace_7793531 : CollatzResearch.WordTrace tailWord_7793531 prefixEnd_7793531 4001827398715652507820709 := by
  unfold tailWord_7793531
  simp only [CollatzResearch.WordTrace]
  refine ⟨284253427928375690971268447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189502285285583793980845631 284253427928375690971268447)
  ·
    refine ⟨426380141892563536456902671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284253427928375690971268447 426380141892563536456902671)
    ·
      refine ⟨639570212838845304685354007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426380141892563536456902671 639570212838845304685354007)
      ·
        refine ⟨959355319258267957028031011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639570212838845304685354007 959355319258267957028031011)
        ·
          refine ⟨1439032978887401935542046517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959355319258267957028031011 1439032978887401935542046517)
          ·
            refine ⟨134909341770693931457066861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1439032978887401935542046517 134909341770693931457066861)
            ·
              refine ⟨50591003164010224296400073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134909341770693931457066861 50591003164010224296400073)
              ·
                refine ⟨37943252373007668222300055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50591003164010224296400073 37943252373007668222300055)
                ·
                  refine ⟨56914878559511502333450083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37943252373007668222300055 56914878559511502333450083)
                  ·
                    refine ⟨85372317839267253500175125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56914878559511502333450083 85372317839267253500175125)
                    ·
                      refine ⟨4001827398715652507820709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85372317839267253500175125 4001827398715652507820709)
                      ·
                        rfl

theorem cell23_7793531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 6].length) (baseStart_7793531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793531 prefixEnd_7793531 := by exact prefixLift 7793531
  have htrace : WordTrace (prefixWord ++ tailWord_7793531) baseStart_7793531 baseEnd_7793531 := by
    simpa [prefixWord, tailWord_7793531, baseEnd_7793531] using wordTrace_append hprefix tailTrace_7793531
  have hstable : (prefixWord ++ tailWord_7793531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793531).length < 2 ^ (prefixWord ++ tailWord_7793531).sum := by decide
  have hdescent : baseEnd_7793531 < baseStart_7793531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793541 : List Nat := [1, 3, 1, 1, 3, 3, 1, 10]
def baseStart_7793541 : Nat := 118140960795 + 7793541 * 2 ^ 59
def prefixEnd_7793541 : Nat := 4983230072969 + 3 ^ 40 * 7793541 * 2
def baseEnd_7793541 : Nat := 148216019760081387729469

theorem tailTrace_7793541 : CollatzResearch.WordTrace tailWord_7793541 prefixEnd_7793541 148216019760081387729469 := by
  unfold tailWord_7793541
  simp only [CollatzResearch.WordTrace]
  refine ⟨284253792658339462679132477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189502528438892975119421651 284253792658339462679132477)
  ·
    refine ⟨106595172246877298504674679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284253792658339462679132477 106595172246877298504674679)
    ·
      refine ⟨159892758370315947757012019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106595172246877298504674679 159892758370315947757012019)
      ·
        refine ⟨239839137555473921635518029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159892758370315947757012019 239839137555473921635518029)
        ·
          refine ⟨89939676583302720613319261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239839137555473921635518029 89939676583302720613319261)
          ·
            refine ⟨33727378718738520229994723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89939676583302720613319261 33727378718738520229994723)
            ·
              refine ⟨50591068078107780344992085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33727378718738520229994723 50591068078107780344992085)
              ·
                refine ⟨148216019760081387729469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50591068078107780344992085 148216019760081387729469)
                ·
                  rfl

theorem cell23_7793541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 10].length) (baseStart_7793541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793541 prefixEnd_7793541 := by exact prefixLift 7793541
  have htrace : WordTrace (prefixWord ++ tailWord_7793541) baseStart_7793541 baseEnd_7793541 := by
    simpa [prefixWord, tailWord_7793541, baseEnd_7793541] using wordTrace_append hprefix tailTrace_7793541
  have hstable : (prefixWord ++ tailWord_7793541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793541).length < 2 ^ (prefixWord ++ tailWord_7793541).sum := by decide
  have hdescent : baseEnd_7793541 < baseStart_7793541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793545 : List Nat := [1, 2, 1, 1, 5, 3, 1, 3, 2, 4]
def baseStart_7793545 : Nat := 118140960795 + 7793545 * 2 ^ 59
def prefixEnd_7793545 : Nat := 4983230072969 + 3 ^ 40 * 7793545 * 2
def baseEnd_7793545 : Nat := 1333944862481605151015215

theorem tailTrace_7793545 : CollatzResearch.WordTrace tailWord_7793545 prefixEnd_7793545 1333944862481605151015215 := by
  unfold tailWord_7793545
  simp only [CollatzResearch.WordTrace]
  refine ⟨284253938550324971362278089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189502625700216647574852059 284253938550324971362278089)
  ·
    refine ⟨213190453912743728521708567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284253938550324971362278089 213190453912743728521708567)
    ·
      refine ⟨319785680869115592782562851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213190453912743728521708567 319785680869115592782562851)
      ·
        refine ⟨479678521303673389173844277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319785680869115592782562851 479678521303673389173844277)
        ·
          refine ⟨44969861372219380235047901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 479678521303673389173844277 44969861372219380235047901)
          ·
            refine ⟨16863698014582267588142963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44969861372219380235047901 16863698014582267588142963)
            ·
              refine ⟨25295547021873401382214445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16863698014582267588142963 25295547021873401382214445)
              ·
                refine ⟨9485830133202525518330417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25295547021873401382214445 9485830133202525518330417)
                ·
                  refine ⟨7114372599901894138747813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9485830133202525518330417 7114372599901894138747813)
                  ·
                    refine ⟨1333944862481605151015215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7114372599901894138747813 1333944862481605151015215)
                    ·
                      rfl

theorem cell23_7793545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 4].length) (baseStart_7793545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793545 prefixEnd_7793545 := by exact prefixLift 7793545
  have htrace : WordTrace (prefixWord ++ tailWord_7793545) baseStart_7793545 baseEnd_7793545 := by
    simpa [prefixWord, tailWord_7793545, baseEnd_7793545] using wordTrace_append hprefix tailTrace_7793545
  have hstable : (prefixWord ++ tailWord_7793545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793545).length < 2 ^ (prefixWord ++ tailWord_7793545).sum := by decide
  have hdescent : baseEnd_7793545 < baseStart_7793545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793568 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 3]
def baseStart_7793568 : Nat := 118140960795 + 7793568 * 2 ^ 59
def prefixEnd_7793568 : Nat := 4983230072969 + 3 ^ 40 * 7793568 * 2
def baseEnd_7793568 : Nat := 4001846397499868863058039

theorem tailTrace_7793568 : CollatzResearch.WordTrace tailWord_7793568 prefixEnd_7793568 4001846397499868863058039 := by
  unfold tailWord_7793568
  simp only [CollatzResearch.WordTrace]
  refine ⟨142127388714620823145182679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189503184952827764193576905 142127388714620823145182679)
  ·
    refine ⟨213191083071931234717774019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142127388714620823145182679 213191083071931234717774019)
    ·
      refine ⟨319786624607896852076661029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213191083071931234717774019 319786624607896852076661029)
      ·
        refine ⟨59959992113980659764373943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319786624607896852076661029 59959992113980659764373943)
        ·
          refine ⟨89939988170970989646560915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59959992113980659764373943 89939988170970989646560915)
          ·
            refine ⟨134909982256456484469841373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89939988170970989646560915 134909982256456484469841373)
            ·
              refine ⟨50591243346171181676190515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134909982256456484469841373 50591243346171181676190515)
              ·
                refine ⟨75886865019256772514285773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50591243346171181676190515 75886865019256772514285773)
                ·
                  refine ⟨28457574382221289692857165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75886865019256772514285773 28457574382221289692857165)
                  ·
                    refine ⟨10671590393332983634821437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28457574382221289692857165 10671590393332983634821437)
                    ·
                      refine ⟨4001846397499868863058039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10671590393332983634821437 4001846397499868863058039)
                      ·
                        rfl

theorem cell23_7793568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_7793568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793568 prefixEnd_7793568 := by exact prefixLift 7793568
  have htrace : WordTrace (prefixWord ++ tailWord_7793568) baseStart_7793568 baseEnd_7793568 := by
    simpa [prefixWord, tailWord_7793568, baseEnd_7793568] using wordTrace_append hprefix tailTrace_7793568
  have hstable : (prefixWord ++ tailWord_7793568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793568).length < 2 ^ (prefixWord ++ tailWord_7793568).sum := by decide
  have hdescent : baseEnd_7793568 < baseStart_7793568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793572 : List Nat := [2, 3, 1, 2, 1, 2, 5, 1, 1, 2, 3]
def baseStart_7793572 : Nat := 118140960795 + 7793572 * 2 ^ 59
def prefixEnd_7793572 : Nat := 4983230072969 + 3 ^ 40 * 7793572 * 2
def baseEnd_7793572 : Nat := 4001848451422486847408021

theorem tailTrace_7793572 : CollatzResearch.WordTrace tailWord_7793572 prefixEnd_7793572 4001848451422486847408021 := by
  unfold tailWord_7793572
  simp only [CollatzResearch.WordTrace]
  refine ⟨142127461660613577486755485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189503282214151436649007313 142127461660613577486755485)
  ·
    refine ⟨53297798122730091557533307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142127461660613577486755485 53297798122730091557533307)
    ·
      refine ⟨79946697184095137336299961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53297798122730091557533307 79946697184095137336299961)
      ·
        refine ⟨59960022888071353002224971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79946697184095137336299961 59960022888071353002224971)
        ·
          refine ⟨89940034332107029503337457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59960022888071353002224971 89940034332107029503337457)
          ·
            refine ⟨67455025749080272127503093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89940034332107029503337457 67455025749080272127503093)
            ·
              refine ⟨6323908663976275511953415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67455025749080272127503093 6323908663976275511953415)
              ·
                refine ⟨9485862995964413267930123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6323908663976275511953415 9485862995964413267930123)
                ·
                  refine ⟨14228794493946619901895185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9485862995964413267930123 14228794493946619901895185)
                  ·
                    refine ⟨10671595870459964926421389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14228794493946619901895185 10671595870459964926421389)
                    ·
                      refine ⟨4001848451422486847408021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10671595870459964926421389 4001848451422486847408021)
                      ·
                        rfl

theorem cell23_7793572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_7793572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793572 prefixEnd_7793572 := by exact prefixLift 7793572
  have htrace : WordTrace (prefixWord ++ tailWord_7793572) baseStart_7793572 baseEnd_7793572 := by
    simpa [prefixWord, tailWord_7793572, baseEnd_7793572] using wordTrace_append hprefix tailTrace_7793572
  have hstable : (prefixWord ++ tailWord_7793572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793572).length < 2 ^ (prefixWord ++ tailWord_7793572).sum := by decide
  have hdescent : baseEnd_7793572 < baseStart_7793572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793612 : List Nat := [2, 2, 1, 4, 1, 1, 2, 4, 1, 3, 2]
def baseStart_7793612 : Nat := 118140960795 + 7793612 * 2 ^ 59
def prefixEnd_7793612 : Nat := 4983230072969 + 3 ^ 40 * 7793612 * 2
def baseEnd_7793612 : Nat := 4001868990648666690907837

theorem tailTrace_7793612 : CollatzResearch.WordTrace tailWord_7793612 prefixEnd_7793612 4001868990648666690907837 := by
  unfold tailWord_7793612
  simp only [CollatzResearch.WordTrace]
  refine ⟨142128191120541120902483545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189504254827388161203311393 142128191120541120902483545)
  ·
    refine ⟨106596143340405840676862659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142128191120541120902483545 106596143340405840676862659)
    ·
      refine ⟨159894215010608761015293989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106596143340405840676862659 159894215010608761015293989)
      ·
        refine ⟨29980165314489142690367623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159894215010608761015293989 29980165314489142690367623)
        ·
          refine ⟨44970247971733714035551435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29980165314489142690367623 44970247971733714035551435)
          ·
            refine ⟨67455371957600571053327153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44970247971733714035551435 67455371957600571053327153)
            ·
              refine ⟨50591528968200428289995365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67455371957600571053327153 50591528968200428289995365)
              ·
                refine ⟨9485911681537580304374131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50591528968200428289995365 9485911681537580304374131)
                ·
                  refine ⟨14228867522306370456561197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9485911681537580304374131 14228867522306370456561197)
                  ·
                    refine ⟨5335825320864888921210449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14228867522306370456561197 5335825320864888921210449)
                    ·
                      refine ⟨4001868990648666690907837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5335825320864888921210449 4001868990648666690907837)
                      ·
                        rfl

theorem cell23_7793612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_7793612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793612 prefixEnd_7793612 := by exact prefixLift 7793612
  have htrace : WordTrace (prefixWord ++ tailWord_7793612) baseStart_7793612 baseEnd_7793612 := by
    simpa [prefixWord, tailWord_7793612, baseEnd_7793612] using wordTrace_append hprefix tailTrace_7793612
  have hstable : (prefixWord ++ tailWord_7793612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793612).length < 2 ^ (prefixWord ++ tailWord_7793612).sum := by decide
  have hdescent : baseEnd_7793612 < baseStart_7793612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793629 : List Nat := [1, 4, 3, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_7793629 : Nat := 118140960795 + 7793629 * 2 ^ 59
def prefixEnd_7793629 : Nat := 4983230072969 + 3 ^ 40 * 7793629 * 2
def baseEnd_7793629 : Nat := 4001877719819793124395259

theorem tailTrace_7793629 : CollatzResearch.WordTrace tailWord_7793629 prefixEnd_7793629 4001877719819793124395259 := by
  unfold tailWord_7793629
  simp only [CollatzResearch.WordTrace]
  refine ⟨284257002282020653708335941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189504668188013769138890627 284257002282020653708335941)
  ·
    refine ⟨53298187927878872570312989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284257002282020653708335941 53298187927878872570312989)
    ·
      refine ⟨19986820472954577213867371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53298187927878872570312989 19986820472954577213867371)
      ·
        refine ⟨29980230709431865820801057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19986820472954577213867371 29980230709431865820801057)
        ·
          refine ⟨22485173032073899365600793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29980230709431865820801057 22485173032073899365600793)
          ·
            refine ⟨16863879774055424524200595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22485173032073899365600793 16863879774055424524200595)
            ·
              refine ⟨25295819661083136786300893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16863879774055424524200595 25295819661083136786300893)
              ·
                refine ⟨9485932372906176294862835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25295819661083136786300893 9485932372906176294862835)
                ·
                  refine ⟨14228898559359264442294253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9485932372906176294862835 14228898559359264442294253)
                  ·
                    refine ⟨5335836959759724165860345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14228898559359264442294253 5335836959759724165860345)
                    ·
                      refine ⟨4001877719819793124395259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5335836959759724165860345 4001877719819793124395259)
                      ·
                        rfl

theorem cell23_7793629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_7793629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793629 prefixEnd_7793629 := by exact prefixLift 7793629
  have htrace : WordTrace (prefixWord ++ tailWord_7793629) baseStart_7793629 baseEnd_7793629 := by
    simpa [prefixWord, tailWord_7793629, baseEnd_7793629] using wordTrace_append hprefix tailTrace_7793629
  have hstable : (prefixWord ++ tailWord_7793629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793629).length < 2 ^ (prefixWord ++ tailWord_7793629).sum := by decide
  have hdescent : baseEnd_7793629 < baseStart_7793629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793653 : List Nat := [1, 3, 5, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_7793653 : Nat := 118140960795 + 7793653 * 2 ^ 59
def prefixEnd_7793653 : Nat := 4983230072969 + 3 ^ 40 * 7793653 * 2
def baseEnd_7793653 : Nat := 4001890043355501030495149

theorem tailTrace_7793653 : CollatzResearch.WordTrace tailWord_7793653 prefixEnd_7793653 4001890043355501030495149 := by
  unfold tailWord_7793653
  simp only [CollatzResearch.WordTrace]
  refine ⟨284257877633933705807209613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189505251755955803871473075 284257877633933705807209613)
  ·
    refine ⟨106596704112725139677703605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284257877633933705807209613 106596704112725139677703605)
    ·
      refine ⟨9993441010567981844784713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106596704112725139677703605 9993441010567981844784713)
      ·
        refine ⟨7495080757925986383588535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9993441010567981844784713 7495080757925986383588535)
        ·
          refine ⟨11242621136888979575382803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7495080757925986383588535 11242621136888979575382803)
          ·
            refine ⟨16863931705333469363074205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11242621136888979575382803 16863931705333469363074205)
            ·
              refine ⟨6323974389500051011152827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16863931705333469363074205 6323974389500051011152827)
              ·
                refine ⟨9485961584250076516729241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6323974389500051011152827 9485961584250076516729241)
                ·
                  refine ⟨7114471188187557387546931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9485961584250076516729241 7114471188187557387546931)
                  ·
                    refine ⟨10671706782281336081320397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7114471188187557387546931 10671706782281336081320397)
                    ·
                      refine ⟨4001890043355501030495149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10671706782281336081320397 4001890043355501030495149)
                      ·
                        rfl

theorem cell23_7793653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_7793653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793653 prefixEnd_7793653 := by exact prefixLift 7793653
  have htrace : WordTrace (prefixWord ++ tailWord_7793653) baseStart_7793653 baseEnd_7793653 := by
    simpa [prefixWord, tailWord_7793653, baseEnd_7793653] using wordTrace_append hprefix tailTrace_7793653
  have hstable : (prefixWord ++ tailWord_7793653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793653).length < 2 ^ (prefixWord ++ tailWord_7793653).sum := by decide
  have hdescent : baseEnd_7793653 < baseStart_7793653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793695 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 2, 5]
def baseStart_7793695 : Nat := 118140960795 + 7793695 * 2 ^ 59
def prefixEnd_7793695 : Nat := 4983230072969 + 3 ^ 40 * 7793695 * 2
def baseEnd_7793695 : Nat := 1333970536514329955389985

theorem tailTrace_7793695 : CollatzResearch.WordTrace tailWord_7793695 prefixEnd_7793695 1333970536514329955389985 := by
  unfold tailWord_7793695
  simp only [CollatzResearch.WordTrace]
  refine ⟨284259409499781546980238539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189506272999854364653492359 284259409499781546980238539)
  ·
    refine ⟨426389114249672320470357809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284259409499781546980238539 426389114249672320470357809)
    ·
      refine ⟨319791835687254240352768357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426389114249672320470357809 319791835687254240352768357)
      ·
        refine ⟨59960969191360170066144067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319791835687254240352768357 59960969191360170066144067)
        ·
          refine ⟨89941453787040255099216101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59960969191360170066144067 89941453787040255099216101)
          ·
            refine ⟨16864022585070047831103019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89941453787040255099216101 16864022585070047831103019)
            ·
              refine ⟨25296033877605071746654529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16864022585070047831103019 25296033877605071746654529)
              ·
                refine ⟨18972025408203803809990897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25296033877605071746654529 18972025408203803809990897)
                ·
                  refine ⟨14229019056152852857493173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18972025408203803809990897 14229019056152852857493173)
                  ·
                    refine ⟨1333970536514329955389985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14229019056152852857493173 1333970536514329955389985)
                    ·
                      rfl

theorem cell23_7793695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 5].length) (baseStart_7793695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793695 prefixEnd_7793695 := by exact prefixLift 7793695
  have htrace : WordTrace (prefixWord ++ tailWord_7793695) baseStart_7793695 baseEnd_7793695 := by
    simpa [prefixWord, tailWord_7793695, baseEnd_7793695] using wordTrace_append hprefix tailTrace_7793695
  have hstable : (prefixWord ++ tailWord_7793695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793695).length < 2 ^ (prefixWord ++ tailWord_7793695).sum := by decide
  have hdescent : baseEnd_7793695 < baseStart_7793695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793715 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 1, 6, 2]
def baseStart_7793715 : Nat := 118140960795 + 7793715 * 2 ^ 59
def prefixEnd_7793715 : Nat := 4983230072969 + 3 ^ 40 * 7793715 * 2
def baseEnd_7793715 : Nat := 4001921879156079787919863

theorem tailTrace_7793715 : CollatzResearch.WordTrace tailWord_7793715 prefixEnd_7793715 4001921879156079787919863 := by
  unfold tailWord_7793715
  simp only [CollatzResearch.WordTrace]
  refine ⟨284260138959709090395966599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189506759306472726930644399 284260138959709090395966599)
  ·
    refine ⟨426390208439563635593949899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284260138959709090395966599 426390208439563635593949899)
    ·
      refine ⟨639585312659345453390924849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426390208439563635593949899 639585312659345453390924849)
      ·
        refine ⟨479688984494509090043193637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639585312659345453390924849 479688984494509090043193637)
        ·
          refine ⟨89941684592720454383098807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 479688984494509090043193637 89941684592720454383098807)
          ·
            refine ⟨134912526889080681574648211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89941684592720454383098807 134912526889080681574648211)
            ·
              refine ⟨202368790333621022361972317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134912526889080681574648211 202368790333621022361972317)
              ·
                refine ⟨75888296375107883385739619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202368790333621022361972317 75888296375107883385739619)
                ·
                  refine ⟨113832444562661825078609429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75888296375107883385739619 113832444562661825078609429)
                  ·
                    refine ⟨5335895838874773050559817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113832444562661825078609429 5335895838874773050559817)
                    ·
                      refine ⟨4001921879156079787919863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5335895838874773050559817 4001921879156079787919863)
                      ·
                        rfl

theorem cell23_7793715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 6, 2].length) (baseStart_7793715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793715 prefixEnd_7793715 := by exact prefixLift 7793715
  have htrace : WordTrace (prefixWord ++ tailWord_7793715) baseStart_7793715 baseEnd_7793715 := by
    simpa [prefixWord, tailWord_7793715, baseEnd_7793715] using wordTrace_append hprefix tailTrace_7793715
  have hstable : (prefixWord ++ tailWord_7793715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793715).length < 2 ^ (prefixWord ++ tailWord_7793715).sum := by decide
  have hdescent : baseEnd_7793715 < baseStart_7793715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793738 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 10]
def baseStart_7793738 : Nat := 118140960795 + 7793738 * 2 ^ 59
def prefixEnd_7793738 : Nat := 4983230072969 + 3 ^ 40 * 7793738 * 2
def baseEnd_7793738 : Nat := 444659298801237021992473

theorem tailTrace_7793738 : CollatzResearch.WordTrace tailWord_7793738 prefixEnd_7793738 444659298801237021992473 := by
  unfold tailWord_7793738
  simp only [CollatzResearch.WordTrace]
  refine ⟨71065244459656441331013467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189507318559083843549369245 71065244459656441331013467)
  ·
    refine ⟨106597866689484661996520201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71065244459656441331013467 106597866689484661996520201)
    ·
      refine ⟨79948400017113496497390151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106597866689484661996520201 79948400017113496497390151)
      ·
        refine ⟨119922600025670244746085227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79948400017113496497390151 119922600025670244746085227)
        ·
          refine ⟨179883900038505367119127841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119922600025670244746085227 179883900038505367119127841)
          ·
            refine ⟨134912925028879025339345881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179883900038505367119127841 134912925028879025339345881)
            ·
              refine ⟨101184693771659269004509411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134912925028879025339345881 101184693771659269004509411)
              ·
                refine ⟨151777040657488903506764117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101184693771659269004509411 151777040657488903506764117)
                ·
                  refine ⟨444659298801237021992473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 151777040657488903506764117 444659298801237021992473)
                  ·
                    rfl

theorem cell23_7793738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_7793738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793738 prefixEnd_7793738 := by exact prefixLift 7793738
  have htrace : WordTrace (prefixWord ++ tailWord_7793738) baseStart_7793738 baseEnd_7793738 := by
    simpa [prefixWord, tailWord_7793738, baseEnd_7793738] using wordTrace_append hprefix tailTrace_7793738
  have hstable : (prefixWord ++ tailWord_7793738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793738).length < 2 ^ (prefixWord ++ tailWord_7793738).sum := by decide
  have hdescent : baseEnd_7793738 < baseStart_7793738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793750 : List Nat := [5, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_7793750 : Nat := 118140960795 + 7793750 * 2 ^ 59
def prefixEnd_7793750 : Nat := 4983230072969 + 3 ^ 40 * 7793750 * 2
def baseEnd_7793750 : Nat := 444659983442109683442467

theorem tailTrace_7793750 : CollatzResearch.WordTrace tailWord_7793750 prefixEnd_7793750 444659983442109683442467 := by
  unfold tailWord_7793750
  simp only [CollatzResearch.WordTrace]
  refine ⟨17766338469661393210843169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189507610343054860915660469 17766338469661393210843169)
  ·
    refine ⟨13324753852246044908132377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17766338469661393210843169 13324753852246044908132377)
    ·
      refine ⟨9993565389184533681099283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13324753852246044908132377 9993565389184533681099283)
      ·
        refine ⟨14990348083776800521648925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9993565389184533681099283 14990348083776800521648925)
        ·
          refine ⟨5621380531416300195618347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14990348083776800521648925 5621380531416300195618347)
          ·
            refine ⟨8432070797124450293427521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621380531416300195618347 8432070797124450293427521)
            ·
              refine ⟨6324053097843337720070641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8432070797124450293427521 6324053097843337720070641)
              ·
                refine ⟨4743039823382503290052981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6324053097843337720070641 4743039823382503290052981)
                ·
                  refine ⟨444659983442109683442467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4743039823382503290052981 444659983442109683442467)
                  ·
                    rfl

theorem cell23_7793750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_7793750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793750 prefixEnd_7793750 := by exact prefixLift 7793750
  have htrace : WordTrace (prefixWord ++ tailWord_7793750) baseStart_7793750 baseEnd_7793750 := by
    simpa [prefixWord, tailWord_7793750, baseEnd_7793750] using wordTrace_append hprefix tailTrace_7793750
  have hstable : (prefixWord ++ tailWord_7793750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793750).length < 2 ^ (prefixWord ++ tailWord_7793750).sum := by decide
  have hdescent : baseEnd_7793750 < baseStart_7793750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793802 : List Nat := [3, 1, 2, 3, 1, 1, 3, 3, 1, 5]
def baseStart_7793802 : Nat := 118140960795 + 7793802 * 2 ^ 59
def prefixEnd_7793802 : Nat := 4983230072969 + 3 ^ 40 * 7793802 * 2
def baseEnd_7793802 : Nat := 1333988850657673649177321

theorem tailTrace_7793802 : CollatzResearch.WordTrace tailWord_7793802 prefixEnd_7793802 1333988850657673649177321 := by
  unfold tailWord_7793802
  simp only [CollatzResearch.WordTrace]
  refine ⟨71065828027598476063595915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189508874740262602836255773 71065828027598476063595915)
  ·
    refine ⟨106598742041397714095393873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71065828027598476063595915 106598742041397714095393873)
    ·
      refine ⟨79949056531048285571545405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106598742041397714095393873 79949056531048285571545405)
      ·
        refine ⟨29980896199143107089329527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79949056531048285571545405 29980896199143107089329527)
        ·
          refine ⟨44971344298714660633994291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29980896199143107089329527 44971344298714660633994291)
          ·
            refine ⟨67457016448071990950991437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44971344298714660633994291 67457016448071990950991437)
            ·
              refine ⟨25296381168026996606621789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67457016448071990950991437 25296381168026996606621789)
              ·
                refine ⟨9486142938010123727483171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25296381168026996606621789 9486142938010123727483171)
                ·
                  refine ⟨14229214407015185591224757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9486142938010123727483171 14229214407015185591224757)
                  ·
                    refine ⟨1333988850657673649177321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14229214407015185591224757 1333988850657673649177321)
                    ·
                      rfl

theorem cell23_7793802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_7793802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793802 prefixEnd_7793802 := by exact prefixLift 7793802
  have htrace : WordTrace (prefixWord ++ tailWord_7793802) baseStart_7793802 baseEnd_7793802 := by
    simpa [prefixWord, tailWord_7793802, baseEnd_7793802] using wordTrace_append hprefix tailTrace_7793802
  have hstable : (prefixWord ++ tailWord_7793802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793802).length < 2 ^ (prefixWord ++ tailWord_7793802).sum := by decide
  have hdescent : baseEnd_7793802 < baseStart_7793802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793816 : List Nat := [2, 1, 2, 4, 2, 1, 2, 4, 1, 1, 3]
def baseStart_7793816 : Nat := 118140960795 + 7793816 * 2 ^ 59
def prefixEnd_7793816 : Nat := 4983230072969 + 3 ^ 40 * 7793816 * 2
def baseEnd_7793816 : Nat := 4001973740702183892756899

theorem tailTrace_7793816 : CollatzResearch.WordTrace tailWord_7793816 prefixEnd_7793816 4001973740702183892756899 := by
  unfold tailWord_7793816
  simp only [CollatzResearch.WordTrace]
  refine ⟨142131911366171592322696651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189509215154895456430262201 142131911366171592322696651)
  ·
    refine ⟨213197867049257388484044977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142131911366171592322696651 213197867049257388484044977)
    ·
      refine ⟨159898400286943041363033733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213197867049257388484044977 159898400286943041363033733)
      ·
        refine ⟨29980950053801820255568825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159898400286943041363033733 29980950053801820255568825)
        ·
          refine ⟨22485712540351365191676619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29980950053801820255568825 22485712540351365191676619)
          ·
            refine ⟨33728568810527047787514929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22485712540351365191676619 33728568810527047787514929)
            ·
              refine ⟨25296426607895285840636197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33728568810527047787514929 25296426607895285840636197)
              ·
                refine ⟨4743079988980366095119287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25296426607895285840636197 4743079988980366095119287)
                ·
                  refine ⟨7114619983470549142678931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4743079988980366095119287 7114619983470549142678931)
                  ·
                    refine ⟨10671929975205823714018397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7114619983470549142678931 10671929975205823714018397)
                    ·
                      refine ⟨4001973740702183892756899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10671929975205823714018397 4001973740702183892756899)
                      ·
                        rfl

theorem cell23_7793816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_7793816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793816 prefixEnd_7793816 := by exact prefixLift 7793816
  have htrace : WordTrace (prefixWord ++ tailWord_7793816) baseStart_7793816 baseEnd_7793816 := by
    simpa [prefixWord, tailWord_7793816, baseEnd_7793816] using wordTrace_append hprefix tailTrace_7793816
  have hstable : (prefixWord ++ tailWord_7793816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793816).length < 2 ^ (prefixWord ++ tailWord_7793816).sum := by decide
  have hdescent : baseEnd_7793816 < baseStart_7793816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793839 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 3, 2, 2]
def baseStart_7793839 : Nat := 118140960795 + 7793839 * 2 ^ 59
def prefixEnd_7793839 : Nat := 4983230072969 + 3 ^ 40 * 7793839 * 2
def baseEnd_7793839 : Nat := 4001985550757237302769293

theorem tailTrace_7793839 : CollatzResearch.WordTrace tailWord_7793839 prefixEnd_7793839 4001985550757237302769293 := by
  unfold tailWord_7793839
  simp only [CollatzResearch.WordTrace]
  refine ⟨284264661611259859573480571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189509774407506573048987047 284264661611259859573480571)
  ·
    refine ⟨426396992416889789360220857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284264661611259859573480571 426396992416889789360220857)
    ·
      refine ⟨319797744312667342020165643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426396992416889789360220857 319797744312667342020165643)
      ·
        refine ⟨479696616469001013030248465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319797744312667342020165643 479696616469001013030248465)
        ·
          refine ⟨359772462351750759772686349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479696616469001013030248465 359772462351750759772686349)
          ·
            refine ⟨134914673381906534914757381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359772462351750759772686349 134914673381906534914757381)
            ·
              refine ⟨25296501259107475296517009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134914673381906534914757381 25296501259107475296517009)
              ·
                refine ⟨18972375944330606472387757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25296501259107475296517009 18972375944330606472387757)
                ·
                  refine ⟨7114640979123977427145409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18972375944330606472387757 7114640979123977427145409)
                  ·
                    refine ⟨5335980734342983070359057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7114640979123977427145409 5335980734342983070359057)
                    ·
                      refine ⟨4001985550757237302769293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5335980734342983070359057 4001985550757237302769293)
                      ·
                        rfl

theorem cell23_7793839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 2, 2].length) (baseStart_7793839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793839 prefixEnd_7793839 := by exact prefixLift 7793839
  have htrace : WordTrace (prefixWord ++ tailWord_7793839) baseStart_7793839 baseEnd_7793839 := by
    simpa [prefixWord, tailWord_7793839, baseEnd_7793839] using wordTrace_append hprefix tailTrace_7793839
  have hstable : (prefixWord ++ tailWord_7793839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793839).length < 2 ^ (prefixWord ++ tailWord_7793839).sum := by decide
  have hdescent : baseEnd_7793839 < baseStart_7793839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
