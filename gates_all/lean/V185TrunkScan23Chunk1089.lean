import V185TrunkScan23Chunk1088

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6447617 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 2, 6]
def baseStart_6447617 : Nat := 118140960795 + 6447617 * 2 ^ 59
def prefixEnd_6447617 : Nat := 4983230072969 + 3 ^ 40 * 6447617 * 2
def baseEnd_6447617 : Nat := 1103575532366735134178485

theorem tailTrace_6447617 : CollatzResearch.WordTrace tailWord_6447617 prefixEnd_6447617 1103575532366735134178485 := by
  unfold tailWord_6447617
  simp only [CollatzResearch.WordTrace]
  refine ⟨235163911482392249160461105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156775940988261499440307403 235163911482392249160461105)
  ·
    refine ⟨176372933611794186870345829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235163911482392249160461105 176372933611794186870345829)
    ·
      refine ⟨33069925052211410038189843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176372933611794186870345829 33069925052211410038189843)
      ·
        refine ⟨49604887578317115057284765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33069925052211410038189843 49604887578317115057284765)
        ·
          refine ⟨18601832841868918146481787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49604887578317115057284765 18601832841868918146481787)
          ·
            refine ⟨27902749262803377219722681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18601832841868918146481787 27902749262803377219722681)
            ·
              refine ⟨20927061947102532914792011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27902749262803377219722681 20927061947102532914792011)
              ·
                refine ⟨31390592920653799372188017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20927061947102532914792011 31390592920653799372188017)
                ·
                  refine ⟨23542944690490349529141013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31390592920653799372188017 23542944690490349529141013)
                  ·
                    refine ⟨1103575532366735134178485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23542944690490349529141013 1103575532366735134178485)
                    ·
                      rfl

theorem cell23_6447617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_6447617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447617 prefixEnd_6447617 := by exact prefixLift 6447617
  have htrace : WordTrace (prefixWord ++ tailWord_6447617) baseStart_6447617 baseEnd_6447617 := by
    simpa [prefixWord, tailWord_6447617, baseEnd_6447617] using wordTrace_append hprefix tailTrace_6447617
  have hstable : (prefixWord ++ tailWord_6447617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447617).length < 2 ^ (prefixWord ++ tailWord_6447617).sum := by decide
  have hdescent : baseEnd_6447617 < baseStart_6447617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447618 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_6447618 : Nat := 118140960795 + 6447618 * 2 ^ 59
def prefixEnd_6447618 : Nat := 4983230072969 + 3 ^ 40 * 6447618 * 2
def baseEnd_6447618 : Nat := 3310727110580859898622951

theorem tailTrace_6447618 : CollatzResearch.WordTrace tailWord_6447618 prefixEnd_6447618 3310727110580859898622951 := by
  unfold tailWord_6447618
  simp only [CollatzResearch.WordTrace]
  refine ⟨58790986988847156582811877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156775965303592417554165005 58790986988847156582811877)
  ·
    refine ⟨11023310060408841859277227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58790986988847156582811877 11023310060408841859277227)
    ·
      refine ⟨16534965090613262788915841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11023310060408841859277227 16534965090613262788915841)
      ·
        refine ⟨12401223817959947091686881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16534965090613262788915841 12401223817959947091686881)
        ·
          refine ⟨9300917863469960318765161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12401223817959947091686881 9300917863469960318765161)
          ·
            refine ⟨6975688397602470239073871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9300917863469960318765161 6975688397602470239073871)
            ·
              refine ⟨10463532596403705358610807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6975688397602470239073871 10463532596403705358610807)
              ·
                refine ⟨15695298894605558037916211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10463532596403705358610807 15695298894605558037916211)
                ·
                  refine ⟨23542948341908337056874317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15695298894605558037916211 23542948341908337056874317)
                  ·
                    refine ⟨8828605628215626396327869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23542948341908337056874317 8828605628215626396327869)
                    ·
                      refine ⟨3310727110580859898622951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8828605628215626396327869 3310727110580859898622951)
                      ·
                        rfl

theorem cell23_6447618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_6447618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447618 prefixEnd_6447618 := by exact prefixLift 6447618
  have htrace : WordTrace (prefixWord ++ tailWord_6447618) baseStart_6447618 baseEnd_6447618 := by
    simpa [prefixWord, tailWord_6447618, baseEnd_6447618] using wordTrace_append hprefix tailTrace_6447618
  have hstable : (prefixWord ++ tailWord_6447618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447618).length < 2 ^ (prefixWord ++ tailWord_6447618).sum := by decide
  have hdescent : baseEnd_6447618 < baseStart_6447618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447741 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_6447741 : Nat := 118140960795 + 6447741 * 2 ^ 59
def prefixEnd_6447741 : Nat := 4983230072969 + 3 ^ 40 * 6447741 * 2
def baseEnd_6447741 : Nat := 1103596756233787639128295

theorem tailTrace_6447741 : CollatzResearch.WordTrace tailWord_6447741 prefixEnd_6447741 1103596756233787639128295 := by
  unfold tailWord_6447741
  simp only [CollatzResearch.WordTrace]
  refine ⟨235168434133943018337975077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156778956089295345558650051 235168434133943018337975077)
  ·
    refine ⟨44094081400114315938370327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235168434133943018337975077 44094081400114315938370327)
    ·
      refine ⟨66141122100171473907555491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44094081400114315938370327 66141122100171473907555491)
      ·
        refine ⟨99211683150257210861333237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66141122100171473907555491 99211683150257210861333237)
        ·
          refine ⟨9301095295336613518249991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99211683150257210861333237 9301095295336613518249991)
          ·
            refine ⟨13951642943004920277374987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9301095295336613518249991 13951642943004920277374987)
            ·
              refine ⟨20927464414507380416062481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13951642943004920277374987 20927464414507380416062481)
              ·
                refine ⟨15695598310880535312046861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20927464414507380416062481 15695598310880535312046861)
                ·
                  refine ⟨5885849366580200742017573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15695598310880535312046861 5885849366580200742017573)
                  ·
                    refine ⟨1103596756233787639128295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5885849366580200742017573 1103596756233787639128295)
                    ·
                      rfl

theorem cell23_6447741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_6447741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447741 prefixEnd_6447741 := by exact prefixLift 6447741
  have htrace : WordTrace (prefixWord ++ tailWord_6447741) baseStart_6447741 baseEnd_6447741 := by
    simpa [prefixWord, tailWord_6447741, baseEnd_6447741] using wordTrace_append hprefix tailTrace_6447741
  have hstable : (prefixWord ++ tailWord_6447741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447741).length < 2 ^ (prefixWord ++ tailWord_6447741).sum := by decide
  have hdescent : baseEnd_6447741 < baseStart_6447741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447758 : List Nat := [4, 1, 1, 3, 1, 1, 4, 3, 1, 4]
def baseStart_6447758 : Nat := 118140960795 + 6447758 * 2 ^ 59
def prefixEnd_6447758 : Nat := 4983230072969 + 3 ^ 40 * 6447758 * 2
def baseEnd_6447758 : Nat := 1103599665957496450290769

theorem tailTrace_6447758 : CollatzResearch.WordTrace tailWord_6447758 prefixEnd_6447758 1103599665957496450290769 := by
  unfold tailWord_6447758
  simp only [CollatzResearch.WordTrace]
  refine ⟨29396131771860178780167991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156779369449920953494229285 29396131771860178780167991)
  ·
    refine ⟨44094197657790268170251987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29396131771860178780167991 44094197657790268170251987)
    ·
      refine ⟨66141296486685402255377981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44094197657790268170251987 66141296486685402255377981)
      ·
        refine ⟨24802986182507025845766743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66141296486685402255377981 24802986182507025845766743)
        ·
          refine ⟨37204479273760538768650115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24802986182507025845766743 37204479273760538768650115)
          ·
            refine ⟨55806718910640808152975173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37204479273760538768650115 55806718910640808152975173)
            ·
              refine ⟨10463759795745151528682845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55806718910640808152975173 10463759795745151528682845)
              ·
                refine ⟨3923909923404431823256067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10463759795745151528682845 3923909923404431823256067)
                ·
                  refine ⟨5885864885106647734884101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923909923404431823256067 5885864885106647734884101)
                  ·
                    refine ⟨1103599665957496450290769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5885864885106647734884101 1103599665957496450290769)
                    ·
                      rfl

theorem cell23_6447758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_6447758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447758 prefixEnd_6447758 := by exact prefixLift 6447758
  have htrace : WordTrace (prefixWord ++ tailWord_6447758) baseStart_6447758 baseEnd_6447758 := by
    simpa [prefixWord, tailWord_6447758, baseEnd_6447758] using wordTrace_append hprefix tailTrace_6447758
  have hstable : (prefixWord ++ tailWord_6447758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447758).length < 2 ^ (prefixWord ++ tailWord_6447758).sum := by decide
  have hdescent : baseEnd_6447758 < baseStart_6447758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447774 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_6447774 : Nat := 118140960795 + 6447774 * 2 ^ 59
def prefixEnd_6447774 : Nat := 4983230072969 + 3 ^ 40 * 6447774 * 2
def baseEnd_6447774 : Nat := 3310807213562961288272233

theorem tailTrace_6447774 : CollatzResearch.WordTrace tailWord_6447774 prefixEnd_6447774 3310807213562961288272233 := by
  unfold tailWord_6447774
  simp only [CollatzResearch.WordTrace]
  refine ⟨29396204717852933121740797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156779758495215643315950917 29396204717852933121740797)
  ·
    refine ⟨11023576769194849920652799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29396204717852933121740797 11023576769194849920652799)
    ·
      refine ⟨16535365153792274880979199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11023576769194849920652799 16535365153792274880979199)
      ·
        refine ⟨24803047730688412321468799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16535365153792274880979199 24803047730688412321468799)
        ·
          refine ⟨37204571596032618482203199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24803047730688412321468799 37204571596032618482203199)
          ·
            refine ⟨55806857394048927723304799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37204571596032618482203199 55806857394048927723304799)
            ·
              refine ⟨83710286091073391584957199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55806857394048927723304799 83710286091073391584957199)
              ·
                refine ⟨125565429136610087377435799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83710286091073391584957199 125565429136610087377435799)
                ·
                  refine ⟨188348143704915131066153699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125565429136610087377435799 188348143704915131066153699)
                  ·
                    refine ⟨282522215557372696599230549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188348143704915131066153699 282522215557372696599230549)
                    ·
                      refine ⟨3310807213562961288272233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 282522215557372696599230549 3310807213562961288272233)
                      ·
                        rfl

theorem cell23_6447774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_6447774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447774 prefixEnd_6447774 := by exact prefixLift 6447774
  have htrace : WordTrace (prefixWord ++ tailWord_6447774) baseStart_6447774 baseEnd_6447774 := by
    simpa [prefixWord, tailWord_6447774, baseEnd_6447774] using wordTrace_append hprefix tailTrace_6447774
  have hstable : (prefixWord ++ tailWord_6447774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447774).length < 2 ^ (prefixWord ++ tailWord_6447774).sum := by decide
  have hdescent : baseEnd_6447774 < baseStart_6447774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447809 : List Nat := [1, 2, 6, 2, 2, 1, 1, 3, 1, 4]
def baseStart_6447809 : Nat := 118140960795 + 6447809 * 2 ^ 59
def prefixEnd_6447809 : Nat := 4983230072969 + 3 ^ 40 * 6447809 * 2
def baseEnd_6447809 : Nat := 1103608395128622883778191

theorem tailTrace_6447809 : CollatzResearch.WordTrace tailWord_6447809 prefixEnd_6447809 1103608395128622883778191 := by
  unfold tailWord_6447809
  simp only [CollatzResearch.WordTrace]
  refine ⟨235170914297696665951450481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156780609531797777300966987 235170914297696665951450481)
  ·
    refine ⟨176378185723272499463587861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235170914297696665951450481 176378185723272499463587861)
    ·
      refine ⟨8267727455778398412355681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 176378185723272499463587861 8267727455778398412355681)
      ·
        refine ⟨6200795591833798809266761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8267727455778398412355681 6200795591833798809266761)
        ·
          refine ⟨4650596693875349106950071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6200795591833798809266761 4650596693875349106950071)
          ·
            refine ⟨6975895040813023660425107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4650596693875349106950071 6975895040813023660425107)
            ·
              refine ⟨10463842561219535490637661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6975895040813023660425107 10463842561219535490637661)
              ·
                refine ⟨3923940960457325808989123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10463842561219535490637661 3923940960457325808989123)
                ·
                  refine ⟨5885911440685988713483685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923940960457325808989123 5885911440685988713483685)
                  ·
                    refine ⟨1103608395128622883778191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5885911440685988713483685 1103608395128622883778191)
                    ·
                      rfl

theorem cell23_6447809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_6447809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447809 prefixEnd_6447809 := by exact prefixLift 6447809
  have htrace : WordTrace (prefixWord ++ tailWord_6447809) baseStart_6447809 baseEnd_6447809 := by
    simpa [prefixWord, tailWord_6447809, baseEnd_6447809] using wordTrace_append hprefix tailTrace_6447809
  have hstable : (prefixWord ++ tailWord_6447809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447809).length < 2 ^ (prefixWord ++ tailWord_6447809).sum := by decide
  have hdescent : baseEnd_6447809 < baseStart_6447809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447844 : List Nat := [2, 3, 1, 1, 1, 5, 2, 8]
def baseStart_6447844 : Nat := 118140960795 + 6447844 * 2 ^ 59
def prefixEnd_6447844 : Nat := 4983230072969 + 3 ^ 40 * 6447844 * 2
def baseEnd_6447844 : Nat := 122623820637362074607293

theorem tailTrace_6447844 : CollatzResearch.WordTrace tailWord_6447844 prefixEnd_6447844 122623820637362074607293 := by
  unfold tailWord_6447844
  simp only [CollatzResearch.WordTrace]
  refine ⟨117586095426284933464487293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156781460568379911285983057 117586095426284933464487293)
  ·
    refine ⟨44094785784856850049182735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117586095426284933464487293 44094785784856850049182735)
    ·
      refine ⟨66142178677285275073774103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44094785784856850049182735 66142178677285275073774103)
      ·
        refine ⟨99213268015927912610661155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66142178677285275073774103 99213268015927912610661155)
        ·
          refine ⟨148819902023891868915991733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99213268015927912610661155 148819902023891868915991733)
          ·
            refine ⟨13951865814739862710874225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148819902023891868915991733 13951865814739862710874225)
            ·
              refine ⟨10463899361054897033155669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13951865814739862710874225 10463899361054897033155669)
              ·
                refine ⟨122623820637362074607293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10463899361054897033155669 122623820637362074607293)
                ·
                  rfl

theorem cell23_6447844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 8].length) (baseStart_6447844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447844 prefixEnd_6447844 := by exact prefixLift 6447844
  have htrace : WordTrace (prefixWord ++ tailWord_6447844) baseStart_6447844 baseEnd_6447844 := by
    simpa [prefixWord, tailWord_6447844, baseEnd_6447844] using wordTrace_append hprefix tailTrace_6447844
  have hstable : (prefixWord ++ tailWord_6447844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447844).length < 2 ^ (prefixWord ++ tailWord_6447844).sum := by decide
  have hdescent : baseEnd_6447844 < baseStart_6447844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447848 : List Nat := [2, 1, 4, 1, 4, 1, 1, 3, 2, 4]
def baseStart_6447848 : Nat := 118140960795 + 6447848 * 2 ^ 59
def prefixEnd_6447848 : Nat := 4983230072969 + 3 ^ 40 * 6447848 * 2
def baseEnd_6447848 : Nat := 1103615070377131332915631

theorem tailTrace_6447848 : CollatzResearch.WordTrace tailWord_6447848 prefixEnd_6447848 1103615070377131332915631 := by
  unfold tailWord_6447848
  simp only [CollatzResearch.WordTrace]
  refine ⟨117586168372277687806060099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156781557829703583741413465 117586168372277687806060099)
  ·
    refine ⟨176379252558416531709090149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117586168372277687806060099 176379252558416531709090149)
    ·
      refine ⟨33071109854703099695454403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176379252558416531709090149 33071109854703099695454403)
      ·
        refine ⟨49606664782054649543181605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33071109854703099695454403 49606664782054649543181605)
        ·
          refine ⟨9301249646635246789346551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49606664782054649543181605 9301249646635246789346551)
          ·
            refine ⟨13951874469952870184019827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9301249646635246789346551 13951874469952870184019827)
            ·
              refine ⟨20927811704929305276029741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13951874469952870184019827 20927811704929305276029741)
              ·
                refine ⟨7847929389348489478511153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20927811704929305276029741 7847929389348489478511153)
                ·
                  refine ⟨5885947042011367108883365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7847929389348489478511153 5885947042011367108883365)
                  ·
                    refine ⟨1103615070377131332915631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5885947042011367108883365 1103615070377131332915631)
                    ·
                      rfl

theorem cell23_6447848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_6447848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447848 prefixEnd_6447848 := by exact prefixLift 6447848
  have htrace : WordTrace (prefixWord ++ tailWord_6447848) baseStart_6447848 baseEnd_6447848 := by
    simpa [prefixWord, tailWord_6447848, baseEnd_6447848] using wordTrace_append hprefix tailTrace_6447848
  have hstable : (prefixWord ++ tailWord_6447848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447848).length < 2 ^ (prefixWord ++ tailWord_6447848).sum := by decide
  have hdescent : baseEnd_6447848 < baseStart_6447848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447858 : List Nat := [3, 2, 1, 3, 1, 2, 3, 2, 1, 2, 3]
def baseStart_6447858 : Nat := 118140960795 + 6447858 * 2 ^ 59
def prefixEnd_6447858 : Nat := 4983230072969 + 3 ^ 40 * 6447858 * 2
def baseEnd_6447858 : Nat := 3310850345937938959621847

theorem tailTrace_6447858 : CollatzResearch.WordTrace tailWord_6447858 prefixEnd_6447858 3310850345937938959621847 := by
  unfold tailWord_6447858
  simp only [CollatzResearch.WordTrace]
  refine ⟨58793175368629786829996057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156781800983012764879989485 58793175368629786829996057)
  ·
    refine ⟨44094881526472340122497043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58793175368629786829996057 44094881526472340122497043)
    ·
      refine ⟨66142322289708510183745565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44094881526472340122497043 66142322289708510183745565)
      ·
        refine ⟨24803370858640691318904587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66142322289708510183745565 24803370858640691318904587)
        ·
          refine ⟨37205056287961036978356881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24803370858640691318904587 37205056287961036978356881)
          ·
            refine ⟨27903792215970777733767661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37205056287961036978356881 27903792215970777733767661)
            ·
              refine ⟨10463922080989041650162873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27903792215970777733767661 10463922080989041650162873)
              ·
                refine ⟨7847941560741781237622155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10463922080989041650162873 7847941560741781237622155)
                ·
                  refine ⟨11771912341112671856433233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7847941560741781237622155 11771912341112671856433233)
                  ·
                    refine ⟨8828934255834503892324925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11771912341112671856433233 8828934255834503892324925)
                    ·
                      refine ⟨3310850345937938959621847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8828934255834503892324925 3310850345937938959621847)
                      ·
                        rfl

theorem cell23_6447858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_6447858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447858 prefixEnd_6447858 := by exact prefixLift 6447858
  have htrace : WordTrace (prefixWord ++ tailWord_6447858) baseStart_6447858 baseEnd_6447858 := by
    simpa [prefixWord, tailWord_6447858, baseEnd_6447858] using wordTrace_append hprefix tailTrace_6447858
  have hstable : (prefixWord ++ tailWord_6447858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447858).length < 2 ^ (prefixWord ++ tailWord_6447858).sum := by decide
  have hdescent : baseEnd_6447858 < baseStart_6447858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447867 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 7]
def baseStart_6447867 : Nat := 118140960795 + 6447867 * 2 ^ 59
def prefixEnd_6447867 : Nat := 4983230072969 + 3 ^ 40 * 6447867 * 2
def baseEnd_6447867 : Nat := 3310854967263829424409305

theorem tailTrace_6447867 : CollatzResearch.WordTrace tailWord_6447867 prefixEnd_6447867 3310854967263829424409305 := by
  unfold tailWord_6447867
  simp only [CollatzResearch.WordTrace]
  refine ⟨235173029731486541857061855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156782019820991027904707903 235173029731486541857061855)
  ·
    refine ⟨352759544597229812785592783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235173029731486541857061855 352759544597229812785592783)
    ·
      refine ⟨529139316895844719178389175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352759544597229812785592783 529139316895844719178389175)
      ·
        refine ⟨793708975343767078767583763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529139316895844719178389175 793708975343767078767583763)
        ·
          refine ⟨1190563463015650618151375645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793708975343767078767583763 1190563463015650618151375645)
          ·
            refine ⟨446461298630868981806765867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1190563463015650618151375645 446461298630868981806765867)
            ·
              refine ⟨669691947946303472710148801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446461298630868981806765867 669691947946303472710148801)
              ·
                refine ⟨502268960959727604532611601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669691947946303472710148801 502268960959727604532611601)
                ·
                  refine ⟨376701720719795703399458701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502268960959727604532611601 376701720719795703399458701)
                  ·
                    refine ⟨141263145269923388774797013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 376701720719795703399458701 141263145269923388774797013)
                    ·
                      refine ⟨3310854967263829424409305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141263145269923388774797013 3310854967263829424409305)
                      ·
                        rfl

theorem cell23_6447867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_6447867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447867 prefixEnd_6447867 := by exact prefixLift 6447867
  have htrace : WordTrace (prefixWord ++ tailWord_6447867) baseStart_6447867 baseEnd_6447867 := by
    simpa [prefixWord, tailWord_6447867, baseEnd_6447867] using wordTrace_append hprefix tailTrace_6447867
  have hstable : (prefixWord ++ tailWord_6447867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447867).length < 2 ^ (prefixWord ++ tailWord_6447867).sum := by decide
  have hdescent : baseEnd_6447867 < baseStart_6447867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447878 : List Nat := [6, 2, 2, 13]
def baseStart_6447878 : Nat := 118140960795 + 6447878 * 2 ^ 59
def prefixEnd_6447878 : Nat := 4983230072969 + 3 ^ 40 * 6447878 * 2
def baseEnd_6447878 : Nat := 1513882311637416040865

theorem tailTrace_6447878 : CollatzResearch.WordTrace tailWord_6447878 prefixEnd_6447878 1513882311637416040865 := by
  unfold tailWord_6447878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7349169716701459085491009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156782287289631127157141525 7349169716701459085491009)
  ·
    refine ⟨5511877287526094314118257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7349169716701459085491009 5511877287526094314118257)
    ·
      refine ⟨4133907965644570735588693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5511877287526094314118257 4133907965644570735588693)
      ·
        refine ⟨1513882311637416040865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4133907965644570735588693 1513882311637416040865)
        ·
          rfl

theorem cell23_6447878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 13].length) (baseStart_6447878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447878 prefixEnd_6447878 := by exact prefixLift 6447878
  have htrace : WordTrace (prefixWord ++ tailWord_6447878) baseStart_6447878 baseEnd_6447878 := by
    simpa [prefixWord, tailWord_6447878, baseEnd_6447878] using wordTrace_append hprefix tailTrace_6447878
  have hstable : (prefixWord ++ tailWord_6447878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447878).length < 2 ^ (prefixWord ++ tailWord_6447878).sum := by decide
  have hdescent : baseEnd_6447878 < baseStart_6447878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447904 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 1, 8]
def baseStart_6447904 : Nat := 118140960795 + 6447904 * 2 ^ 59
def prefixEnd_6447904 : Nat := 4983230072969 + 3 ^ 40 * 6447904 * 2
def baseEnd_6447904 : Nat := 1103624655349348593215545

theorem tailTrace_6447904 : CollatzResearch.WordTrace tailWord_6447904 prefixEnd_6447904 1103624655349348593215545 := by
  unfold tailWord_6447904
  simp only [CollatzResearch.WordTrace]
  refine ⟨117587189616176248588079383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156782919488234998117439177 117587189616176248588079383)
  ·
    refine ⟨176380784424264372882119075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117587189616176248588079383 176380784424264372882119075)
    ·
      refine ⟨264571176636396559323178613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176380784424264372882119075 264571176636396559323178613)
      ·
        refine ⟨24803547809662177436547995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 264571176636396559323178613 24803547809662177436547995)
        ·
          refine ⟨37205321714493266154821993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24803547809662177436547995 37205321714493266154821993)
          ·
            refine ⟨27903991285869949616116495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37205321714493266154821993 27903991285869949616116495)
            ·
              refine ⟨41855986928804924424174743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27903991285869949616116495 41855986928804924424174743)
              ·
                refine ⟨62783980393207386636262115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41855986928804924424174743 62783980393207386636262115)
                ·
                  refine ⟨94175970589811079954393173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62783980393207386636262115 94175970589811079954393173)
                  ·
                    refine ⟨1103624655349348593215545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94175970589811079954393173 1103624655349348593215545)
                    ·
                      rfl

theorem cell23_6447904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 8].length) (baseStart_6447904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447904 prefixEnd_6447904 := by exact prefixLift 6447904
  have htrace : WordTrace (prefixWord ++ tailWord_6447904) baseStart_6447904 baseEnd_6447904 := by
    simpa [prefixWord, tailWord_6447904, baseEnd_6447904] using wordTrace_append hprefix tailTrace_6447904
  have hstable : (prefixWord ++ tailWord_6447904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447904).length < 2 ^ (prefixWord ++ tailWord_6447904).sum := by decide
  have hdescent : baseEnd_6447904 < baseStart_6447904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447928 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 4, 2, 2]
def baseStart_6447928 : Nat := 118140960795 + 6447928 * 2 ^ 59
def prefixEnd_6447928 : Nat := 4983230072969 + 3 ^ 40 * 6447928 * 2
def baseEnd_6447928 : Nat := 3310886289583753685746525

theorem tailTrace_6447928 : CollatzResearch.WordTrace tailWord_6447928 prefixEnd_6447928 3310886289583753685746525 := by
  unfold tailWord_6447928
  simp only [CollatzResearch.WordTrace]
  refine ⟨117587627292132774637516219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156783503056177032850021625 117587627292132774637516219)
  ·
    refine ⟨176381440938199161956274329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117587627292132774637516219 176381440938199161956274329)
    ·
      refine ⟨132286080703649371467205747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176381440938199161956274329 132286080703649371467205747)
      ·
        refine ⟨198429121055474057200808621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132286080703649371467205747 198429121055474057200808621)
        ·
          refine ⟨74410920395802771450303233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198429121055474057200808621 74410920395802771450303233)
          ·
            refine ⟨55808190296852078587727425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74410920395802771450303233 55808190296852078587727425)
            ·
              refine ⟨41856142722639058940795569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55808190296852078587727425 41856142722639058940795569)
              ·
                refine ⟨31392107041979294205596677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41856142722639058940795569 31392107041979294205596677)
                ·
                  refine ⟨5886020070371117663549377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31392107041979294205596677 5886020070371117663549377)
                  ·
                    refine ⟨4414515052778338247662033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5886020070371117663549377 4414515052778338247662033)
                    ·
                      refine ⟨3310886289583753685746525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414515052778338247662033 3310886289583753685746525)
                      ·
                        rfl

theorem cell23_6447928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 4, 2, 2].length) (baseStart_6447928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447928 prefixEnd_6447928 := by exact prefixLift 6447928
  have htrace : WordTrace (prefixWord ++ tailWord_6447928) baseStart_6447928 baseEnd_6447928 := by
    simpa [prefixWord, tailWord_6447928, baseEnd_6447928] using wordTrace_append hprefix tailTrace_6447928
  have hstable : (prefixWord ++ tailWord_6447928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447928).length < 2 ^ (prefixWord ++ tailWord_6447928).sum := by decide
  have hdescent : baseEnd_6447928 < baseStart_6447928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447945 : List Nat := [1, 2, 1, 1, 2, 5, 3, 2, 2, 2, 2]
def baseStart_6447945 : Nat := 118140960795 + 6447945 * 2 ^ 59
def prefixEnd_6447945 : Nat := 4983230072969 + 3 ^ 40 * 6447945 * 2
def baseEnd_6447945 : Nat := 3310895018754880119233947

theorem tailTrace_6447945 : CollatzResearch.WordTrace tailWord_6447945 prefixEnd_6447945 3310895018754880119233947 := by
  unfold tailWord_6447945
  simp only [CollatzResearch.WordTrace]
  refine ⟨235175874625203961178401289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156783916416802640785600859 235175874625203961178401289)
  ·
    refine ⟨176381905968902970883800967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235175874625203961178401289 176381905968902970883800967)
    ·
      refine ⟨264572858953354456325701451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176381905968902970883800967 264572858953354456325701451)
      ·
        refine ⟨396859288430031684488552177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264572858953354456325701451 396859288430031684488552177)
        ·
          refine ⟨297644466322523763366414133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396859288430031684488552177 297644466322523763366414133)
          ·
            refine ⟨27904168717736602815601325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 297644466322523763366414133 27904168717736602815601325)
            ·
              refine ⟨10464063269151226055850497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27904168717736602815601325 10464063269151226055850497)
              ·
                refine ⟨7848047451863419541887873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10464063269151226055850497 7848047451863419541887873)
                ·
                  refine ⟨5886035588897564656415905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7848047451863419541887873 5886035588897564656415905)
                  ·
                    refine ⟨4414526691673173492311929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5886035588897564656415905 4414526691673173492311929)
                    ·
                      refine ⟨3310895018754880119233947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414526691673173492311929 3310895018754880119233947)
                      ·
                        rfl

theorem cell23_6447945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 2, 2].length) (baseStart_6447945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447945 prefixEnd_6447945 := by exact prefixLift 6447945
  have htrace : WordTrace (prefixWord ++ tailWord_6447945) baseStart_6447945 baseEnd_6447945 := by
    simpa [prefixWord, tailWord_6447945, baseEnd_6447945] using wordTrace_append hprefix tailTrace_6447945
  have hstable : (prefixWord ++ tailWord_6447945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447945).length < 2 ^ (prefixWord ++ tailWord_6447945).sum := by decide
  have hdescent : baseEnd_6447945 < baseStart_6447945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447961 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 2, 3, 3]
def baseStart_6447961 : Nat := 118140960795 + 6447961 * 2 ^ 59
def prefixEnd_6447961 : Nat := 4983230072969 + 3 ^ 40 * 6447961 * 2
def baseEnd_6447961 : Nat := 3310903234445352056633873

theorem tailTrace_6447961 : CollatzResearch.WordTrace tailWord_6447961 prefixEnd_6447961 3310903234445352056633873 := by
  unfold tailWord_6447961
  simp only [CollatzResearch.WordTrace]
  refine ⟨235176458193145995910983737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156784305462097330607322491 235176458193145995910983737)
  ·
    refine ⟨176382343644859496933237803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235176458193145995910983737 176382343644859496933237803)
    ·
      refine ⟨264573515467289245399856705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176382343644859496933237803 264573515467289245399856705)
      ·
        refine ⟨198430136600466934049892529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264573515467289245399856705 198430136600466934049892529)
        ·
          refine ⟨148822602450350200537419397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198430136600466934049892529 148822602450350200537419397)
          ·
            refine ⟨27904237959440662600766137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148822602450350200537419397 27904237959440662600766137)
            ·
              refine ⟨20928178469580496950574603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27904237959440662600766137 20928178469580496950574603)
              ·
                refine ⟨31392267704370745425861905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20928178469580496950574603 31392267704370745425861905)
                ·
                  refine ⟨23544200778278059069396429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31392267704370745425861905 23544200778278059069396429)
                  ·
                    refine ⟨8829075291854272151023661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23544200778278059069396429 8829075291854272151023661)
                    ·
                      refine ⟨3310903234445352056633873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8829075291854272151023661 3310903234445352056633873)
                      ·
                        rfl

theorem cell23_6447961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_6447961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447961 prefixEnd_6447961 := by exact prefixLift 6447961
  have htrace : WordTrace (prefixWord ++ tailWord_6447961) baseStart_6447961 baseEnd_6447961 := by
    simpa [prefixWord, tailWord_6447961, baseEnd_6447961] using wordTrace_append hprefix tailTrace_6447961
  have hstable : (prefixWord ++ tailWord_6447961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447961).length < 2 ^ (prefixWord ++ tailWord_6447961).sum := by decide
  have hdescent : baseEnd_6447961 < baseStart_6447961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447962 : List Nat := [3, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2]
def baseStart_6447962 : Nat := 118140960795 + 6447962 * 2 ^ 59
def prefixEnd_6447962 : Nat := 4983230072969 + 3 ^ 40 * 6447962 * 2
def baseEnd_6447962 : Nat := 3310903747926006552721369

theorem tailTrace_6447962 : CollatzResearch.WordTrace tailWord_6447962 prefixEnd_6447962 3310903747926006552721369 := by
  unfold tailWord_6447962
  simp only [CollatzResearch.WordTrace]
  refine ⟨58794123666535593270442535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156784329777428248721180093 58794123666535593270442535)
  ·
    refine ⟨88191185499803389905663803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58794123666535593270442535 88191185499803389905663803)
    ·
      refine ⟨132286778249705084858495705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88191185499803389905663803 132286778249705084858495705)
      ·
        refine ⟨99215083687278813643871779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132286778249705084858495705 99215083687278813643871779)
        ·
          refine ⟨148822625530918220465807669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99215083687278813643871779 148822625530918220465807669)
          ·
            refine ⟨13952121143523583168669469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148822625530918220465807669 13952121143523583168669469)
            ·
              refine ⟨5232045428821343688251051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13952121143523583168669469 5232045428821343688251051)
              ·
                refine ⟨7848068143232015532376577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5232045428821343688251051 7848068143232015532376577)
                ·
                  refine ⟨5886051107424011649282433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7848068143232015532376577 5886051107424011649282433)
                  ·
                    refine ⟨4414538330568008736961825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5886051107424011649282433 4414538330568008736961825)
                    ·
                      refine ⟨3310903747926006552721369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414538330568008736961825 3310903747926006552721369)
                      ·
                        rfl

theorem cell23_6447962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_6447962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447962 prefixEnd_6447962 := by exact prefixLift 6447962
  have htrace : WordTrace (prefixWord ++ tailWord_6447962) baseStart_6447962 baseEnd_6447962 := by
    simpa [prefixWord, tailWord_6447962, baseEnd_6447962] using wordTrace_append hprefix tailTrace_6447962
  have hstable : (prefixWord ++ tailWord_6447962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447962).length < 2 ^ (prefixWord ++ tailWord_6447962).sum := by decide
  have hdescent : baseEnd_6447962 < baseStart_6447962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447981 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_6447981 : Nat := 118140960795 + 6447981 * 2 ^ 59
def prefixEnd_6447981 : Nat := 4983230072969 + 3 ^ 40 * 6447981 * 2
def baseEnd_6447981 : Nat := 1103637834686147326127927

theorem tailTrace_6447981 : CollatzResearch.WordTrace tailWord_6447981 prefixEnd_6447981 1103637834686147326127927 := by
  unfold tailWord_6447981
  simp only [CollatzResearch.WordTrace]
  refine ⟨235177187653073539326711797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156784791768715692884474531 235177187653073539326711797)
  ·
    refine ⟨22047861342475644311879231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235177187653073539326711797 22047861342475644311879231)
    ·
      refine ⟨33071792013713466467818847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22047861342475644311879231 33071792013713466467818847)
      ·
        refine ⟨49607688020570199701728271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33071792013713466467818847 49607688020570199701728271)
        ·
          refine ⟨74411532030855299552592407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49607688020570199701728271 74411532030855299552592407)
          ·
            refine ⟨111617298046282949328888611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74411532030855299552592407 111617298046282949328888611)
            ·
              refine ⟨167425947069424423993332917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111617298046282949328888611 167425947069424423993332917)
              ·
                refine ⟨15696182537758539749374961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167425947069424423993332917 15696182537758539749374961)
                ·
                  refine ⟨11772136903318904812031221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15696182537758539749374961 11772136903318904812031221)
                  ·
                    refine ⟨1103637834686147326127927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11772136903318904812031221 1103637834686147326127927)
                    ·
                      rfl

theorem cell23_6447981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_6447981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447981 prefixEnd_6447981 := by exact prefixLift 6447981
  have htrace : WordTrace (prefixWord ++ tailWord_6447981) baseStart_6447981 baseEnd_6447981 := by
    simpa [prefixWord, tailWord_6447981, baseEnd_6447981] using wordTrace_append hprefix tailTrace_6447981
  have hstable : (prefixWord ++ tailWord_6447981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447981).length < 2 ^ (prefixWord ++ tailWord_6447981).sum := by decide
  have hdescent : baseEnd_6447981 < baseStart_6447981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448002 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 7]
def baseStart_6448002 : Nat := 118140960795 + 6448002 * 2 ^ 59
def prefixEnd_6448002 : Nat := 4983230072969 + 3 ^ 40 * 6448002 * 2
def baseEnd_6448002 : Nat := 367880476350242932913465

theorem tailTrace_6448002 : CollatzResearch.WordTrace tailWord_6448002 prefixEnd_6448002 367880476350242932913465 := by
  unfold tailWord_6448002
  simp only [CollatzResearch.WordTrace]
  refine ⟨58794488396499364978306565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156785302390664973275484173 58794488396499364978306565)
  ·
    refine ⟨11023966574343630933432481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58794488396499364978306565 11023966574343630933432481)
    ·
      refine ⟨8267974930757723200074361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11023966574343630933432481 8267974930757723200074361)
      ·
        refine ⟨6200981198068292400055771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8267974930757723200074361 6200981198068292400055771)
        ·
          refine ⟨9301471797102438600083657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6200981198068292400055771 9301471797102438600083657)
          ·
            refine ⟨6976103847826828950062743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9301471797102438600083657 6976103847826828950062743)
            ·
              refine ⟨10464155771740243425094115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6976103847826828950062743 10464155771740243425094115)
              ·
                refine ⟨15696233657610365137641173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10464155771740243425094115 15696233657610365137641173)
                ·
                  refine ⟨367880476350242932913465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15696233657610365137641173 367880476350242932913465)
                  ·
                    rfl

theorem cell23_6448002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_6448002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448002 prefixEnd_6448002 := by exact prefixLift 6448002
  have htrace : WordTrace (prefixWord ++ tailWord_6448002) baseStart_6448002 baseEnd_6448002 := by
    simpa [prefixWord, tailWord_6448002, baseEnd_6448002] using wordTrace_append hprefix tailTrace_6448002
  have hstable : (prefixWord ++ tailWord_6448002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448002).length < 2 ^ (prefixWord ++ tailWord_6448002).sum := by decide
  have hdescent : baseEnd_6448002 < baseStart_6448002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448071 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 3, 5]
def baseStart_6448071 : Nat := 118140960795 + 6448071 * 2 ^ 59
def prefixEnd_6448071 : Nat := 4983230072969 + 3 ^ 40 * 6448071 * 2
def baseEnd_6448071 : Nat := 1103653239105782208752789

theorem tailTrace_6448071 : CollatzResearch.WordTrace tailWord_6448071 prefixEnd_6448071 1103653239105782208752789 := by
  unfold tailWord_6448071
  simp only [CollatzResearch.WordTrace]
  refine ⟨235180470222747484697488067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156786980148498323131658711 235180470222747484697488067)
  ·
    refine ⟨352770705334121227046232101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235180470222747484697488067 352770705334121227046232101)
    ·
      refine ⟨66144507250147730071168519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 352770705334121227046232101 66144507250147730071168519)
      ·
        refine ⟨99216760875221595106752779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66144507250147730071168519 99216760875221595106752779)
        ·
          refine ⟨148825141312832392660129169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99216760875221595106752779 148825141312832392660129169)
          ·
            refine ⟨111618855984624294495096877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148825141312832392660129169 111618855984624294495096877)
            ·
              refine ⟨41857070994234110435661329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111618855984624294495096877 41857070994234110435661329)
              ·
                refine ⟨31392803245675582826745997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41857070994234110435661329 31392803245675582826745997)
                ·
                  refine ⟨11772301217128343560029749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31392803245675582826745997 11772301217128343560029749)
                  ·
                    refine ⟨1103653239105782208752789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11772301217128343560029749 1103653239105782208752789)
                    ·
                      rfl

theorem cell23_6448071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_6448071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448071 prefixEnd_6448071 := by exact prefixLift 6448071
  have htrace : WordTrace (prefixWord ++ tailWord_6448071) baseStart_6448071 baseEnd_6448071 := by
    simpa [prefixWord, tailWord_6448071, baseEnd_6448071] using wordTrace_append hprefix tailTrace_6448071
  have hstable : (prefixWord ++ tailWord_6448071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448071).length < 2 ^ (prefixWord ++ tailWord_6448071).sum := by decide
  have hdescent : baseEnd_6448071 < baseStart_6448071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448095 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 1, 5, 2]
def baseStart_6448095 : Nat := 118140960795 + 6448095 * 2 ^ 59
def prefixEnd_6448095 : Nat := 4983230072969 + 3 ^ 40 * 6448095 * 2
def baseEnd_6448095 : Nat := 3310972040853054532358257

theorem tailTrace_6448095 : CollatzResearch.WordTrace tailWord_6448095 prefixEnd_6448095 3310972040853054532358257 := by
  unfold tailWord_6448095
  simp only [CollatzResearch.WordTrace]
  refine ⟨235181345574660536796361739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156787563716440357864241159 235181345574660536796361739)
  ·
    refine ⟨352772018361990805194542609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235181345574660536796361739 352772018361990805194542609)
    ·
      refine ⟨264579013771493103895906957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352772018361990805194542609 264579013771493103895906957)
      ·
        refine ⟨99217130164309913960965109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264579013771493103895906957 99217130164309913960965109)
        ·
          refine ⟨9301605952904054433840479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99217130164309913960965109 9301605952904054433840479)
          ·
            refine ⟨13952408929356081650760719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9301605952904054433840479 13952408929356081650760719)
            ·
              refine ⟨20928613394034122476141079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13952408929356081650760719 20928613394034122476141079)
              ·
                refine ⟨31392920091051183714211619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20928613394034122476141079 31392920091051183714211619)
                ·
                  refine ⟨47089380136576775571317429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31392920091051183714211619 47089380136576775571317429)
                  ·
                    refine ⟨4414629387804072709811009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47089380136576775571317429 4414629387804072709811009)
                    ·
                      refine ⟨3310972040853054532358257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414629387804072709811009 3310972040853054532358257)
                      ·
                        rfl

theorem cell23_6448095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_6448095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448095 prefixEnd_6448095 := by exact prefixLift 6448095
  have htrace : WordTrace (prefixWord ++ tailWord_6448095) baseStart_6448095 baseEnd_6448095 := by
    simpa [prefixWord, tailWord_6448095, baseEnd_6448095] using wordTrace_append hprefix tailTrace_6448095
  have hstable : (prefixWord ++ tailWord_6448095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448095).length < 2 ^ (prefixWord ++ tailWord_6448095).sum := by decide
  have hdescent : baseEnd_6448095 < baseStart_6448095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448121 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 6]
def baseStart_6448121 : Nat := 118140960795 + 6448121 * 2 ^ 59
def prefixEnd_6448121 : Nat := 4983230072969 + 3 ^ 40 * 6448121 * 2
def baseEnd_6448121 : Nat := 3310985391350071430633137

theorem tailTrace_6448121 : CollatzResearch.WordTrace tailWord_6448121 prefixEnd_6448121 3310985391350071430633137 := by
  unfold tailWord_6448121
  simp only [CollatzResearch.WordTrace]
  refine ⟨235182293872566343236808217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156788195915044228824538811 235182293872566343236808217)
  ·
    refine ⟨176386720404424757427606163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235182293872566343236808217 176386720404424757427606163)
    ·
      refine ⟨264580080606637136141409245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176386720404424757427606163 264580080606637136141409245)
      ·
        refine ⟨99217530227488926053028467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264580080606637136141409245 99217530227488926053028467)
        ·
          refine ⟨148826295341233389079542701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99217530227488926053028467 148826295341233389079542701)
          ·
            refine ⟨55809860752962520904828513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148826295341233389079542701 55809860752962520904828513)
            ·
              refine ⟨41857395564721890678621385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55809860752962520904828513 41857395564721890678621385)
              ·
                refine ⟨31393046673541418008966039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41857395564721890678621385 31393046673541418008966039)
                ·
                  refine ⟨47089570010312127013449059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31393046673541418008966039 47089570010312127013449059)
                  ·
                    refine ⟨70634355015468190520173589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47089570010312127013449059 70634355015468190520173589)
                    ·
                      refine ⟨3310985391350071430633137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70634355015468190520173589 3310985391350071430633137)
                      ·
                        rfl

theorem cell23_6448121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_6448121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448121 prefixEnd_6448121 := by exact prefixLift 6448121
  have htrace : WordTrace (prefixWord ++ tailWord_6448121) baseStart_6448121 baseEnd_6448121 := by
    simpa [prefixWord, tailWord_6448121, baseEnd_6448121] using wordTrace_append hprefix tailTrace_6448121
  have hstable : (prefixWord ++ tailWord_6448121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448121).length < 2 ^ (prefixWord ++ tailWord_6448121).sum := by decide
  have hdescent : baseEnd_6448121 < baseStart_6448121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448138 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_6448138 : Nat := 118140960795 + 6448138 * 2 ^ 59
def prefixEnd_6448138 : Nat := 4983230072969 + 3 ^ 40 * 6448138 * 2
def baseEnd_6448138 : Nat := 3310994120521197864120559

theorem tailTrace_6448138 : CollatzResearch.WordTrace tailWord_6448138 prefixEnd_6448138 3310994120521197864120559 := by
  unfold tailWord_6448138
  simp only [CollatzResearch.WordTrace]
  refine ⟨58795728478376188785044267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156788609275669836760118045 58795728478376188785044267)
  ·
    refine ⟨88193592717564283177566401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58795728478376188785044267 88193592717564283177566401)
    ·
      refine ⟨66145194538173212383174801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88193592717564283177566401 66145194538173212383174801)
      ·
        refine ⟨49608895903629909287381101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66145194538173212383174801 49608895903629909287381101)
        ·
          refine ⟨18603335963861215982767913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49608895903629909287381101 18603335963861215982767913)
          ·
            refine ⟨13952501972895911987075935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18603335963861215982767913 13952501972895911987075935)
            ·
              refine ⟨20928752959343867980613903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13952501972895911987075935 20928752959343867980613903)
              ·
                refine ⟨31393129439015801970920855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20928752959343867980613903 31393129439015801970920855)
                ·
                  refine ⟨47089694158523702956381283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31393129439015801970920855 47089694158523702956381283)
                  ·
                    refine ⟨70634541237785554434571925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47089694158523702956381283 70634541237785554434571925)
                    ·
                      refine ⟨3310994120521197864120559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70634541237785554434571925 3310994120521197864120559)
                      ·
                        rfl

theorem cell23_6448138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_6448138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448138 prefixEnd_6448138 := by exact prefixLift 6448138
  have htrace : WordTrace (prefixWord ++ tailWord_6448138) baseStart_6448138 baseEnd_6448138 := by
    simpa [prefixWord, tailWord_6448138, baseEnd_6448138] using wordTrace_append hprefix tailTrace_6448138
  have hstable : (prefixWord ++ tailWord_6448138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448138).length < 2 ^ (prefixWord ++ tailWord_6448138).sum := by decide
  have hdescent : baseEnd_6448138 < baseStart_6448138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448142 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2]
def baseStart_6448142 : Nat := 118140960795 + 6448142 * 2 ^ 59
def prefixEnd_6448142 : Nat := 4983230072969 + 3 ^ 40 * 6448142 * 2
def baseEnd_6448142 : Nat := 3310996174443815848470541

theorem tailTrace_6448142 : CollatzResearch.WordTrace tailWord_6448142 prefixEnd_6448142 3310996174443815848470541 := by
  unfold tailWord_6448142
  simp only [CollatzResearch.WordTrace]
  refine ⟨29397882475686282977915335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156788706536993509215548453 29397882475686282977915335)
  ·
    refine ⟨44096823713529424466873003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29397882475686282977915335 44096823713529424466873003)
    ·
      refine ⟨66145235570294136700309505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44096823713529424466873003 66145235570294136700309505)
      ·
        refine ⟨49608926677720602525232129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66145235570294136700309505 49608926677720602525232129)
        ·
          refine ⟨37206695008290451893924097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49608926677720602525232129 37206695008290451893924097)
          ·
            refine ⟨27905021256217838920443073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37206695008290451893924097 27905021256217838920443073)
            ·
              refine ⟨20928765942163379190332305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27905021256217838920443073 20928765942163379190332305)
              ·
                refine ⟨15696574456622534392749229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20928765942163379190332305 15696574456622534392749229)
                ·
                  refine ⟨5886215421233450397280961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15696574456622534392749229 5886215421233450397280961)
                  ·
                    refine ⟨4414661565925087797960721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5886215421233450397280961 4414661565925087797960721)
                    ·
                      refine ⟨3310996174443815848470541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414661565925087797960721 3310996174443815848470541)
                      ·
                        rfl

theorem cell23_6448142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_6448142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448142 prefixEnd_6448142 := by exact prefixLift 6448142
  have htrace : WordTrace (prefixWord ++ tailWord_6448142) baseStart_6448142 baseEnd_6448142 := by
    simpa [prefixWord, tailWord_6448142, baseEnd_6448142] using wordTrace_append hprefix tailTrace_6448142
  have hstable : (prefixWord ++ tailWord_6448142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448142).length < 2 ^ (prefixWord ++ tailWord_6448142).sum := by decide
  have hdescent : baseEnd_6448142 < baseStart_6448142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448159 : List Nat := [1, 1, 2, 4, 1, 3, 3, 3, 1, 2, 2]
def baseStart_6448159 : Nat := 118140960795 + 6448159 * 2 ^ 59
def prefixEnd_6448159 : Nat := 4983230072969 + 3 ^ 40 * 6448159 * 2
def baseEnd_6448159 : Nat := 3311004903614942281957963

theorem tailTrace_6448159 : CollatzResearch.WordTrace tailWord_6448159 prefixEnd_6448159 3311004903614942281957963 := by
  unfold tailWord_6448159
  simp only [CollatzResearch.WordTrace]
  refine ⟨235183679846428675726691531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156789119897619117151127687 235183679846428675726691531)
  ·
    refine ⟨352775519769643013590037297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235183679846428675726691531 352775519769643013590037297)
    ·
      refine ⟨264581639827232260192527973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352775519769643013590037297 264581639827232260192527973)
      ·
        refine ⟨49609057467606048786098995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264581639827232260192527973 49609057467606048786098995)
        ·
          refine ⟨74413586201409073179148493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49609057467606048786098995 74413586201409073179148493)
          ·
            refine ⟨27905094825528402442180685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74413586201409073179148493 27905094825528402442180685)
            ·
              refine ⟨10464410559573150915817757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27905094825528402442180685 10464410559573150915817757)
              ·
                refine ⟨3924153959839931593431659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10464410559573150915817757 3924153959839931593431659)
                ·
                  refine ⟨5886230939759897390147489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924153959839931593431659 5886230939759897390147489)
                  ·
                    refine ⟨4414673204819923042610617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5886230939759897390147489 4414673204819923042610617)
                    ·
                      refine ⟨3311004903614942281957963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414673204819923042610617 3311004903614942281957963)
                      ·
                        rfl

theorem cell23_6448159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_6448159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448159 prefixEnd_6448159 := by exact prefixLift 6448159
  have htrace : WordTrace (prefixWord ++ tailWord_6448159) baseStart_6448159 baseEnd_6448159 := by
    simpa [prefixWord, tailWord_6448159, baseEnd_6448159] using wordTrace_append hprefix tailTrace_6448159
  have hstable : (prefixWord ++ tailWord_6448159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448159).length < 2 ^ (prefixWord ++ tailWord_6448159).sum := by decide
  have hdescent : baseEnd_6448159 < baseStart_6448159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448171 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 5]
def baseStart_6448171 : Nat := 118140960795 + 6448171 * 2 ^ 59
def prefixEnd_6448171 : Nat := 4983230072969 + 3 ^ 40 * 6448171 * 2
def baseEnd_6448171 : Nat := 3311011065382796235007907

theorem tailTrace_6448171 : CollatzResearch.WordTrace tailWord_6448171 prefixEnd_6448171 3311011065382796235007907 := by
  unfold tailWord_6448171
  simp only [CollatzResearch.WordTrace]
  refine ⟨235184117522385201776128367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156789411681590134517418911 235184117522385201776128367)
  ·
    refine ⟨352776176283577802664192551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235184117522385201776128367 352776176283577802664192551)
    ·
      refine ⟨529164264425366703996288827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352776176283577802664192551 529164264425366703996288827)
      ·
        refine ⟨793746396638050055994433241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529164264425366703996288827 793746396638050055994433241)
        ·
          refine ⟨595309797478537541995824931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793746396638050055994433241 595309797478537541995824931)
          ·
            refine ⟨892964696217806312993737397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595309797478537541995824931 892964696217806312993737397)
            ·
              refine ⟨83715440270419341843162881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 892964696217806312993737397 83715440270419341843162881)
              ·
                refine ⟨62786580202814506382372161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83715440270419341843162881 62786580202814506382372161)
                ·
                  refine ⟨47089935152110879786779121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62786580202814506382372161 47089935152110879786779121)
                  ·
                    refine ⟨35317451364083159840084341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47089935152110879786779121 35317451364083159840084341)
                    ·
                      refine ⟨3311011065382796235007907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35317451364083159840084341 3311011065382796235007907)
                      ·
                        rfl

theorem cell23_6448171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 5].length) (baseStart_6448171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448171 prefixEnd_6448171 := by exact prefixLift 6448171
  have htrace : WordTrace (prefixWord ++ tailWord_6448171) baseStart_6448171 baseEnd_6448171 := by
    simpa [prefixWord, tailWord_6448171, baseEnd_6448171] using wordTrace_append hprefix tailTrace_6448171
  have hstable : (prefixWord ++ tailWord_6448171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448171).length < 2 ^ (prefixWord ++ tailWord_6448171).sum := by decide
  have hdescent : baseEnd_6448171 < baseStart_6448171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448191 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 1, 8]
def baseStart_6448191 : Nat := 118140960795 + 6448191 * 2 ^ 59
def prefixEnd_6448191 : Nat := 4983230072969 + 3 ^ 40 * 6448191 * 2
def baseEnd_6448191 : Nat := 1103673778331962052252605

theorem tailTrace_6448191 : CollatzResearch.WordTrace tailWord_6448191 prefixEnd_6448191 1103673778331962052252605 := by
  unfold tailWord_6448191
  simp only [CollatzResearch.WordTrace]
  refine ⟨235184846982312745191856427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156789897988208496794570951 235184846982312745191856427)
  ·
    refine ⟨352777270473469117787784641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235184846982312745191856427 352777270473469117787784641)
    ·
      refine ⟨264582952855101838340838481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352777270473469117787784641 264582952855101838340838481)
      ·
        refine ⟨198437214641326378755628861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264582952855101838340838481 198437214641326378755628861)
        ·
          refine ⟨74413955490497392033360823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198437214641326378755628861 74413955490497392033360823)
          ·
            refine ⟨111620933235746088050041235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74413955490497392033360823 111620933235746088050041235)
            ·
              refine ⟨167431399853619132075061853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111620933235746088050041235 167431399853619132075061853)
              ·
                refine ⟨62786774945107174528148195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167431399853619132075061853 62786774945107174528148195)
                ·
                  refine ⟨94180162417660761792222293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62786774945107174528148195 94180162417660761792222293)
                  ·
                    refine ⟨1103673778331962052252605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94180162417660761792222293 1103673778331962052252605)
                    ·
                      rfl

theorem cell23_6448191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_6448191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448191 prefixEnd_6448191 := by exact prefixLift 6448191
  have htrace : WordTrace (prefixWord ++ tailWord_6448191) baseStart_6448191 baseEnd_6448191 := by
    simpa [prefixWord, tailWord_6448191, baseEnd_6448191] using wordTrace_append hprefix tailTrace_6448191
  have hstable : (prefixWord ++ tailWord_6448191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448191).length < 2 ^ (prefixWord ++ tailWord_6448191).sum := by decide
  have hdescent : baseEnd_6448191 < baseStart_6448191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448202 : List Nat := [3, 1, 2, 1, 1, 2, 5, 2, 1, 3, 2]
def baseStart_6448202 : Nat := 118140960795 + 6448202 * 2 ^ 59
def prefixEnd_6448202 : Nat := 4983230072969 + 3 ^ 40 * 6448202 * 2
def baseEnd_6448202 : Nat := 3311026983283085613720265

theorem tailTrace_6448202 : CollatzResearch.WordTrace tailWord_6448202 prefixEnd_6448202 3311026983283085613720265 := by
  unfold tailWord_6448202
  simp only [CollatzResearch.WordTrace]
  refine ⟨58796312046318223517626715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156790165456848596047004573 58796312046318223517626715)
  ·
    refine ⟨88194468069477335276440073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58796312046318223517626715 88194468069477335276440073)
    ·
      refine ⟨66145851052108001457330055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88194468069477335276440073 66145851052108001457330055)
      ·
        refine ⟨99218776578162002185995083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66145851052108001457330055 99218776578162002185995083)
        ·
          refine ⟨148828164867243003278992625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99218776578162002185995083 148828164867243003278992625)
          ·
            refine ⟨111621123650432252459244469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148828164867243003278992625 111621123650432252459244469)
            ·
              refine ⟨10464480342228023668054169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111621123650432252459244469 10464480342228023668054169)
              ·
                refine ⟨7848360256671017751040627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10464480342228023668054169 7848360256671017751040627)
                ·
                  refine ⟨11772540385006526626560941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7848360256671017751040627 11772540385006526626560941)
                  ·
                    refine ⟨4414702644377447484960353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11772540385006526626560941 4414702644377447484960353)
                    ·
                      refine ⟨3311026983283085613720265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414702644377447484960353 3311026983283085613720265)
                      ·
                        rfl

theorem cell23_6448202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_6448202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448202 prefixEnd_6448202 := by exact prefixLift 6448202
  have htrace : WordTrace (prefixWord ++ tailWord_6448202) baseStart_6448202 baseEnd_6448202 := by
    simpa [prefixWord, tailWord_6448202, baseEnd_6448202] using wordTrace_append hprefix tailTrace_6448202
  have hstable : (prefixWord ++ tailWord_6448202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448202).length < 2 ^ (prefixWord ++ tailWord_6448202).sum := by decide
  have hdescent : baseEnd_6448202 < baseStart_6448202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448228 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_6448228 : Nat := 118140960795 + 6448228 * 2 ^ 59
def prefixEnd_6448228 : Nat := 4983230072969 + 3 ^ 40 * 6448228 * 2
def baseEnd_6448228 : Nat := 3311040333780102511995145

theorem tailTrace_6448228 : CollatzResearch.WordTrace tailWord_6448228 prefixEnd_6448228 3311040333780102511995145 := by
  unfold tailWord_6448228
  simp only [CollatzResearch.WordTrace]
  refine ⟨117593098241589350255476669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156790797655452467007302225 117593098241589350255476669)
  ·
    refine ⟨44097411840596006345803751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117593098241589350255476669 44097411840596006345803751)
    ·
      refine ⟨66146117760894009518705627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44097411840596006345803751 66146117760894009518705627)
      ·
        refine ⟨99219176641341014278058441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66146117760894009518705627 99219176641341014278058441)
        ·
          refine ⟨74414382481005760708543831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99219176641341014278058441 74414382481005760708543831)
          ·
            refine ⟨111621573721508641062815747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74414382481005760708543831 111621573721508641062815747)
            ·
              refine ⟨167432360582262961594223621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111621573721508641062815747 167432360582262961594223621)
              ·
                refine ⟨31393567609174305298916929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167432360582262961594223621 31393567609174305298916929)
                ·
                  refine ⟨23545175706880728974187697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31393567609174305298916929 23545175706880728974187697)
                  ·
                    refine ⟨17658881780160546730640773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23545175706880728974187697 17658881780160546730640773)
                    ·
                      refine ⟨3311040333780102511995145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17658881780160546730640773 3311040333780102511995145)
                      ·
                        rfl

theorem cell23_6448228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_6448228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448228 prefixEnd_6448228 := by exact prefixLift 6448228
  have htrace : WordTrace (prefixWord ++ tailWord_6448228) baseStart_6448228 baseEnd_6448228 := by
    simpa [prefixWord, tailWord_6448228, baseEnd_6448228] using wordTrace_append hprefix tailTrace_6448228
  have hstable : (prefixWord ++ tailWord_6448228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448228).length < 2 ^ (prefixWord ++ tailWord_6448228).sum := by decide
  have hdescent : baseEnd_6448228 < baseStart_6448228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448248 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 1, 5, 3]
def baseStart_6448248 : Nat := 118140960795 + 6448248 * 2 ^ 59
def prefixEnd_6448248 : Nat := 4983230072969 + 3 ^ 40 * 6448248 * 2
def baseEnd_6448248 : Nat := 3311050603393192433745053

theorem tailTrace_6448248 : CollatzResearch.WordTrace tailWord_6448248 prefixEnd_6448248 3311050603393192433745053 := by
  unfold tailWord_6448248
  simp only [CollatzResearch.WordTrace]
  refine ⟨117593462971553121963340699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156791283962070829284454265 117593462971553121963340699)
  ·
    refine ⟨176390194457329682945011049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117593462971553121963340699 176390194457329682945011049)
    ·
      refine ⟨132292645842997262208758287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176390194457329682945011049 132292645842997262208758287)
      ·
        refine ⟨198438968764495893313137431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132292645842997262208758287 198438968764495893313137431)
        ·
          refine ⟨297658453146743839969706147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198438968764495893313137431 297658453146743839969706147)
          ·
            refine ⟨446487679720115759954559221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297658453146743839969706147 446487679720115759954559221)
            ·
              refine ⟨41858219973760852495739927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 446487679720115759954559221 41858219973760852495739927)
              ·
                refine ⟨62787329960641278743609891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41858219973760852495739927 62787329960641278743609891)
                ·
                  refine ⟨94180994940961918115414837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62787329960641278743609891 94180994940961918115414837)
                  ·
                    refine ⟨8829468275715179823320141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94180994940961918115414837 8829468275715179823320141)
                    ·
                      refine ⟨3311050603393192433745053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8829468275715179823320141 3311050603393192433745053)
                      ·
                        rfl

theorem cell23_6448248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_6448248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448248 prefixEnd_6448248 := by exact prefixLift 6448248
  have htrace : WordTrace (prefixWord ++ tailWord_6448248) baseStart_6448248 baseEnd_6448248 := by
    simpa [prefixWord, tailWord_6448248, baseEnd_6448248] using wordTrace_append hprefix tailTrace_6448248
  have hstable : (prefixWord ++ tailWord_6448248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448248).length < 2 ^ (prefixWord ++ tailWord_6448248).sum := by decide
  have hdescent : baseEnd_6448248 < baseStart_6448248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448305 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 1, 3, 4]
def baseStart_6448305 : Nat := 118140960795 + 6448305 * 2 ^ 59
def prefixEnd_6448305 : Nat := 4983230072969 + 3 ^ 40 * 6448305 * 2
def baseEnd_6448305 : Nat := 3311079871790498710732291

theorem tailTrace_6448305 : CollatzResearch.WordTrace tailWord_6448305 prefixEnd_6448305 3311079871790498710732291 := by
  unfold tailWord_6448305
  simp only [CollatzResearch.WordTrace]
  refine ⟨235189004903899742661506369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156792669935933161774337579 235189004903899742661506369)
  ·
    refine ⟨176391753677924806996129777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235189004903899742661506369 176391753677924806996129777)
    ·
      refine ⟨132293815258443605247097333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176391753677924806996129777 132293815258443605247097333)
      ·
        refine ⟨12402545180479087991915375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132293815258443605247097333 12402545180479087991915375)
        ·
          refine ⟨18603817770718631987873063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12402545180479087991915375 18603817770718631987873063)
          ·
            refine ⟨27905726656077947981809595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18603817770718631987873063 27905726656077947981809595)
            ·
              refine ⟨41858589984116921972714393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27905726656077947981809595 41858589984116921972714393)
              ·
                refine ⟨31393942488087691479535795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41858589984116921972714393 31393942488087691479535795)
                ·
                  refine ⟨47090913732131537219303693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31393942488087691479535795 47090913732131537219303693)
                  ·
                    refine ⟨17659092649549326457238885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47090913732131537219303693 17659092649549326457238885)
                    ·
                      refine ⟨3311079871790498710732291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17659092649549326457238885 3311079871790498710732291)
                      ·
                        rfl

theorem cell23_6448305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_6448305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448305 prefixEnd_6448305 := by exact prefixLift 6448305
  have htrace : WordTrace (prefixWord ++ tailWord_6448305) baseStart_6448305 baseEnd_6448305 := by
    simpa [prefixWord, tailWord_6448305, baseEnd_6448305] using wordTrace_append hprefix tailTrace_6448305
  have hstable : (prefixWord ++ tailWord_6448305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448305).length < 2 ^ (prefixWord ++ tailWord_6448305).sum := by decide
  have hdescent : baseEnd_6448305 < baseStart_6448305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448325 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 2, 2, 3]
def baseStart_6448325 : Nat := 118140960795 + 6448325 * 2 ^ 59
def prefixEnd_6448325 : Nat := 4983230072969 + 3 ^ 40 * 6448325 * 2
def baseEnd_6448325 : Nat := 3311090141403588632482199

theorem tailTrace_6448325 : CollatzResearch.WordTrace tailWord_6448325 prefixEnd_6448325 3311090141403588632482199 := by
  unfold tailWord_6448325
  simp only [CollatzResearch.WordTrace]
  refine ⟨235189734363827286077234429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156793156242551524051489619 235189734363827286077234429)
  ·
    refine ⟨88196150386435232278962911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235189734363827286077234429 88196150386435232278962911)
    ·
      refine ⟨132294225579652848418444367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88196150386435232278962911 132294225579652848418444367)
      ·
        refine ⟨198441338369479272627666551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132294225579652848418444367 198441338369479272627666551)
        ·
          refine ⟨297662007554218908941499827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198441338369479272627666551 297662007554218908941499827)
          ·
            refine ⟨446493011331328363412249741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297662007554218908941499827 446493011331328363412249741)
            ·
              refine ⟨167434879249248136279593653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 446493011331328363412249741 167434879249248136279593653)
              ·
                refine ⟨15697019929617012776211905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167434879249248136279593653 15697019929617012776211905)
                ·
                  refine ⟨11772764947212759582158929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15697019929617012776211905 11772764947212759582158929)
                  ·
                    refine ⟨8829573710409569686619197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11772764947212759582158929 8829573710409569686619197)
                    ·
                      refine ⟨3311090141403588632482199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8829573710409569686619197 3311090141403588632482199)
                      ·
                        rfl

theorem cell23_6448325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_6448325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448325 prefixEnd_6448325 := by exact prefixLift 6448325
  have htrace : WordTrace (prefixWord ++ tailWord_6448325) baseStart_6448325 baseEnd_6448325 := by
    simpa [prefixWord, tailWord_6448325, baseEnd_6448325] using wordTrace_append hprefix tailTrace_6448325
  have hstable : (prefixWord ++ tailWord_6448325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448325).length < 2 ^ (prefixWord ++ tailWord_6448325).sum := by decide
  have hdescent : baseEnd_6448325 < baseStart_6448325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448328 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 8]
def baseStart_6448328 : Nat := 118140960795 + 6448328 * 2 ^ 59
def prefixEnd_6448328 : Nat := 4983230072969 + 3 ^ 40 * 6448328 * 2
def baseEnd_6448328 : Nat := 367899075760616902304965

theorem tailTrace_6448328 : CollatzResearch.WordTrace tailWord_6448328 prefixEnd_6448328 367899075760616902304965 := by
  unfold tailWord_6448328
  simp only [CollatzResearch.WordTrace]
  refine ⟨117594921891408208794796819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156793229188544278393062425 117594921891408208794796819)
  ·
    refine ⟨176392382837112313192195229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117594921891408208794796819 176392382837112313192195229)
    ·
      refine ⟨66147143563917117447073211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176392382837112313192195229 66147143563917117447073211)
      ·
        refine ⟨99220715345875676170609817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66147143563917117447073211 99220715345875676170609817)
        ·
          refine ⟨74415536509406757127957363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99220715345875676170609817 74415536509406757127957363)
          ·
            refine ⟨111623304764110135691936045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74415536509406757127957363 111623304764110135691936045)
            ·
              refine ⟨41858739286541300884476017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111623304764110135691936045 41858739286541300884476017)
              ·
                refine ⟨31394054464905975663357013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41858739286541300884476017 31394054464905975663357013)
                ·
                  refine ⟨367899075760616902304965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31394054464905975663357013 367899075760616902304965)
                  ·
                    rfl

theorem cell23_6448328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 8].length) (baseStart_6448328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448328 prefixEnd_6448328 := by exact prefixLift 6448328
  have htrace : WordTrace (prefixWord ++ tailWord_6448328) baseStart_6448328 baseEnd_6448328 := by
    simpa [prefixWord, tailWord_6448328, baseEnd_6448328] using wordTrace_append hprefix tailTrace_6448328
  have hstable : (prefixWord ++ tailWord_6448328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448328).length < 2 ^ (prefixWord ++ tailWord_6448328).sum := by decide
  have hdescent : baseEnd_6448328 < baseStart_6448328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448362 : List Nat := [3, 1, 3, 1, 1, 3, 4, 1, 6]
def baseStart_6448362 : Nat := 118140960795 + 6448362 * 2 ^ 59
def prefixEnd_6448362 : Nat := 4983230072969 + 3 ^ 40 * 6448362 * 2
def baseEnd_6448362 : Nat := 367901015576422776413281

theorem tailTrace_6448362 : CollatzResearch.WordTrace tailWord_6448362 prefixEnd_6448362 367901015576422776413281 := by
  unfold tailWord_6448362
  simp only [CollatzResearch.WordTrace]
  refine ⟨58797770966173310349082835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156794055909795494264220893 58797770966173310349082835)
  ·
    refine ⟨88196656449259965523624253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58797770966173310349082835 88196656449259965523624253)
    ·
      refine ⟨33073746168472487071359095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88196656449259965523624253 33073746168472487071359095)
      ·
        refine ⟨49610619252708730607038643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33073746168472487071359095 49610619252708730607038643)
        ·
          refine ⟨74415928879063095910557965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49610619252708730607038643 74415928879063095910557965)
          ·
            refine ⟨27905973329648660966459237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74415928879063095910557965 27905973329648660966459237)
            ·
              refine ⟨5232369999309123931211107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27905973329648660966459237 5232369999309123931211107)
              ·
                refine ⟨7848554998963685896816661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5232369999309123931211107 7848554998963685896816661)
                ·
                  refine ⟨367901015576422776413281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7848554998963685896816661 367901015576422776413281)
                  ·
                    rfl

theorem cell23_6448362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 6].length) (baseStart_6448362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448362 prefixEnd_6448362 := by exact prefixLift 6448362
  have htrace : WordTrace (prefixWord ++ tailWord_6448362) baseStart_6448362 baseEnd_6448362 := by
    simpa [prefixWord, tailWord_6448362, baseEnd_6448362] using wordTrace_append hprefix tailTrace_6448362
  have hstable : (prefixWord ++ tailWord_6448362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448362).length < 2 ^ (prefixWord ++ tailWord_6448362).sum := by decide
  have hdescent : baseEnd_6448362 < baseStart_6448362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448389 : List Nat := [1, 3, 1, 1, 2, 1, 4, 5, 1, 1, 3]
def baseStart_6448389 : Nat := 118140960795 + 6448389 * 2 ^ 59
def prefixEnd_6448389 : Nat := 4983230072969 + 3 ^ 40 * 6448389 * 2
def baseEnd_6448389 : Nat := 3311123004165476382081905

theorem tailTrace_6448389 : CollatzResearch.WordTrace tailWord_6448389 prefixEnd_6448389 3311123004165476382081905 := by
  unfold tailWord_6448389
  simp only [CollatzResearch.WordTrace]
  refine ⟨235192068635595425007564221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156794712423730283338376147 235192068635595425007564221)
  ·
    refine ⟨88197025738348284377836583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235192068635595425007564221 88197025738348284377836583)
    ·
      refine ⟨132295538607522426566754875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88197025738348284377836583 132295538607522426566754875)
      ·
        refine ⟨198443307911283639850132313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132295538607522426566754875 198443307911283639850132313)
        ·
          refine ⟨148832480933462729887599235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198443307911283639850132313 148832480933462729887599235)
          ·
            refine ⟨223248721400194094831398853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148832480933462729887599235 223248721400194094831398853)
            ·
              refine ⟨41859135262536392780887285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223248721400194094831398853 41859135262536392780887285)
              ·
                refine ⟨3924293930862786823208183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41859135262536392780887285 3924293930862786823208183)
                ·
                  refine ⟨5886440896294180234812275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924293930862786823208183 5886440896294180234812275)
                  ·
                    refine ⟨8829661344441270352218413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5886440896294180234812275 8829661344441270352218413)
                    ·
                      refine ⟨3311123004165476382081905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8829661344441270352218413 3311123004165476382081905)
                      ·
                        rfl

theorem cell23_6448389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 1, 1, 3].length) (baseStart_6448389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448389 prefixEnd_6448389 := by exact prefixLift 6448389
  have htrace : WordTrace (prefixWord ++ tailWord_6448389) baseStart_6448389 baseEnd_6448389 := by
    simpa [prefixWord, tailWord_6448389, baseEnd_6448389] using wordTrace_append hprefix tailTrace_6448389
  have hstable : (prefixWord ++ tailWord_6448389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448389).length < 2 ^ (prefixWord ++ tailWord_6448389).sum := by decide
  have hdescent : baseEnd_6448389 < baseStart_6448389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448429 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_6448429 : Nat := 118140960795 + 6448429 * 2 ^ 59
def prefixEnd_6448429 : Nat := 4983230072969 + 3 ^ 40 * 6448429 * 2
def baseEnd_6448429 : Nat := 3311143543391656225581721

theorem tailTrace_6448429 : CollatzResearch.WordTrace tailWord_6448429 prefixEnd_6448429 3311143543391656225581721 := by
  unfold tailWord_6448429
  simp only [CollatzResearch.WordTrace]
  refine ⟨235193527555450511839020341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156795685036967007892680227 235193527555450511839020341)
  ·
    refine ⟨22049393208323485484908157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235193527555450511839020341 22049393208323485484908157)
    ·
      refine ⟨8268522453121307056840559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22049393208323485484908157 8268522453121307056840559)
      ·
        refine ⟨12402783679681960585260839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8268522453121307056840559 12402783679681960585260839)
        ·
          refine ⟨18604175519522940877891259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12402783679681960585260839 18604175519522940877891259)
          ·
            refine ⟨27906263279284411316836889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18604175519522940877891259 27906263279284411316836889)
            ·
              refine ⟨20929697459463308487627667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27906263279284411316836889 20929697459463308487627667)
              ·
                refine ⟨31394546189194962731441501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20929697459463308487627667 31394546189194962731441501)
                ·
                  refine ⟨11772954820948111024290563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31394546189194962731441501 11772954820948111024290563)
                  ·
                    refine ⟨17659432231422166536435845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11772954820948111024290563 17659432231422166536435845)
                    ·
                      refine ⟨3311143543391656225581721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17659432231422166536435845 3311143543391656225581721)
                      ·
                        rfl

theorem cell23_6448429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_6448429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448429 prefixEnd_6448429 := by exact prefixLift 6448429
  have htrace : WordTrace (prefixWord ++ tailWord_6448429) baseStart_6448429 baseEnd_6448429 := by
    simpa [prefixWord, tailWord_6448429, baseEnd_6448429] using wordTrace_append hprefix tailTrace_6448429
  have hstable : (prefixWord ++ tailWord_6448429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448429).length < 2 ^ (prefixWord ++ tailWord_6448429).sum := by decide
  have hdescent : baseEnd_6448429 < baseStart_6448429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448432 : List Nat := [2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 3]
def baseStart_6448432 : Nat := 118140960795 + 6448432 * 2 ^ 59
def prefixEnd_6448432 : Nat := 4983230072969 + 3 ^ 40 * 6448432 * 2
def baseEnd_6448432 : Nat := 3311145083833619713844207

theorem tailTrace_6448432 : CollatzResearch.WordTrace tailWord_6448432 prefixEnd_6448432 3311145083833619713844207 := by
  unfold tailWord_6448432
  simp only [CollatzResearch.WordTrace]
  refine ⟨117596818487219821675689775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156795757982959762234253033 117596818487219821675689775)
  ·
    refine ⟨176395227730829732513534663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117596818487219821675689775 176395227730829732513534663)
    ·
      refine ⟨264592841596244598770301995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176395227730829732513534663 264592841596244598770301995)
      ·
        refine ⟨396889262394366898155452993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264592841596244598770301995 396889262394366898155452993)
        ·
          refine ⟨297666946795775173616589745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396889262394366898155452993 297666946795775173616589745)
          ·
            refine ⟨223250210096831380212442309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297666946795775173616589745 223250210096831380212442309)
            ·
              refine ⟨41859414393155883789832933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223250210096831380212442309 41859414393155883789832933)
              ·
                refine ⟨7848640198716728210593675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41859414393155883789832933 7848640198716728210593675)
                ·
                  refine ⟨11772960298075092315890513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7848640198716728210593675 11772960298075092315890513)
                  ·
                    refine ⟨8829720223556319236917885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11772960298075092315890513 8829720223556319236917885)
                    ·
                      refine ⟨3311145083833619713844207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8829720223556319236917885 3311145083833619713844207)
                      ·
                        rfl

theorem cell23_6448432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 3].length) (baseStart_6448432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448432 prefixEnd_6448432 := by exact prefixLift 6448432
  have htrace : WordTrace (prefixWord ++ tailWord_6448432) baseStart_6448432 baseEnd_6448432 := by
    simpa [prefixWord, tailWord_6448432, baseEnd_6448432] using wordTrace_append hprefix tailTrace_6448432
  have hstable : (prefixWord ++ tailWord_6448432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448432).length < 2 ^ (prefixWord ++ tailWord_6448432).sum := by decide
  have hdescent : baseEnd_6448432 < baseStart_6448432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448452 : List Nat := [2, 3, 4, 1, 1, 2, 10]
def baseStart_6448452 : Nat := 118140960795 + 6448452 * 2 ^ 59
def prefixEnd_6448452 : Nat := 4983230072969 + 3 ^ 40 * 6448452 * 2
def baseEnd_6448452 : Nat := 40878461153663081920915

theorem tailTrace_6448452 : CollatzResearch.WordTrace tailWord_6448452 prefixEnd_6448452 40878461153663081920915 := by
  unfold tailWord_6448452
  simp only [CollatzResearch.WordTrace]
  refine ⟨117597183217183593383553805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156796244289578124511405073 117597183217183593383553805)
  ·
    refine ⟨44098943706443847518832677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117597183217183593383553805 44098943706443847518832677)
    ·
      refine ⟨8268551944958221409781127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44098943706443847518832677 8268551944958221409781127)
      ·
        refine ⟨12402827917437332114671691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8268551944958221409781127 12402827917437332114671691)
        ·
          refine ⟨18604241876155998172007537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12402827917437332114671691 18604241876155998172007537)
          ·
            refine ⟨13953181407116998629005653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18604241876155998172007537 13953181407116998629005653)
            ·
              refine ⟨40878461153663081920915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13953181407116998629005653 40878461153663081920915)
              ·
                rfl

theorem cell23_6448452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 10].length) (baseStart_6448452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448452 prefixEnd_6448452 := by exact prefixLift 6448452
  have htrace : WordTrace (prefixWord ++ tailWord_6448452) baseStart_6448452 baseEnd_6448452 := by
    simpa [prefixWord, tailWord_6448452, baseEnd_6448452] using wordTrace_append hprefix tailTrace_6448452
  have hstable : (prefixWord ++ tailWord_6448452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448452).length < 2 ^ (prefixWord ++ tailWord_6448452).sum := by decide
  have hdescent : baseEnd_6448452 < baseStart_6448452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448505 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 1, 3, 5]
def baseStart_6448505 : Nat := 118140960795 + 6448505 * 2 ^ 59
def prefixEnd_6448505 : Nat := 4983230072969 + 3 ^ 40 * 6448505 * 2
def baseEnd_6448505 : Nat := 3311182567921397928231371

theorem tailTrace_6448505 : CollatzResearch.WordTrace tailWord_6448505 prefixEnd_6448505 3311182567921397928231371 := by
  unfold tailWord_6448505
  simp only [CollatzResearch.WordTrace]
  refine ⟨235196299503175176818786969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156797533002116784545857979 235196299503175176818786969)
  ·
    refine ⟨176397224627381382614090227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235196299503175176818786969 176397224627381382614090227)
    ·
      refine ⟨264595836941072073921135341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176397224627381382614090227 264595836941072073921135341)
      ·
        refine ⟨99223438852902027720425753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264595836941072073921135341 99223438852902027720425753)
        ·
          refine ⟨74417579139676520790319315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99223438852902027720425753 74417579139676520790319315)
          ·
            refine ⟨111626368709514781185478973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74417579139676520790319315 111626368709514781185478973)
            ·
              refine ⟨41859888266068042944554615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111626368709514781185478973 41859888266068042944554615)
              ·
                refine ⟨62789832399102064416831923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41859888266068042944554615 62789832399102064416831923)
                ·
                  refine ⟨94184748598653096625247885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62789832399102064416831923 94184748598653096625247885)
                  ·
                    refine ⟨35319280724494911234467957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94184748598653096625247885 35319280724494911234467957)
                    ·
                      refine ⟨3311182567921397928231371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35319280724494911234467957 3311182567921397928231371)
                      ·
                        rfl

theorem cell23_6448505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_6448505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448505 prefixEnd_6448505 := by exact prefixLift 6448505
  have htrace : WordTrace (prefixWord ++ tailWord_6448505) baseStart_6448505 baseEnd_6448505 := by
    simpa [prefixWord, tailWord_6448505, baseEnd_6448505] using wordTrace_append hprefix tailTrace_6448505
  have hstable : (prefixWord ++ tailWord_6448505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448505).length < 2 ^ (prefixWord ++ tailWord_6448505).sum := by decide
  have hdescent : baseEnd_6448505 < baseStart_6448505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448540 : List Nat := [2, 2, 3, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6448540 : Nat := 118140960795 + 6448540 * 2 ^ 59
def prefixEnd_6448540 : Nat := 4983230072969 + 3 ^ 40 * 6448540 * 2
def baseEnd_6448540 : Nat := 3311200539744305291293711

theorem tailTrace_6448540 : CollatzResearch.WordTrace tailWord_6448540 prefixEnd_6448540 3311200539744305291293711 := by
  unfold tailWord_6448540
  simp only [CollatzResearch.WordTrace]
  refine ⟨117598788029024188898155537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156798384038698918530874049 117598788029024188898155537)
  ·
    refine ⟨88199091021768141673616653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117598788029024188898155537 88199091021768141673616653)
    ·
      refine ⟨33074659133163053127606245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88199091021768141673616653 33074659133163053127606245)
      ·
        refine ⟨6201498587468072461426171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33074659133163053127606245 6201498587468072461426171)
        ·
          refine ⟨9302247881202108692139257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6201498587468072461426171 9302247881202108692139257)
          ·
            refine ⟨6976685910901581519104443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9302247881202108692139257 6976685910901581519104443)
            ·
              refine ⟨10465028866352372278656665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6976685910901581519104443 10465028866352372278656665)
              ·
                refine ⟨7848771649764279208992499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10465028866352372278656665 7848771649764279208992499)
                ·
                  refine ⟨11773157474646418813488749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7848771649764279208992499 11773157474646418813488749)
                  ·
                    refine ⟨4414934052992407055058281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11773157474646418813488749 4414934052992407055058281)
                    ·
                      refine ⟨3311200539744305291293711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414934052992407055058281 3311200539744305291293711)
                      ·
                        rfl

theorem cell23_6448540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6448540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448540 prefixEnd_6448540 := by exact prefixLift 6448540
  have htrace : WordTrace (prefixWord ++ tailWord_6448540) baseStart_6448540 baseEnd_6448540 := by
    simpa [prefixWord, tailWord_6448540, baseEnd_6448540] using wordTrace_append hprefix tailTrace_6448540
  have hstable : (prefixWord ++ tailWord_6448540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448540).length < 2 ^ (prefixWord ++ tailWord_6448540).sum := by decide
  have hdescent : baseEnd_6448540 < baseStart_6448540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448585 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 2, 8]
def baseStart_6448585 : Nat := 118140960795 + 6448585 * 2 ^ 59
def prefixEnd_6448585 : Nat := 4983230072969 + 3 ^ 40 * 6448585 * 2
def baseEnd_6448585 : Nat := 1103741215457919205077001

theorem tailTrace_6448585 : CollatzResearch.WordTrace tailWord_6448585 prefixEnd_6448585 1103741215457919205077001 := by
  unfold tailWord_6448585
  simp only [CollatzResearch.WordTrace]
  refine ⟨235199217342885350481699209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156799478228590233654466139 235199217342885350481699209)
  ·
    refine ⟨176399413007164012861274407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235199217342885350481699209 176399413007164012861274407)
    ·
      refine ⟨264599119510746019291911611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176399413007164012861274407 264599119510746019291911611)
      ·
        refine ⟨396898679266119028937867417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264599119510746019291911611 396898679266119028937867417)
        ·
          refine ⟨297674009449589271703400563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396898679266119028937867417 297674009449589271703400563)
          ·
            refine ⟨446511014174383907555100845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297674009449589271703400563 446511014174383907555100845)
            ·
              refine ⟨167441630315393965333162817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 446511014174383907555100845 167441630315393965333162817)
              ·
                refine ⟨125581222736545473999872113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167441630315393965333162817 125581222736545473999872113)
                ·
                  refine ⟨94185917052409105499904085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125581222736545473999872113 94185917052409105499904085)
                  ·
                    refine ⟨1103741215457919205077001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94185917052409105499904085 1103741215457919205077001)
                    ·
                      rfl

theorem cell23_6448585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_6448585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448585 prefixEnd_6448585 := by exact prefixLift 6448585
  have htrace : WordTrace (prefixWord ++ tailWord_6448585) baseStart_6448585 baseEnd_6448585 := by
    simpa [prefixWord, tailWord_6448585, baseEnd_6448585] using wordTrace_append hprefix tailTrace_6448585
  have hstable : (prefixWord ++ tailWord_6448585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448585).length < 2 ^ (prefixWord ++ tailWord_6448585).sum := by decide
  have hdescent : baseEnd_6448585 < baseStart_6448585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448609 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_6448609 : Nat := 118140960795 + 6448609 * 2 ^ 59
def prefixEnd_6448609 : Nat := 4983230072969 + 3 ^ 40 * 6448609 * 2
def baseEnd_6448609 : Nat := 3311235969909465521330893

theorem tailTrace_6448609 : CollatzResearch.WordTrace tailWord_6448609 prefixEnd_6448609 3311235969909465521330893 := by
  unfold tailWord_6448609
  simp only [CollatzResearch.WordTrace]
  refine ⟨235200092694798402580572881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156800061796532268387048587 235200092694798402580572881)
  ·
    refine ⟨176400069521098801935429661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235200092694798402580572881 176400069521098801935429661)
    ·
      refine ⟨66150026070412050725786123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176400069521098801935429661 66150026070412050725786123)
      ·
        refine ⟨99225039105618076088679185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66150026070412050725786123 99225039105618076088679185)
        ·
          refine ⟨74418779329213557066509389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99225039105618076088679185 74418779329213557066509389)
          ·
            refine ⟨27907042248455083899941021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74418779329213557066509389 27907042248455083899941021)
            ·
              refine ⟨10465140843170656462477883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27907042248455083899941021 10465140843170656462477883)
              ·
                refine ⟨15697711264755984693716825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10465140843170656462477883 15697711264755984693716825)
                ·
                  refine ⟨11773283448566988520287619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15697711264755984693716825 11773283448566988520287619)
                  ·
                    refine ⟨17659925172850482780431429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11773283448566988520287619 17659925172850482780431429)
                    ·
                      refine ⟨3311235969909465521330893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17659925172850482780431429 3311235969909465521330893)
                      ·
                        rfl

theorem cell23_6448609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_6448609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448609 prefixEnd_6448609 := by exact prefixLift 6448609
  have htrace : WordTrace (prefixWord ++ tailWord_6448609) baseStart_6448609 baseEnd_6448609 := by
    simpa [prefixWord, tailWord_6448609, baseEnd_6448609] using wordTrace_append hprefix tailTrace_6448609
  have hstable : (prefixWord ++ tailWord_6448609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448609).length < 2 ^ (prefixWord ++ tailWord_6448609).sum := by decide
  have hdescent : baseEnd_6448609 < baseStart_6448609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448622 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_6448622 : Nat := 118140960795 + 6448622 * 2 ^ 59
def prefixEnd_6448622 : Nat := 4983230072969 + 3 ^ 40 * 6448622 * 2
def baseEnd_6448622 : Nat := 3311242645157973970468333

theorem tailTrace_6448622 : CollatzResearch.WordTrace tailWord_6448622 prefixEnd_6448622 3311242645157973970468333 := by
  unfold tailWord_6448622
  simp only [CollatzResearch.WordTrace]
  refine ⟨29400070855468913225099515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156800377895834203867197413 29400070855468913225099515)
  ·
    refine ⟨44100106283203369837649273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29400070855468913225099515 44100106283203369837649273)
    ·
      refine ⟨33075079712402527378236955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44100106283203369837649273 33075079712402527378236955)
      ·
        refine ⟨49612619568603791067355433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33075079712402527378236955 49612619568603791067355433)
        ·
          refine ⟨37209464676452843300516575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49612619568603791067355433 37209464676452843300516575)
          ·
            refine ⟨55814197014679264950774863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37209464676452843300516575 55814197014679264950774863)
            ·
              refine ⟨83721295522018897426162295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55814197014679264950774863 83721295522018897426162295)
              ·
                refine ⟨125581943283028346139243443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83721295522018897426162295 125581943283028346139243443)
                ·
                  refine ⟨188372914924542519208865165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125581943283028346139243443 188372914924542519208865165)
                  ·
                    refine ⟨70639843096703444703324437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188372914924542519208865165 70639843096703444703324437)
                    ·
                      refine ⟨3311242645157973970468333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70639843096703444703324437 3311242645157973970468333)
                      ·
                        rfl

theorem cell23_6448622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_6448622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448622 prefixEnd_6448622 := by exact prefixLift 6448622
  have htrace : WordTrace (prefixWord ++ tailWord_6448622) baseStart_6448622 baseEnd_6448622 := by
    simpa [prefixWord, tailWord_6448622, baseEnd_6448622] using wordTrace_append hprefix tailTrace_6448622
  have hstable : (prefixWord ++ tailWord_6448622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448622).length < 2 ^ (prefixWord ++ tailWord_6448622).sum := by decide
  have hdescent : baseEnd_6448622 < baseStart_6448622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448626 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 2, 4, 2]
def baseStart_6448626 : Nat := 118140960795 + 6448626 * 2 ^ 59
def prefixEnd_6448626 : Nat := 4983230072969 + 3 ^ 40 * 6448626 * 2
def baseEnd_6448626 : Nat := 3311244699080591954818315

theorem tailTrace_6448626 : CollatzResearch.WordTrace tailWord_6448626 prefixEnd_6448626 3311244699080591954818315 := by
  unfold tailWord_6448626
  simp only [CollatzResearch.WordTrace]
  refine ⟨58800178183934203620985433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156800475157157876322627821 58800178183934203620985433)
  ·
    refine ⟨44100133637950652715739075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58800178183934203620985433 44100133637950652715739075)
    ·
      refine ⟨66150200456925979073608613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44100133637950652715739075 66150200456925979073608613)
      ·
        refine ⟨12403162585673621076301615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66150200456925979073608613 12403162585673621076301615)
        ·
          refine ⟨18604743878510431614452423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12403162585673621076301615 18604743878510431614452423)
          ·
            refine ⟨27907115817765647421678635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18604743878510431614452423 27907115817765647421678635)
            ·
              refine ⟨41860673726648471132517953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27907115817765647421678635 41860673726648471132517953)
              ·
                refine ⟨31395505294986353349388465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41860673726648471132517953 31395505294986353349388465)
                ·
                  refine ⟨23546628971239765012041349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31395505294986353349388465 23546628971239765012041349)
                  ·
                    refine ⟨4414992932107455939757753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23546628971239765012041349 4414992932107455939757753)
                    ·
                      refine ⟨3311244699080591954818315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414992932107455939757753 3311244699080591954818315)
                      ·
                        rfl

theorem cell23_6448626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_6448626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448626 prefixEnd_6448626 := by exact prefixLift 6448626
  have htrace : WordTrace (prefixWord ++ tailWord_6448626) baseStart_6448626 baseEnd_6448626 := by
    simpa [prefixWord, tailWord_6448626, baseEnd_6448626] using wordTrace_append hprefix tailTrace_6448626
  have hstable : (prefixWord ++ tailWord_6448626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448626).length < 2 ^ (prefixWord ++ tailWord_6448626).sum := by decide
  have hdescent : baseEnd_6448626 < baseStart_6448626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448632 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 8]
def baseStart_6448632 : Nat := 118140960795 + 6448632 * 2 ^ 59
def prefixEnd_6448632 : Nat := 4983230072969 + 3 ^ 40 * 6448632 * 2
def baseEnd_6448632 : Nat := 367916419996057659038143

theorem tailTrace_6448632 : CollatzResearch.WordTrace tailWord_6448632 prefixEnd_6448632 367916419996057659038143 := by
  unfold tailWord_6448632
  simp only [CollatzResearch.WordTrace]
  refine ⟨117600465786857538754330075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156800621049143385005773433 117600465786857538754330075)
  ·
    refine ⟨176400698680286308131495113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117600465786857538754330075 176400698680286308131495113)
    ·
      refine ⟨132300524010214731098621335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176400698680286308131495113 132300524010214731098621335)
      ·
        refine ⟨198450786015322096647932003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132300524010214731098621335 198450786015322096647932003)
        ·
          refine ⟨297676179022983144971898005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198450786015322096647932003 297676179022983144971898005)
          ·
            refine ⟨13953570891702334920557719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 297676179022983144971898005 13953570891702334920557719)
            ·
              refine ⟨20930356337553502380836579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13953570891702334920557719 20930356337553502380836579)
              ·
                refine ⟨31395534506330253571254869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20930356337553502380836579 31395534506330253571254869)
                ·
                  refine ⟨367916419996057659038143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31395534506330253571254869 367916419996057659038143)
                  ·
                    rfl

theorem cell23_6448632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 8].length) (baseStart_6448632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448632 prefixEnd_6448632 := by exact prefixLift 6448632
  have htrace : WordTrace (prefixWord ++ tailWord_6448632) baseStart_6448632 baseEnd_6448632 := by
    simpa [prefixWord, tailWord_6448632, baseEnd_6448632] using wordTrace_append hprefix tailTrace_6448632
  have hstable : (prefixWord ++ tailWord_6448632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448632).length < 2 ^ (prefixWord ++ tailWord_6448632).sum := by decide
  have hdescent : baseEnd_6448632 < baseStart_6448632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448636 : List Nat := [2, 2, 2, 1, 2, 1, 4, 4, 1, 4]
def baseStart_6448636 : Nat := 118140960795 + 6448636 * 2 ^ 59
def prefixEnd_6448636 : Nat := 4983230072969 + 3 ^ 40 * 6448636 * 2
def baseEnd_6448636 : Nat := 1103749944629045638564423

theorem tailTrace_6448636 : CollatzResearch.WordTrace tailWord_6448636 prefixEnd_6448636 1103749944629045638564423 := by
  unfold tailWord_6448636
  simp only [CollatzResearch.WordTrace]
  refine ⟨117600538732850293095902881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156800718310467057461203841 117600538732850293095902881)
  ·
    refine ⟨88200404049637719821927161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117600538732850293095902881 88200404049637719821927161)
    ·
      refine ⟨66150303037228289866445371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88200404049637719821927161 66150303037228289866445371)
      ·
        refine ⟨99225454555842434799668057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66150303037228289866445371 99225454555842434799668057)
        ·
          refine ⟨74419090916881826099751043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99225454555842434799668057 74419090916881826099751043)
          ·
            refine ⟨111628636375322739149626565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74419090916881826099751043 111628636375322739149626565)
            ·
              refine ⟨20930369320373013590554981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111628636375322739149626565 20930369320373013590554981)
              ·
                refine ⟨3924444247569940048229059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20930369320373013590554981 3924444247569940048229059)
                ·
                  refine ⟨5886666371354910072343589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924444247569940048229059 5886666371354910072343589)
                  ·
                    refine ⟨1103749944629045638564423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5886666371354910072343589 1103749944629045638564423)
                    ·
                      rfl

theorem cell23_6448636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_6448636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448636 prefixEnd_6448636 := by exact prefixLift 6448636
  have htrace : WordTrace (prefixWord ++ tailWord_6448636) baseStart_6448636 baseEnd_6448636 := by
    simpa [prefixWord, tailWord_6448636, baseEnd_6448636] using wordTrace_append hprefix tailTrace_6448636
  have hstable : (prefixWord ++ tailWord_6448636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448636).length < 2 ^ (prefixWord ++ tailWord_6448636).sum := by decide
  have hdescent : baseEnd_6448636 < baseStart_6448636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448649 : List Nat := [1, 2, 1, 1, 3, 1, 7, 1, 6]
def baseStart_6448649 : Nat := 118140960795 + 6448649 * 2 ^ 59
def prefixEnd_6448649 : Nat := 4983230072969 + 3 ^ 40 * 6448649 * 2
def baseEnd_6448649 : Nat := 367917389903960596092301

theorem tailTrace_6448649 : CollatzResearch.WordTrace tailWord_6448649 prefixEnd_6448649 367917389903960596092301 := by
  unfold tailWord_6448649
  simp only [CollatzResearch.WordTrace]
  refine ⟨235201551614653489412029001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156801034409768992941352667 235201551614653489412029001)
  ·
    refine ⟨176401163710990117059021751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235201551614653489412029001 176401163710990117059021751)
    ·
      refine ⟨264601745566485175588532627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176401163710990117059021751 264601745566485175588532627)
      ·
        refine ⟨396902618349727763382798941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264601745566485175588532627 396902618349727763382798941)
        ·
          refine ⟨148838481881147911268549603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396902618349727763382798941 148838481881147911268549603)
          ·
            refine ⟨223257722821721866902824405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148838481881147911268549603 223257722821721866902824405)
            ·
              refine ⟨5232602878634106255534947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 223257722821721866902824405 5232602878634106255534947)
              ·
                refine ⟨7848904317951159383302421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5232602878634106255534947 7848904317951159383302421)
                ·
                  refine ⟨367917389903960596092301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7848904317951159383302421 367917389903960596092301)
                  ·
                    rfl

theorem cell23_6448649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 6].length) (baseStart_6448649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448649 prefixEnd_6448649 := by exact prefixLift 6448649
  have htrace : WordTrace (prefixWord ++ tailWord_6448649) baseStart_6448649 baseEnd_6448649 := by
    simpa [prefixWord, tailWord_6448649, baseEnd_6448649] using wordTrace_append hprefix tailTrace_6448649
  have hstable : (prefixWord ++ tailWord_6448649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448649).length < 2 ^ (prefixWord ++ tailWord_6448649).sum := by decide
  have hdescent : baseEnd_6448649 < baseStart_6448649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448693 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_6448693 : Nat := 118140960795 + 6448693 * 2 ^ 59
def prefixEnd_6448693 : Nat := 4983230072969 + 3 ^ 40 * 6448693 * 2
def baseEnd_6448693 : Nat := 3311279102284443192680507

theorem tailTrace_6448693 : CollatzResearch.WordTrace tailWord_6448693 prefixEnd_6448693 3311279102284443192680507 := by
  unfold tailWord_6448693
  simp only [CollatzResearch.WordTrace]
  refine ⟨235203156426494084926630733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156802104284329389951087155 235203156426494084926630733)
  ·
    refine ⟨88201183659935281847486525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235203156426494084926630733 88201183659935281847486525)
    ·
      refine ⟨33075443872475730692807447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88201183659935281847486525 33075443872475730692807447)
      ·
        refine ⟨49613165808713596039211171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33075443872475730692807447 49613165808713596039211171)
        ·
          refine ⟨74419748713070394058816757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49613165808713596039211171 74419748713070394058816757)
          ·
            refine ⟨6976851441850349443014071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74419748713070394058816757 6976851441850349443014071)
            ·
              refine ⟨10465277162775524164521107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6976851441850349443014071 10465277162775524164521107)
              ·
                refine ⟨15697915744163286246781661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10465277162775524164521107 15697915744163286246781661)
                ·
                  refine ⟨5886718404061232342543123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15697915744163286246781661 5886718404061232342543123)
                  ·
                    refine ⟨8830077606091848513814685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5886718404061232342543123 8830077606091848513814685)
                    ·
                      refine ⟨3311279102284443192680507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8830077606091848513814685 3311279102284443192680507)
                      ·
                        rfl

theorem cell23_6448693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_6448693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448693 prefixEnd_6448693 := by exact prefixLift 6448693
  have htrace : WordTrace (prefixWord ++ tailWord_6448693) baseStart_6448693 baseEnd_6448693 := by
    simpa [prefixWord, tailWord_6448693, baseEnd_6448693] using wordTrace_append hprefix tailTrace_6448693
  have hstable : (prefixWord ++ tailWord_6448693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448693).length < 2 ^ (prefixWord ++ tailWord_6448693).sum := by decide
  have hdescent : baseEnd_6448693 < baseStart_6448693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448716 : List Nat := [2, 2, 1, 3, 1, 3, 3, 2, 1, 1, 4]
def baseStart_6448716 : Nat := 118140960795 + 6448716 * 2 ^ 59
def prefixEnd_6448716 : Nat := 4983230072969 + 3 ^ 40 * 6448716 * 2
def baseEnd_6448716 : Nat := 3311290912339496602692901

theorem tailTrace_6448716 : CollatzResearch.WordTrace tailWord_6448716 prefixEnd_6448716 3311290912339496602692901 := by
  unfold tailWord_6448716
  simp only [CollatzResearch.WordTrace]
  refine ⟨117601997652705379927359001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156802663536940506569812001 117601997652705379927359001)
  ·
    refine ⟨88201498239529034945519251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117601997652705379927359001 88201498239529034945519251)
    ·
      refine ⟨132302247359293552418278877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88201498239529034945519251 132302247359293552418278877)
      ·
        refine ⟨49613342759735082156854579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132302247359293552418278877 49613342759735082156854579)
        ·
          refine ⟨74420014139602623235281869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49613342759735082156854579 74420014139602623235281869)
          ·
            refine ⟨27907505302350983713230701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74420014139602623235281869 27907505302350983713230701)
            ·
              refine ⟨10465314488381618892461513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27907505302350983713230701 10465314488381618892461513)
              ·
                refine ⟨7848985866286214169346135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10465314488381618892461513 7848985866286214169346135)
                ·
                  refine ⟨11773478799429321254019203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7848985866286214169346135 11773478799429321254019203)
                  ·
                    refine ⟨17660218199143981881028805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11773478799429321254019203 17660218199143981881028805)
                    ·
                      refine ⟨3311290912339496602692901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17660218199143981881028805 3311290912339496602692901)
                      ·
                        rfl

theorem cell23_6448716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_6448716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448716 prefixEnd_6448716 := by exact prefixLift 6448716
  have htrace : WordTrace (prefixWord ++ tailWord_6448716) baseStart_6448716 baseEnd_6448716 := by
    simpa [prefixWord, tailWord_6448716, baseEnd_6448716] using wordTrace_append hprefix tailTrace_6448716
  have hstable : (prefixWord ++ tailWord_6448716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448716).length < 2 ^ (prefixWord ++ tailWord_6448716).sum := by decide
  have hdescent : baseEnd_6448716 < baseStart_6448716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448800 : List Nat := [2, 1, 1, 4, 3, 3, 1, 2, 2, 1, 3]
def baseStart_6448800 : Nat := 118140960795 + 6448800 * 2 ^ 59
def prefixEnd_6448800 : Nat := 4983230072969 + 3 ^ 40 * 6448800 * 2
def baseEnd_6448800 : Nat := 3311334044714474274042515

theorem tailTrace_6448800 : CollatzResearch.WordTrace tailWord_6448800 prefixEnd_6448800 3311334044714474274042515 := by
  unfold tailWord_6448800
  simp only [CollatzResearch.WordTrace]
  refine ⟨117603529518553221100387927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156804706024737628133850569 117603529518553221100387927)
  ·
    refine ⟨176405294277829831650581891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117603529518553221100387927 176405294277829831650581891)
    ·
      refine ⟨264607941416744747475872837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176405294277829831650581891 264607941416744747475872837)
      ·
        refine ⟨49613989015639640151726157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264607941416744747475872837 49613989015639640151726157)
        ·
          refine ⟨18605245880864865056897309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49613989015639640151726157 18605245880864865056897309)
          ·
            refine ⟨6976967205324324396336491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18605245880864865056897309 6976967205324324396336491)
            ·
              refine ⟨10465450807986486594504737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6976967205324324396336491 10465450807986486594504737)
              ·
                refine ⟨7849088105989864945878553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10465450807986486594504737 7849088105989864945878553)
                ·
                  refine ⟨5886816079492398709408915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7849088105989864945878553 5886816079492398709408915)
                  ·
                    refine ⟨8830224119238598064113373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5886816079492398709408915 8830224119238598064113373)
                    ·
                      refine ⟨3311334044714474274042515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8830224119238598064113373 3311334044714474274042515)
                      ·
                        rfl

theorem cell23_6448800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_6448800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448800 prefixEnd_6448800 := by exact prefixLift 6448800
  have htrace : WordTrace (prefixWord ++ tailWord_6448800) baseStart_6448800 baseEnd_6448800 := by
    simpa [prefixWord, tailWord_6448800, baseEnd_6448800] using wordTrace_append hprefix tailTrace_6448800
  have hstable : (prefixWord ++ tailWord_6448800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448800).length < 2 ^ (prefixWord ++ tailWord_6448800).sum := by decide
  have hdescent : baseEnd_6448800 < baseStart_6448800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448819 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 4]
def baseStart_6448819 : Nat := 118140960795 + 6448819 * 2 ^ 59
def prefixEnd_6448819 : Nat := 4983230072969 + 3 ^ 40 * 6448819 * 2
def baseEnd_6448819 : Nat := 3311343800846909699704927

theorem tailTrace_6448819 : CollatzResearch.WordTrace tailWord_6448819 prefixEnd_6448819 3311343800846909699704927 := by
  unfold tailWord_6448819
  simp only [CollatzResearch.WordTrace]
  refine ⟨235207752024037608445717511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156805168016025072297145007 235207752024037608445717511)
  ·
    refine ⟨352811628036056412668576267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235207752024037608445717511 352811628036056412668576267)
    ·
      refine ⟨529217442054084619002864401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352811628036056412668576267 529217442054084619002864401)
      ·
        refine ⟨396913081540563464252148301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529217442054084619002864401 396913081540563464252148301)
        ·
          refine ⟨148842405577711299094555613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396913081540563464252148301 148842405577711299094555613)
          ·
            refine ⟨55815902091641737160458355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148842405577711299094555613 55815902091641737160458355)
            ·
              refine ⟨83723853137462605740687533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55815902091641737160458355 83723853137462605740687533)
              ·
                refine ⟨31396444926548477152757825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83723853137462605740687533 31396444926548477152757825)
                ·
                  refine ⟨23547333694911357864568369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31396444926548477152757825 23547333694911357864568369)
                  ·
                    refine ⟨17660500271183518398426277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23547333694911357864568369 17660500271183518398426277)
                    ·
                      refine ⟨3311343800846909699704927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17660500271183518398426277 3311343800846909699704927)
                      ·
                        rfl

theorem cell23_6448819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_6448819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448819 prefixEnd_6448819 := by exact prefixLift 6448819
  have htrace : WordTrace (prefixWord ++ tailWord_6448819) baseStart_6448819 baseEnd_6448819 := by
    simpa [prefixWord, tailWord_6448819, baseEnd_6448819] using wordTrace_append hprefix tailTrace_6448819
  have hstable : (prefixWord ++ tailWord_6448819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448819).length < 2 ^ (prefixWord ++ tailWord_6448819).sum := by decide
  have hdescent : baseEnd_6448819 < baseStart_6448819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448823 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 1, 4, 2]
def baseStart_6448823 : Nat := 118140960795 + 6448823 * 2 ^ 59
def prefixEnd_6448823 : Nat := 4983230072969 + 3 ^ 40 * 6448823 * 2
def baseEnd_6448823 : Nat := 3311345854769527684054909

theorem tailTrace_6448823 : CollatzResearch.WordTrace tailWord_6448823 prefixEnd_6448823 3311345854769527684054909 := by
  unfold tailWord_6448823
  simp only [CollatzResearch.WordTrace]
  refine ⟨235207897916023117128863123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156805265277348744752575415 235207897916023117128863123)
  ·
    refine ⟨352811846874034675693294685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235207897916023117128863123 352811846874034675693294685)
    ·
      refine ⟨132304442577763003384985507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352811846874034675693294685 132304442577763003384985507)
      ·
        refine ⟨198456663866644505077478261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132304442577763003384985507 198456663866644505077478261)
        ·
          refine ⟨18605312237497922351013587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198456663866644505077478261 18605312237497922351013587)
          ·
            refine ⟨27907968356246883526520381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18605312237497922351013587 27907968356246883526520381)
            ·
              refine ⟨10465488133592581322445143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27907968356246883526520381 10465488133592581322445143)
              ·
                refine ⟨15698232200388871983667715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10465488133592581322445143 15698232200388871983667715)
                ·
                  refine ⟨23547348300583307975501573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15698232200388871983667715 23547348300583307975501573)
                  ·
                    refine ⟨4415127806359370245406545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23547348300583307975501573 4415127806359370245406545)
                    ·
                      refine ⟨3311345854769527684054909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4415127806359370245406545 3311345854769527684054909)
                      ·
                        rfl

theorem cell23_6448823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 4, 2].length) (baseStart_6448823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448823 prefixEnd_6448823 := by exact prefixLift 6448823
  have htrace : WordTrace (prefixWord ++ tailWord_6448823) baseStart_6448823 baseEnd_6448823 := by
    simpa [prefixWord, tailWord_6448823, baseEnd_6448823] using wordTrace_append hprefix tailTrace_6448823
  have hstable : (prefixWord ++ tailWord_6448823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448823).length < 2 ^ (prefixWord ++ tailWord_6448823).sum := by decide
  have hdescent : baseEnd_6448823 < baseStart_6448823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448829 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 7]
def baseStart_6448829 : Nat := 118140960795 + 6448829 * 2 ^ 59
def prefixEnd_6448829 : Nat := 4983230072969 + 3 ^ 40 * 6448829 * 2
def baseEnd_6448829 : Nat := 367927659517050517842209

theorem tailTrace_6448829 : CollatzResearch.WordTrace tailWord_6448829 prefixEnd_6448829 367927659517050517842209 := by
  unfold tailWord_6448829
  simp only [CollatzResearch.WordTrace]
  refine ⟨235208116754001380153581541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156805411169334253435721027 235208116754001380153581541)
  ·
    refine ⟨44101521891375258778796539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235208116754001380153581541 44101521891375258778796539)
    ·
      refine ⟨66152282837062888168194809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44101521891375258778796539 66152282837062888168194809)
      ·
        refine ⟨49614212127797166126146107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66152282837062888168194809 49614212127797166126146107)
        ·
          refine ⟨74421318191695749189219161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49614212127797166126146107 74421318191695749189219161)
          ·
            refine ⟨55815988643771811891914371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74421318191695749189219161 55815988643771811891914371)
            ·
              refine ⟨83723982965657717837871557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55815988643771811891914371 83723982965657717837871557)
              ·
                refine ⟨15698246806060822094600917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83723982965657717837871557 15698246806060822094600917)
                ·
                  refine ⟨367927659517050517842209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15698246806060822094600917 367927659517050517842209)
                  ·
                    rfl

theorem cell23_6448829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_6448829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448829 prefixEnd_6448829 := by exact prefixLift 6448829
  have htrace : WordTrace (prefixWord ++ tailWord_6448829) baseStart_6448829 baseEnd_6448829 := by
    simpa [prefixWord, tailWord_6448829, baseEnd_6448829] using wordTrace_append hprefix tailTrace_6448829
  have hstable : (prefixWord ++ tailWord_6448829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448829).length < 2 ^ (prefixWord ++ tailWord_6448829).sum := by decide
  have hdescent : baseEnd_6448829 < baseStart_6448829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448863 : List Nat := [1, 1, 2, 3, 2, 2, 5, 2, 5]
def baseStart_6448863 : Nat := 118140960795 + 6448863 * 2 ^ 59
def prefixEnd_6448863 : Nat := 4983230072969 + 3 ^ 40 * 6448863 * 2
def baseEnd_6448863 : Nat := 367929599332856391950525

theorem tailTrace_6448863 : CollatzResearch.WordTrace tailWord_6448863 prefixEnd_6448863 367929599332856391950525 := by
  unfold tailWord_6448863
  simp only [CollatzResearch.WordTrace]
  refine ⟨235209356835878203960319243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156806237890585469306879495 235209356835878203960319243)
  ·
    refine ⟨352814035253817305940478865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235209356835878203960319243 352814035253817305940478865)
    ·
      refine ⟨264610526440362979455359149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352814035253817305940478865 264610526440362979455359149)
      ·
        refine ⟨99228947415136117295759681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264610526440362979455359149 99228947415136117295759681)
        ·
          refine ⟨74421710561352087971819761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99228947415136117295759681 74421710561352087971819761)
          ·
            refine ⟨55816282921014065978864821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74421710561352087971819761 55816282921014065978864821)
            ·
              refine ⟨5232776523845068685518577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55816282921014065978864821 5232776523845068685518577)
              ·
                refine ⟨3924582392883801514138933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5232776523845068685518577 3924582392883801514138933)
                ·
                  refine ⟨367929599332856391950525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3924582392883801514138933 367929599332856391950525)
                  ·
                    rfl

theorem cell23_6448863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 5].length) (baseStart_6448863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448863 prefixEnd_6448863 := by exact prefixLift 6448863
  have htrace : WordTrace (prefixWord ++ tailWord_6448863) baseStart_6448863 baseEnd_6448863 := by
    simpa [prefixWord, tailWord_6448863, baseEnd_6448863] using wordTrace_append hprefix tailTrace_6448863
  have hstable : (prefixWord ++ tailWord_6448863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448863).length < 2 ^ (prefixWord ++ tailWord_6448863).sum := by decide
  have hdescent : baseEnd_6448863 < baseStart_6448863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448896 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 1, 6, 2]
def baseStart_6448896 : Nat := 118140960795 + 6448896 * 2 ^ 59
def prefixEnd_6448896 : Nat := 4983230072969 + 3 ^ 40 * 6448896 * 2
def baseEnd_6448896 : Nat := 3311383338857305898442073

theorem tailTrace_6448896 : CollatzResearch.WordTrace tailWord_6448896 prefixEnd_6448896 3311383338857305898442073 := by
  unfold tailWord_6448896
  simp only [CollatzResearch.WordTrace]
  refine ⟨117605280222379325298135271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156807040296505767064180361 117605280222379325298135271)
  ·
    refine ⟨176407920333568987947202907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117605280222379325298135271 176407920333568987947202907)
    ·
      refine ⟨264611880500353481920804361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176407920333568987947202907 264611880500353481920804361)
      ·
        refine ⟨198458910375265111440603271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264611880500353481920804361 198458910375265111440603271)
        ·
          refine ⟨297688365562897667160904907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198458910375265111440603271 297688365562897667160904907)
          ·
            refine ⟨446532548344346500741357361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297688365562897667160904907 446532548344346500741357361)
            ·
              refine ⟨334899411258259875556018021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446532548344346500741357361 334899411258259875556018021)
              ·
                refine ⟨62793639610923726666753379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334899411258259875556018021 62793639610923726666753379)
                ·
                  refine ⟨94190459416385590000130069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62793639610923726666753379 94190459416385590000130069)
                  ·
                    refine ⟨4415177785143074531256097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94190459416385590000130069 4415177785143074531256097)
                    ·
                      refine ⟨3311383338857305898442073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4415177785143074531256097 3311383338857305898442073)
                      ·
                        rfl

theorem cell23_6448896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 6, 2].length) (baseStart_6448896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448896 prefixEnd_6448896 := by exact prefixLift 6448896
  have htrace : WordTrace (prefixWord ++ tailWord_6448896) baseStart_6448896 baseEnd_6448896 := by
    simpa [prefixWord, tailWord_6448896, baseEnd_6448896] using wordTrace_append hprefix tailTrace_6448896
  have hstable : (prefixWord ++ tailWord_6448896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448896).length < 2 ^ (prefixWord ++ tailWord_6448896).sum := by decide
  have hdescent : baseEnd_6448896 < baseStart_6448896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448923 : List Nat := [1, 1, 1, 1, 1, 1, 4, 8, 1, 4]
def baseStart_6448923 : Nat := 118140960795 + 6448923 * 2 ^ 59
def prefixEnd_6448923 : Nat := 4983230072969 + 3 ^ 40 * 6448923 * 2
def baseEnd_6448923 : Nat := 1103799067611659097601483

theorem tailTrace_6448923 : CollatzResearch.WordTrace tailWord_6448923 prefixEnd_6448923 1103799067611659097601483 := by
  unfold tailWord_6448923
  simp only [CollatzResearch.WordTrace]
  refine ⟨235211545215660834207503423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156807696810440556138335615 235211545215660834207503423)
  ·
    refine ⟨352817317823491251311255135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235211545215660834207503423 352817317823491251311255135)
    ·
      refine ⟨529225976735236876966882703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352817317823491251311255135 529225976735236876966882703)
      ·
        refine ⟨793838965102855315450324055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529225976735236876966882703 793838965102855315450324055)
        ·
          refine ⟨1190758447654282973175486083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793838965102855315450324055 1190758447654282973175486083)
          ·
            refine ⟨1786137671481424459763229125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190758447654282973175486083 1786137671481424459763229125)
            ·
              refine ⟨334900813402767086205605461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1786137671481424459763229125 334900813402767086205605461)
              ·
                refine ⟨3924618907063676791471939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 334900813402767086205605461 3924618907063676791471939)
                ·
                  refine ⟨5886928360595515187207909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924618907063676791471939 5886928360595515187207909)
                  ·
                    refine ⟨1103799067611659097601483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5886928360595515187207909 1103799067611659097601483)
                    ·
                      rfl

theorem cell23_6448923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 1, 4].length) (baseStart_6448923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448923 prefixEnd_6448923 := by exact prefixLift 6448923
  have htrace : WordTrace (prefixWord ++ tailWord_6448923) baseStart_6448923 baseEnd_6448923 := by
    simpa [prefixWord, tailWord_6448923, baseEnd_6448923] using wordTrace_append hprefix tailTrace_6448923
  have hstable : (prefixWord ++ tailWord_6448923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448923).length < 2 ^ (prefixWord ++ tailWord_6448923).sum := by decide
  have hdescent : baseEnd_6448923 < baseStart_6448923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448950 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_6448950 : Nat := 118140960795 + 6448950 * 2 ^ 59
def prefixEnd_6448950 : Nat := 4983230072969 + 3 ^ 40 * 6448950 * 2
def baseEnd_6448950 : Nat := 3311411066812648687166825

theorem tailTrace_6448950 : CollatzResearch.WordTrace tailWord_6448950 prefixEnd_6448950 3311411066812648687166825 := by
  unfold tailWord_6448950
  simp only [CollatzResearch.WordTrace]
  refine ⟨14700783124160188613671019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156808353324375345212490869 14700783124160188613671019)
  ·
    refine ⟨22051174686240282920506529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14700783124160188613671019 22051174686240282920506529)
    ·
      refine ⟨16538381014680212190379897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22051174686240282920506529 16538381014680212190379897)
      ·
        refine ⟨12403785761010159142784923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16538381014680212190379897 12403785761010159142784923)
        ·
          refine ⟨18605678641515238714177385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12403785761010159142784923 18605678641515238714177385)
          ·
            refine ⟨13954258981136429035633039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18605678641515238714177385 13954258981136429035633039)
            ·
              refine ⟨20931388471704643553449559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13954258981136429035633039 20931388471704643553449559)
              ·
                refine ⟨31397082707556965330174339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20931388471704643553449559 31397082707556965330174339)
                ·
                  refine ⟨47095624061335447995261509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31397082707556965330174339 47095624061335447995261509)
                  ·
                    refine ⟨8830429511500396499111533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47095624061335447995261509 8830429511500396499111533)
                    ·
                      refine ⟨3311411066812648687166825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8830429511500396499111533 3311411066812648687166825)
                      ·
                        rfl

theorem cell23_6448950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_6448950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448950 prefixEnd_6448950 := by exact prefixLift 6448950
  have htrace : WordTrace (prefixWord ++ tailWord_6448950) baseStart_6448950 baseEnd_6448950 := by
    simpa [prefixWord, tailWord_6448950, baseEnd_6448950] using wordTrace_append hprefix tailTrace_6448950
  have hstable : (prefixWord ++ tailWord_6448950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448950).length < 2 ^ (prefixWord ++ tailWord_6448950).sum := by decide
  have hdescent : baseEnd_6448950 < baseStart_6448950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448957 : List Nat := [1, 4, 1, 4, 1, 2, 2, 3, 1, 4]
def baseStart_6448957 : Nat := 118140960795 + 6448957 * 2 ^ 59
def prefixEnd_6448957 : Nat := 4983230072969 + 3 ^ 40 * 6448957 * 2
def baseEnd_6448957 : Nat := 1103804887059076719926431

theorem tailTrace_6448957 : CollatzResearch.WordTrace tailWord_6448957 prefixEnd_6448957 1103804887059076719926431 := by
  unfold tailWord_6448957
  simp only [CollatzResearch.WordTrace]
  refine ⟨235212785297537658014241125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156808523531691772009494083 235212785297537658014241125)
  ·
    refine ⟨44102397243288310877670211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235212785297537658014241125 44102397243288310877670211)
    ·
      refine ⟨66153595864932466316505317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44102397243288310877670211 66153595864932466316505317)
      ·
        refine ⟨12403799224674837434344747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66153595864932466316505317 12403799224674837434344747)
        ·
          refine ⟨18605698837012256151517121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12403799224674837434344747 18605698837012256151517121)
          ·
            refine ⟨13954274127759192113637841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18605698837012256151517121 13954274127759192113637841)
            ·
              refine ⟨10465705595819394085228381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13954274127759192113637841 10465705595819394085228381)
              ·
                refine ⟨3924639598432272781960643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10465705595819394085228381 3924639598432272781960643)
                ·
                  refine ⟨5886959397648409172940965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924639598432272781960643 5886959397648409172940965)
                  ·
                    refine ⟨1103804887059076719926431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5886959397648409172940965 1103804887059076719926431)
                    ·
                      rfl

theorem cell23_6448957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_6448957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448957 prefixEnd_6448957 := by exact prefixLift 6448957
  have htrace : WordTrace (prefixWord ++ tailWord_6448957) baseStart_6448957 baseEnd_6448957 := by
    simpa [prefixWord, tailWord_6448957, baseEnd_6448957] using wordTrace_append hprefix tailTrace_6448957
  have hstable : (prefixWord ++ tailWord_6448957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448957).length < 2 ^ (prefixWord ++ tailWord_6448957).sum := by decide
  have hdescent : baseEnd_6448957 < baseStart_6448957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448973 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_6448973 : Nat := 118140960795 + 6448973 * 2 ^ 59
def prefixEnd_6448973 : Nat := 4983230072969 + 3 ^ 40 * 6448973 * 2
def baseEnd_6448973 : Nat := 3311422876867702097179219

theorem tailTrace_6448973 : CollatzResearch.WordTrace tailWord_6448973 prefixEnd_6448973 3311422876867702097179219 := by
  unfold tailWord_6448973
  simp only [CollatzResearch.WordTrace]
  refine ⟨235213368865479692746823573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156808912576986461831215715 235213368865479692746823573)
  ·
    refine ⟨11025626665569360597507355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 235213368865479692746823573 11025626665569360597507355)
    ·
      refine ⟨16538439998354040896261033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11025626665569360597507355 16538439998354040896261033)
      ·
        refine ⟨12403829998765530672195775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16538439998354040896261033 12403829998765530672195775)
        ·
          refine ⟨18605744998148296008293663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12403829998765530672195775 18605744998148296008293663)
          ·
            refine ⟨27908617497222444012440495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18605744998148296008293663 27908617497222444012440495)
            ·
              refine ⟨41862926245833666018660743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27908617497222444012440495 41862926245833666018660743)
              ·
                refine ⟨62794389368750499027991115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41862926245833666018660743 62794389368750499027991115)
                ·
                  refine ⟨94191584053125748541986673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62794389368750499027991115 94191584053125748541986673)
                  ·
                    refine ⟨70643688039844311406490005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94191584053125748541986673 70643688039844311406490005)
                    ·
                      refine ⟨3311422876867702097179219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70643688039844311406490005 3311422876867702097179219)
                      ·
                        rfl

theorem cell23_6448973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_6448973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448973 prefixEnd_6448973 := by exact prefixLift 6448973
  have htrace : WordTrace (prefixWord ++ tailWord_6448973) baseStart_6448973 baseEnd_6448973 := by
    simpa [prefixWord, tailWord_6448973, baseEnd_6448973] using wordTrace_append hprefix tailTrace_6448973
  have hstable : (prefixWord ++ tailWord_6448973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448973).length < 2 ^ (prefixWord ++ tailWord_6448973).sum := by decide
  have hdescent : baseEnd_6448973 < baseStart_6448973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448979 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 2, 10]
def baseStart_6448979 : Nat := 118140960795 + 6448979 * 2 ^ 59
def prefixEnd_6448979 : Nat := 4983230072969 + 3 ^ 40 * 6448979 * 2
def baseEnd_6448979 : Nat := 1103808652583876357901397

theorem tailTrace_6448979 : CollatzResearch.WordTrace tailWord_6448979 prefixEnd_6448979 1103808652583876357901397 := by
  unfold tailWord_6448979
  simp only [CollatzResearch.WordTrace]
  refine ⟨235213587703457955771541991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156809058468971970514361327 235213587703457955771541991)
  ·
    refine ⟨352820381555186933657312987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235213587703457955771541991 352820381555186933657312987)
    ·
      refine ⟨529230572332780400485969481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352820381555186933657312987 529230572332780400485969481)
      ·
        refine ⟨396922929249585300364477111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529230572332780400485969481 396922929249585300364477111)
        ·
          refine ⟨595384393874377950546715667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396922929249585300364477111 595384393874377950546715667)
          ·
            refine ⟨893076590811566925820073501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595384393874377950546715667 893076590811566925820073501)
            ·
              refine ⟨334903721554337597182527563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 893076590811566925820073501 334903721554337597182527563)
              ·
                refine ⟨502355582331506395773791345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334903721554337597182527563 502355582331506395773791345)
                ·
                  refine ⟨376766686748629796830343509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502355582331506395773791345 376766686748629796830343509)
                  ·
                    refine ⟨1103808652583876357901397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 376766686748629796830343509 1103808652583876357901397)
                    ·
                      rfl

theorem cell23_6448979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 10].length) (baseStart_6448979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448979 prefixEnd_6448979 := by exact prefixLift 6448979
  have htrace : WordTrace (prefixWord ++ tailWord_6448979) baseStart_6448979 baseEnd_6448979 := by
    simpa [prefixWord, tailWord_6448979, baseEnd_6448979] using wordTrace_append hprefix tailTrace_6448979
  have hstable : (prefixWord ++ tailWord_6448979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448979).length < 2 ^ (prefixWord ++ tailWord_6448979).sum := by decide
  have hdescent : baseEnd_6448979 < baseStart_6448979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6448980 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_6448980 : Nat := 118140960795 + 6448980 * 2 ^ 59
def prefixEnd_6448980 : Nat := 4983230072969 + 3 ^ 40 * 6448980 * 2
def baseEnd_6448980 : Nat := 3311426471232283569791687

theorem tailTrace_6448980 : CollatzResearch.WordTrace tailWord_6448980 prefixEnd_6448980 3311426471232283569791687 := by
  unfold tailWord_6448980
  simp only [CollatzResearch.WordTrace]
  refine ⟨117606812088227166471164197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156809082784302888628218929 117606812088227166471164197)
  ·
    refine ⟨22051277266542593713343287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117606812088227166471164197 22051277266542593713343287)
    ·
      refine ⟨33076915899813890570014931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22051277266542593713343287 33076915899813890570014931)
      ·
        refine ⟨49615373849720835855022397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33076915899813890570014931 49615373849720835855022397)
        ·
          refine ⟨18605765193645313445633399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49615373849720835855022397 18605765193645313445633399)
          ·
            refine ⟨27908647790467970168450099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18605765193645313445633399 27908647790467970168450099)
            ·
              refine ⟨41862971685701955252675149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27908647790467970168450099 41862971685701955252675149)
              ·
                refine ⟨15698614382138233219753181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41862971685701955252675149 15698614382138233219753181)
                ·
                  refine ⟨5886980393301837457407443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15698614382138233219753181 5886980393301837457407443)
                  ·
                    refine ⟨8830470589952756186111165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5886980393301837457407443 8830470589952756186111165)
                    ·
                      refine ⟨3311426471232283569791687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8830470589952756186111165 3311426471232283569791687)
                      ·
                        rfl

theorem cell23_6448980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_6448980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6448980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6448980 prefixEnd_6448980 := by exact prefixLift 6448980
  have htrace : WordTrace (prefixWord ++ tailWord_6448980) baseStart_6448980 baseEnd_6448980 := by
    simpa [prefixWord, tailWord_6448980, baseEnd_6448980] using wordTrace_append hprefix tailTrace_6448980
  have hstable : (prefixWord ++ tailWord_6448980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6448980).length < 2 ^ (prefixWord ++ tailWord_6448980).sum := by decide
  have hdescent : baseEnd_6448980 < baseStart_6448980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6448980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449013 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 6, 4]
def baseStart_6449013 : Nat := 118140960795 + 6449013 * 2 ^ 59
def prefixEnd_6449013 : Nat := 4983230072969 + 3 ^ 40 * 6449013 * 2
def baseEnd_6449013 : Nat := 1103814472031293980226345

theorem tailTrace_6449013 : CollatzResearch.WordTrace tailWord_6449013 prefixEnd_6449013 1103814472031293980226345 := by
  unfold tailWord_6449013
  simp only [CollatzResearch.WordTrace]
  refine ⟨235214827785334779578279693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156809885190223186385519795 235214827785334779578279693)
  ·
    refine ⟨88205560419500542341854885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235214827785334779578279693 88205560419500542341854885)
    ·
      refine ⟨16538542578656351689097791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88205560419500542341854885 16538542578656351689097791)
      ·
        refine ⟨24807813867984527533646687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16538542578656351689097791 24807813867984527533646687)
        ·
          refine ⟨37211720801976791300470031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24807813867984527533646687 37211720801976791300470031)
          ·
            refine ⟨55817581202965186950705047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37211720801976791300470031 55817581202965186950705047)
            ·
              refine ⟨83726371804447780426057571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55817581202965186950705047 83726371804447780426057571)
              ·
                refine ⟨125589557706671670639086357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83726371804447780426057571 125589557706671670639086357)
                ·
                  refine ⟨5887010517500234561207173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125589557706671670639086357 5887010517500234561207173)
                  ·
                    refine ⟨1103814472031293980226345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5887010517500234561207173 1103814472031293980226345)
                    ·
                      rfl

theorem cell23_6449013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_6449013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449013 prefixEnd_6449013 := by exact prefixLift 6449013
  have htrace : WordTrace (prefixWord ++ tailWord_6449013) baseStart_6449013 baseEnd_6449013 := by
    simpa [prefixWord, tailWord_6449013, baseEnd_6449013] using wordTrace_append hprefix tailTrace_6449013
  have hstable : (prefixWord ++ tailWord_6449013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449013).length < 2 ^ (prefixWord ++ tailWord_6449013).sum := by decide
  have hdescent : baseEnd_6449013 < baseStart_6449013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449047 : List Nat := [1, 1, 3, 3, 1, 5, 2, 1, 2, 4]
def baseStart_6449047 : Nat := 118140960795 + 6449047 * 2 ^ 59
def prefixEnd_6449047 : Nat := 4983230072969 + 3 ^ 40 * 6449047 * 2
def baseEnd_6449047 : Nat := 1103820291478711602551293

theorem tailTrace_6449047 : CollatzResearch.WordTrace tailWord_6449047 prefixEnd_6449047 1103820291478711602551293 := by
  unfold tailWord_6449047
  simp only [CollatzResearch.WordTrace]
  refine ⟨235216067867211603385017395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156810711911474402256678263 235216067867211603385017395)
  ·
    refine ⟨352824101800817405077526093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235216067867211603385017395 352824101800817405077526093)
    ·
      refine ⟨132309038175306526904072285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352824101800817405077526093 132309038175306526904072285)
      ·
        refine ⟨49615889315739947589027107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132309038175306526904072285 49615889315739947589027107)
        ·
          refine ⟨74423833973609921383540661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49615889315739947589027107 74423833973609921383540661)
          ·
            refine ⟨6977234435025930129706937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74423833973609921383540661 6977234435025930129706937)
            ·
              refine ⟨5232925826269447597280203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6977234435025930129706937 5232925826269447597280203)
              ·
                refine ⟨7849388739404171395920305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5232925826269447597280203 7849388739404171395920305)
                ·
                  refine ⟨5887041554553128546940229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7849388739404171395920305 5887041554553128546940229)
                  ·
                    refine ⟨1103820291478711602551293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5887041554553128546940229 1103820291478711602551293)
                    ·
                      rfl

theorem cell23_6449047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_6449047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449047 prefixEnd_6449047 := by exact prefixLift 6449047
  have htrace : WordTrace (prefixWord ++ tailWord_6449047) baseStart_6449047 baseEnd_6449047 := by
    simpa [prefixWord, tailWord_6449047, baseEnd_6449047] using wordTrace_append hprefix tailTrace_6449047
  have hstable : (prefixWord ++ tailWord_6449047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449047).length < 2 ^ (prefixWord ++ tailWord_6449047).sum := by decide
  have hdescent : baseEnd_6449047 < baseStart_6449047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449150 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 7]
def baseStart_6449150 : Nat := 118140960795 + 6449150 * 2 ^ 59
def prefixEnd_6449150 : Nat := 4983230072969 + 3 ^ 40 * 6449150 * 2
def baseEnd_6449150 : Nat := 367945973660394211629545

theorem tailTrace_6449150 : CollatzResearch.WordTrace tailWord_6449150 prefixEnd_6449150 367945973660394211629545 := by
  unfold tailWord_6449150
  simp only [CollatzResearch.WordTrace]
  refine ⟨29402478073229806497002113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156813216390558967984011269 29402478073229806497002113)
  ·
    refine ⟨22051858554922354872751585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29402478073229806497002113 22051858554922354872751585)
    ·
      refine ⟨16538893916191766154563689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22051858554922354872751585 16538893916191766154563689)
      ·
        refine ⟨12404170437143824615922767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16538893916191766154563689 12404170437143824615922767)
        ·
          refine ⟨18606255655715736923884151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12404170437143824615922767 18606255655715736923884151)
          ·
            refine ⟨27909383483573605385826227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18606255655715736923884151 27909383483573605385826227)
            ·
              refine ⟨41864075225360408078739341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27909383483573605385826227 41864075225360408078739341)
              ·
                refine ⟨15699028209510153029527253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41864075225360408078739341 15699028209510153029527253)
                ·
                  refine ⟨367945973660394211629545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15699028209510153029527253 367945973660394211629545)
                  ·
                    rfl

theorem cell23_6449150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_6449150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449150 prefixEnd_6449150 := by exact prefixLift 6449150
  have htrace : WordTrace (prefixWord ++ tailWord_6449150) baseStart_6449150 baseEnd_6449150 := by
    simpa [prefixWord, tailWord_6449150, baseEnd_6449150] using wordTrace_append hprefix tailTrace_6449150
  have hstable : (prefixWord ++ tailWord_6449150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449150).length < 2 ^ (prefixWord ++ tailWord_6449150).sum := by decide
  have hdescent : baseEnd_6449150 < baseStart_6449150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449183 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 4]
def baseStart_6449183 : Nat := 118140960795 + 6449183 * 2 ^ 59
def prefixEnd_6449183 : Nat := 4983230072969 + 3 ^ 40 * 6449183 * 2
def baseEnd_6449183 : Nat := 3311530707805146275553253

theorem tailTrace_6449183 : CollatzResearch.WordTrace tailWord_6449183 prefixEnd_6449183 3311530707805146275553253 := by
  unfold tailWord_6449183
  simp only [CollatzResearch.WordTrace]
  refine ⟨235221028194718898611968203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156814018796479265741312135 235221028194718898611968203)
  ·
    refine ⟨352831542292078347917952305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235221028194718898611968203 352831542292078347917952305)
    ·
      refine ⟨264623656719058760938464229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352831542292078347917952305 264623656719058760938464229)
      ·
        refine ⟨49616935634823517675962043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264623656719058760938464229 49616935634823517675962043)
        ·
          refine ⟨74425403452235276513943065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49616935634823517675962043 74425403452235276513943065)
          ·
            refine ⟨55819052589176457385457299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74425403452235276513943065 55819052589176457385457299)
            ·
              refine ⟨83728578883764686078185949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55819052589176457385457299 83728578883764686078185949)
              ·
                refine ⟨31398217081411757279319731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83728578883764686078185949 31398217081411757279319731)
                ·
                  refine ⟨47097325622117635918979597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31398217081411757279319731 47097325622117635918979597)
                  ·
                    refine ⟨17661497108294113469617349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47097325622117635918979597 17661497108294113469617349)
                    ·
                      refine ⟨3311530707805146275553253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17661497108294113469617349 3311530707805146275553253)
                      ·
                        rfl

theorem cell23_6449183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_6449183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449183 prefixEnd_6449183 := by exact prefixLift 6449183
  have htrace : WordTrace (prefixWord ++ tailWord_6449183) baseStart_6449183 baseEnd_6449183 := by
    simpa [prefixWord, tailWord_6449183, baseEnd_6449183] using wordTrace_append hprefix tailTrace_6449183
  have hstable : (prefixWord ++ tailWord_6449183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449183).length < 2 ^ (prefixWord ++ tailWord_6449183).sum := by decide
  have hdescent : baseEnd_6449183 < baseStart_6449183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449200 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 4]
def baseStart_6449200 : Nat := 118140960795 + 6449200 * 2 ^ 59
def prefixEnd_6449200 : Nat := 4983230072969 + 3 ^ 40 * 6449200 * 2
def baseEnd_6449200 : Nat := 3311539436976272709040675

theorem tailTrace_6449200 : CollatzResearch.WordTrace tailWord_6449200 prefixEnd_6449200 3311539436976272709040675 := by
  unfold tailWord_6449200
  simp only [CollatzResearch.WordTrace]
  refine ⟨117610824117828655257668527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156814432157104873676891369 117610824117828655257668527)
  ·
    refine ⟨176416236176742982886502791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117610824117828655257668527 176416236176742982886502791)
    ·
      refine ⟨264624354265114474329754187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176416236176742982886502791 264624354265114474329754187)
      ·
        refine ⟨396936531397671711494631281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264624354265114474329754187 396936531397671711494631281)
        ·
          refine ⟨297702398548253783620973461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396936531397671711494631281 297702398548253783620973461)
          ·
            refine ⟨13954799931949396107233131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 297702398548253783620973461 13954799931949396107233131)
            ·
              refine ⟨20932199897924094160849697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13954799931949396107233131 20932199897924094160849697)
              ·
                refine ⟨15699149923443070620637273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20932199897924094160849697 15699149923443070620637273)
                ·
                  refine ⟨11774362442582302965477955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15699149923443070620637273 11774362442582302965477955)
                  ·
                    refine ⟨17661543663873454448216933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11774362442582302965477955 17661543663873454448216933)
                    ·
                      refine ⟨3311539436976272709040675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17661543663873454448216933 3311539436976272709040675)
                      ·
                        rfl

theorem cell23_6449200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_6449200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449200 prefixEnd_6449200 := by exact prefixLift 6449200
  have htrace : WordTrace (prefixWord ++ tailWord_6449200) baseStart_6449200 baseEnd_6449200 := by
    simpa [prefixWord, tailWord_6449200, baseEnd_6449200] using wordTrace_append hprefix tailTrace_6449200
  have hstable : (prefixWord ++ tailWord_6449200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449200).length < 2 ^ (prefixWord ++ tailWord_6449200).sum := by decide
  have hdescent : baseEnd_6449200 < baseStart_6449200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449237 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_6449237 : Nat := 118140960795 + 6449237 * 2 ^ 59
def prefixEnd_6449237 : Nat := 4983230072969 + 3 ^ 40 * 6449237 * 2
def baseEnd_6449237 : Nat := 3311558435760489064278005

theorem tailTrace_6449237 : CollatzResearch.WordTrace tailWord_6449237 prefixEnd_6449237 3311558435760489064278005 := by
  unfold tailWord_6449237
  simp only [CollatzResearch.WordTrace]
  refine ⟨235222997736523265834433965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156815331824348843889622643 235222997736523265834433965)
  ·
    refine ⟨88208624151196224687912737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235222997736523265834433965 88208624151196224687912737)
    ·
      refine ⟨66156468113397168515934553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88208624151196224687912737 66156468113397168515934553)
      ·
        refine ⟨49617351085047876386950915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66156468113397168515934553 49617351085047876386950915)
        ·
          refine ⟨74426026627571814580426373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49617351085047876386950915 74426026627571814580426373)
          ·
            refine ⟨13954879992669715233829945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74426026627571814580426373 13954879992669715233829945)
            ·
              refine ⟨10466159994502286425372459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13954879992669715233829945 10466159994502286425372459)
              ·
                refine ⟨15699239991753429638058689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10466159994502286425372459 15699239991753429638058689)
                ·
                  refine ⟨11774429993815072228544017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15699239991753429638058689 11774429993815072228544017)
                  ·
                    refine ⟨8830822495361304171408013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11774429993815072228544017 8830822495361304171408013)
                    ·
                      refine ⟨3311558435760489064278005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8830822495361304171408013 3311558435760489064278005)
                      ·
                        rfl

theorem cell23_6449237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_6449237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449237 prefixEnd_6449237 := by exact prefixLift 6449237
  have htrace : WordTrace (prefixWord ++ tailWord_6449237) baseStart_6449237 baseEnd_6449237 := by
    simpa [prefixWord, tailWord_6449237, baseEnd_6449237] using wordTrace_append hprefix tailTrace_6449237
  have hstable : (prefixWord ++ tailWord_6449237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449237).length < 2 ^ (prefixWord ++ tailWord_6449237).sum := by decide
  have hdescent : baseEnd_6449237 < baseStart_6449237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449294 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2]
def baseStart_6449294 : Nat := 118140960795 + 6449294 * 2 ^ 59
def prefixEnd_6449294 : Nat := 4983230072969 + 3 ^ 40 * 6449294 * 2
def baseEnd_6449294 : Nat := 3311587704157795341265243

theorem tailTrace_6449294 : CollatzResearch.WordTrace tailWord_6449294 prefixEnd_6449294 3311587704157795341265243 := by
  unfold tailWord_6449294
  simp only [CollatzResearch.WordTrace]
  refine ⟨29403134587164595571157367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156816717798211176379505957 29403134587164595571157367)
  ·
    refine ⟨44104701880746893356736051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29403134587164595571157367 44104701880746893356736051)
    ·
      refine ⟨66157052821120340035104077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44104701880746893356736051 66157052821120340035104077)
      ·
        refine ⟨24808894807920127513164029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66157052821120340035104077 24808894807920127513164029)
        ·
          refine ⟨9303335552970047817436511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24808894807920127513164029 9303335552970047817436511)
          ·
            refine ⟨13955003329455071726154767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9303335552970047817436511 13955003329455071726154767)
            ·
              refine ⟨20932504994182607589232151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13955003329455071726154767 20932504994182607589232151)
              ·
                refine ⟨31398757491273911383848227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20932504994182607589232151 31398757491273911383848227)
                ·
                  refine ⟨47098136236910867075772341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31398757491273911383848227 47098136236910867075772341)
                  ·
                    refine ⟨4415450272210393788353657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47098136236910867075772341 4415450272210393788353657)
                    ·
                      refine ⟨3311587704157795341265243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4415450272210393788353657 3311587704157795341265243)
                      ·
                        rfl

theorem cell23_6449294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_6449294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449294 prefixEnd_6449294 := by exact prefixLift 6449294
  have htrace : WordTrace (prefixWord ++ tailWord_6449294) baseStart_6449294 baseEnd_6449294 := by
    simpa [prefixWord, tailWord_6449294, baseEnd_6449294] using wordTrace_append hprefix tailTrace_6449294
  have hstable : (prefixWord ++ tailWord_6449294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449294).length < 2 ^ (prefixWord ++ tailWord_6449294).sum := by decide
  have hdescent : baseEnd_6449294 < baseStart_6449294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449307 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 5, 2, 2]
def baseStart_6449307 : Nat := 118140960795 + 6449307 * 2 ^ 59
def prefixEnd_6449307 : Nat := 4983230072969 + 3 ^ 40 * 6449307 * 2
def baseEnd_6449307 : Nat := 3311594379406303790402683

theorem tailTrace_6449307 : CollatzResearch.WordTrace tailWord_6449307 prefixEnd_6449307 3311594379406303790402683 := by
  unfold tailWord_6449307
  simp only [CollatzResearch.WordTrace]
  refine ⟨235225550846269667789482175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156817033897513111859654783 235225550846269667789482175)
  ·
    refine ⟨352838326269404501684223263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235225550846269667789482175 352838326269404501684223263)
    ·
      refine ⟨529257489404106752526334895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352838326269404501684223263 529257489404106752526334895)
      ·
        refine ⟨793886234106160128789502343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529257489404106752526334895 793886234106160128789502343)
        ·
          refine ⟨1190829351159240193184253515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793886234106160128789502343 1190829351159240193184253515)
          ·
            refine ⟨1786244026738860289776380273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190829351159240193184253515 1786244026738860289776380273)
            ·
              refine ⟨1339683020054145217332285205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1786244026738860289776380273 1339683020054145217332285205)
              ·
                refine ⟨62797641565038057062450869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1339683020054145217332285205 62797641565038057062450869)
                ·
                  refine ⟨5887278896722317849604769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62797641565038057062450869 5887278896722317849604769)
                  ·
                    refine ⟨4415459172541738387203577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5887278896722317849604769 4415459172541738387203577)
                    ·
                      refine ⟨3311594379406303790402683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4415459172541738387203577 3311594379406303790402683)
                      ·
                        rfl

theorem cell23_6449307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 2, 2].length) (baseStart_6449307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449307 prefixEnd_6449307 := by exact prefixLift 6449307
  have htrace : WordTrace (prefixWord ++ tailWord_6449307) baseStart_6449307 baseEnd_6449307 := by
    simpa [prefixWord, tailWord_6449307, baseEnd_6449307] using wordTrace_append hprefix tailTrace_6449307
  have hstable : (prefixWord ++ tailWord_6449307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449307).length < 2 ^ (prefixWord ++ tailWord_6449307).sum := by decide
  have hdescent : baseEnd_6449307 < baseStart_6449307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449344 : List Nat := [2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 3]
def baseStart_6449344 : Nat := 118140960795 + 6449344 * 2 ^ 59
def prefixEnd_6449344 : Nat := 4983230072969 + 3 ^ 40 * 6449344 * 2
def baseEnd_6449344 : Nat := 3311613378190520145640013

theorem tailTrace_6449344 : CollatzResearch.WordTrace tailWord_6449344 prefixEnd_6449344 3311613378190520145640013 := by
  unfold tailWord_6449344
  simp only [CollatzResearch.WordTrace]
  refine ⟨117613450173567811554289543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156817933564757082072386057 117613450173567811554289543)
  ·
    refine ⟨176420175260351717331434315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117613450173567811554289543 176420175260351717331434315)
    ·
      refine ⟨264630262890527575997151473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176420175260351717331434315 264630262890527575997151473)
      ·
        refine ⟨198472697167895681997863605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264630262890527575997151473 198472697167895681997863605)
        ·
          refine ⟨18606815359490220187299713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198472697167895681997863605 18606815359490220187299713)
          ·
            refine ⟨13955111519617665140474785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18606815359490220187299713 13955111519617665140474785)
            ·
              refine ⟨10466333639713248855356089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13955111519617665140474785 10466333639713248855356089)
              ·
                refine ⟨7849750229784936641517067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10466333639713248855356089 7849750229784936641517067)
                ·
                  refine ⟨11774625344677404962275601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7849750229784936641517067 11774625344677404962275601)
                  ·
                    refine ⟨8830969008508053721706701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11774625344677404962275601 8830969008508053721706701)
                    ·
                      refine ⟨3311613378190520145640013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8830969008508053721706701 3311613378190520145640013)
                      ·
                        rfl

theorem cell23_6449344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_6449344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449344 prefixEnd_6449344 := by exact prefixLift 6449344
  have htrace : WordTrace (prefixWord ++ tailWord_6449344) baseStart_6449344 baseEnd_6449344 := by
    simpa [prefixWord, tailWord_6449344, baseEnd_6449344] using wordTrace_append hprefix tailTrace_6449344
  have hstable : (prefixWord ++ tailWord_6449344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449344).length < 2 ^ (prefixWord ++ tailWord_6449344).sum := by decide
  have hdescent : baseEnd_6449344 < baseStart_6449344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449358 : List Nat := [4, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2]
def baseStart_6449358 : Nat := 118140960795 + 6449358 * 2 ^ 59
def prefixEnd_6449358 : Nat := 4983230072969 + 3 ^ 40 * 6449358 * 2
def baseEnd_6449358 : Nat := 3311620566919683090864949

theorem tailTrace_6449358 : CollatzResearch.WordTrace tailWord_6449358 prefixEnd_6449358 3311620566919683090864949 := by
  unfold tailWord_6449358
  simp only [CollatzResearch.WordTrace]
  refine ⟨29403426371135612937448591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156818273979389935666392485 29403426371135612937448591)
  ·
    refine ⟨44105139556703419406172887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29403426371135612937448591 44105139556703419406172887)
    ·
      refine ⟨66157709335055129109259331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44105139556703419406172887 66157709335055129109259331)
      ·
        refine ⟨99236564002582693663888997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66157709335055129109259331 99236564002582693663888997)
        ·
          refine ⟨18606855750484255061979187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99236564002582693663888997 18606855750484255061979187)
          ·
            refine ⟨27910283625726382592968781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18606855750484255061979187 27910283625726382592968781)
            ·
              refine ⟨10466356359647393472363293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27910283625726382592968781 10466356359647393472363293)
              ·
                refine ⟨3924883634867772552136235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10466356359647393472363293 3924883634867772552136235)
                ·
                  refine ⟨5887325452301658828204353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924883634867772552136235 5887325452301658828204353)
                  ·
                    refine ⟨4415494089226244121153265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5887325452301658828204353 4415494089226244121153265)
                    ·
                      refine ⟨3311620566919683090864949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4415494089226244121153265 3311620566919683090864949)
                      ·
                        rfl

theorem cell23_6449358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_6449358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449358 prefixEnd_6449358 := by exact prefixLift 6449358
  have htrace : WordTrace (prefixWord ++ tailWord_6449358) baseStart_6449358 baseEnd_6449358 := by
    simpa [prefixWord, tailWord_6449358, baseEnd_6449358] using wordTrace_append hprefix tailTrace_6449358
  have hstable : (prefixWord ++ tailWord_6449358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449358).length < 2 ^ (prefixWord ++ tailWord_6449358).sum := by decide
  have hdescent : baseEnd_6449358 < baseStart_6449358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449367 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 5, 3, 2]
def baseStart_6449367 : Nat := 118140960795 + 6449367 * 2 ^ 59
def prefixEnd_6449367 : Nat := 4983230072969 + 3 ^ 40 * 6449367 * 2
def baseEnd_6449367 : Nat := 3311625188245573555652407

theorem tailTrace_6449367 : CollatzResearch.WordTrace tailWord_6449367 prefixEnd_6449367 3311625188245573555652407 := by
  unfold tailWord_6449367
  simp only [CollatzResearch.WordTrace]
  refine ⟨235227739226052298036666355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156818492817368198691110903 235227739226052298036666355)
  ·
    refine ⟨352841608839078447054999533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235227739226052298036666355 352841608839078447054999533)
    ·
      refine ⟨132315603314654417645624825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352841608839078447054999533 132315603314654417645624825)
      ·
        refine ⟨99236702485990813234218619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132315603314654417645624825 99236702485990813234218619)
        ·
          refine ⟨148855053728986219851327929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99236702485990813234218619 148855053728986219851327929)
          ·
            refine ⟨111641290296739664888495947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148855053728986219851327929 111641290296739664888495947)
            ·
              refine ⟨167461935445109497332743921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111641290296739664888495947 167461935445109497332743921)
              ·
                refine ⟨125596451583832122999557941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167461935445109497332743921 125596451583832122999557941)
                ·
                  refine ⟨11774667335984261531208557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125596451583832122999557941 11774667335984261531208557)
                  ·
                    refine ⟨4415500250994098074203209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11774667335984261531208557 4415500250994098074203209)
                    ·
                      refine ⟨3311625188245573555652407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4415500250994098074203209 3311625188245573555652407)
                      ·
                        rfl

theorem cell23_6449367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_6449367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449367 prefixEnd_6449367 := by exact prefixLift 6449367
  have htrace : WordTrace (prefixWord ++ tailWord_6449367) baseStart_6449367 baseEnd_6449367 := by
    simpa [prefixWord, tailWord_6449367, baseEnd_6449367] using wordTrace_append hprefix tailTrace_6449367
  have hstable : (prefixWord ++ tailWord_6449367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449367).length < 2 ^ (prefixWord ++ tailWord_6449367).sum := by decide
  have hdescent : baseEnd_6449367 < baseStart_6449367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449380 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_6449380 : Nat := 118140960795 + 6449380 * 2 ^ 59
def prefixEnd_6449380 : Nat := 4983230072969 + 3 ^ 40 * 6449380 * 2
def baseEnd_6449380 : Nat := 3311631863494082004789847

theorem tailTrace_6449380 : CollatzResearch.WordTrace tailWord_6449380 prefixEnd_6449380 3311631863494082004789847 := by
  unfold tailWord_6449380
  simp only [CollatzResearch.WordTrace]
  refine ⟨117614106687502600628444797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156818808916670134171259729 117614106687502600628444797)
  ·
    refine ⟨44105290007813475235666799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117614106687502600628444797 44105290007813475235666799)
    ·
      refine ⟨66157935011720212853500199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44105290007813475235666799 66157935011720212853500199)
      ·
        refine ⟨99236902517580319280250299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66157935011720212853500199 99236902517580319280250299)
        ·
          refine ⟨148855353776370478920375449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99236902517580319280250299 148855353776370478920375449)
          ·
            refine ⟨111641515332277859190281587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148855353776370478920375449 111641515332277859190281587)
            ·
              refine ⟨167462272998416788785422381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111641515332277859190281587 167462272998416788785422381)
              ·
                refine ⟨62798352374406295794533393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167462272998416788785422381 62798352374406295794533393)
                ·
                  refine ⟨47098764280804721845900045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62798352374406295794533393 47098764280804721845900045)
                  ·
                    refine ⟨17662036605301770692212517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47098764280804721845900045 17662036605301770692212517)
                    ·
                      refine ⟨3311631863494082004789847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17662036605301770692212517 3311631863494082004789847)
                      ·
                        rfl

theorem cell23_6449380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_6449380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449380 prefixEnd_6449380 := by exact prefixLift 6449380
  have htrace : WordTrace (prefixWord ++ tailWord_6449380) baseStart_6449380 baseEnd_6449380 := by
    simpa [prefixWord, tailWord_6449380, baseEnd_6449380] using wordTrace_append hprefix tailTrace_6449380
  have hstable : (prefixWord ++ tailWord_6449380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449380).length < 2 ^ (prefixWord ++ tailWord_6449380).sum := by decide
  have hdescent : baseEnd_6449380 < baseStart_6449380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449390 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_6449390 : Nat := 118140960795 + 6449390 * 2 ^ 59
def prefixEnd_6449390 : Nat := 4983230072969 + 3 ^ 40 * 6449390 * 2
def baseEnd_6449390 : Nat := 1103878999433542321888267

theorem tailTrace_6449390 : CollatzResearch.WordTrace tailWord_6449390 prefixEnd_6449390 1103878999433542321888267 := by
  unfold tailWord_6449390
  simp only [CollatzResearch.WordTrace]
  refine ⟨29403572263121121620594203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156819052069979315309835749 29403572263121121620594203)
  ·
    refine ⟨44105358394681682430891305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29403572263121121620594203 44105358394681682430891305)
    ·
      refine ⟨33079018796011261823168479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44105358394681682430891305 33079018796011261823168479)
      ·
        refine ⟨49618528194016892734752719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33079018796011261823168479 49618528194016892734752719)
        ·
          refine ⟨74427792291025339102129079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49618528194016892734752719 74427792291025339102129079)
          ·
            refine ⟨111641688436538008653193619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74427792291025339102129079 111641688436538008653193619)
            ·
              refine ⟨167462532654807012979790429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111641688436538008653193619 167462532654807012979790429)
              ·
                refine ⟨62798449745552629867421411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167462532654807012979790429 62798449745552629867421411)
                ·
                  refine ⟨94197674618328944801132117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62798449745552629867421411 94197674618328944801132117)
                  ·
                    refine ⟨1103878999433542321888267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94197674618328944801132117 1103878999433542321888267)
                    ·
                      rfl

theorem cell23_6449390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_6449390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449390 prefixEnd_6449390 := by exact prefixLift 6449390
  have htrace : WordTrace (prefixWord ++ tailWord_6449390) baseStart_6449390 baseEnd_6449390 := by
    simpa [prefixWord, tailWord_6449390, baseEnd_6449390] using wordTrace_append hprefix tailTrace_6449390
  have hstable : (prefixWord ++ tailWord_6449390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449390).length < 2 ^ (prefixWord ++ tailWord_6449390).sum := by decide
  have hdescent : baseEnd_6449390 < baseStart_6449390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449391 : List Nat := [1, 1, 2, 1, 6, 1, 4, 1, 2, 1, 3]
def baseStart_6449391 : Nat := 118140960795 + 6449391 * 2 ^ 59
def prefixEnd_6449391 : Nat := 4983230072969 + 3 ^ 40 * 6449391 * 2
def baseEnd_6449391 : Nat := 3311637511781281461752297

theorem tailTrace_6449391 : CollatzResearch.WordTrace tailWord_6449391 prefixEnd_6449391 3311637511781281461752297 := by
  unfold tailWord_6449391
  simp only [CollatzResearch.WordTrace]
  refine ⟨235228614577965350135540027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156819076385310233423693351 235228614577965350135540027)
  ·
    refine ⟨352842921866948025203310041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235228614577965350135540027 352842921866948025203310041)
    ·
      refine ⟨264632191400211018902482531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352842921866948025203310041 264632191400211018902482531)
      ·
        refine ⟨396948287100316528353723797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264632191400211018902482531 396948287100316528353723797)
        ·
          refine ⟨18606950957827337266580803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 396948287100316528353723797 18606950957827337266580803)
          ·
            refine ⟨27910426436741005899871205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18606950957827337266580803 27910426436741005899871205)
            ·
              refine ⟨5233204956888938606225851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27910426436741005899871205 5233204956888938606225851)
              ·
                refine ⟨7849807435333407909338777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5233204956888938606225851 7849807435333407909338777)
                ·
                  refine ⟨5887355576500055932004083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7849807435333407909338777 5887355576500055932004083)
                  ·
                    refine ⟨8831033364750083898006125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5887355576500055932004083 8831033364750083898006125)
                    ·
                      refine ⟨3311637511781281461752297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8831033364750083898006125 3311637511781281461752297)
                      ·
                        rfl

theorem cell23_6449391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 2, 1, 3].length) (baseStart_6449391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449391 prefixEnd_6449391 := by exact prefixLift 6449391
  have htrace : WordTrace (prefixWord ++ tailWord_6449391) baseStart_6449391 baseEnd_6449391 := by
    simpa [prefixWord, tailWord_6449391, baseEnd_6449391] using wordTrace_append hprefix tailTrace_6449391
  have hstable : (prefixWord ++ tailWord_6449391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449391).length < 2 ^ (prefixWord ++ tailWord_6449391).sum := by decide
  have hdescent : baseEnd_6449391 < baseStart_6449391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449431 : List Nat := [1, 1, 3, 4, 1, 2, 1, 4, 2, 2, 2]
def baseStart_6449431 : Nat := 118140960795 + 6449431 * 2 ^ 59
def prefixEnd_6449431 : Nat := 4983230072969 + 3 ^ 40 * 6449431 * 2
def baseEnd_6449431 : Nat := 3311658051007461305252113

theorem tailTrace_6449431 : CollatzResearch.WordTrace tailWord_6449431 prefixEnd_6449431 3311658051007461305252113 := by
  unfold tailWord_6449431
  simp only [CollatzResearch.WordTrace]
  refine ⟨235230073497820436966996147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156820048998546957977997431 235230073497820436966996147)
  ·
    refine ⟨352845110246730655450494221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235230073497820436966996147 352845110246730655450494221)
    ·
      refine ⟨132316916342523995793935333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352845110246730655450494221 132316916342523995793935333)
      ·
        refine ⟨24809421814223249211362875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132316916342523995793935333 24809421814223249211362875)
        ·
          refine ⟨37214132721334873817044313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24809421814223249211362875 37214132721334873817044313)
          ·
            refine ⟨27910599541001155362783235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37214132721334873817044313 27910599541001155362783235)
            ·
              refine ⟨41865899311501733044174853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27910599541001155362783235 41865899311501733044174853)
              ·
                refine ⟨7849856120906574945782785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41865899311501733044174853 7849856120906574945782785)
                ·
                  refine ⟨5887392090679931209337089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7849856120906574945782785 5887392090679931209337089)
                  ·
                    refine ⟨4415544068009948407002817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5887392090679931209337089 4415544068009948407002817)
                    ·
                      refine ⟨3311658051007461305252113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4415544068009948407002817 3311658051007461305252113)
                      ·
                        rfl

theorem cell23_6449431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_6449431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449431 prefixEnd_6449431 := by exact prefixLift 6449431
  have htrace : WordTrace (prefixWord ++ tailWord_6449431) baseStart_6449431 baseEnd_6449431 := by
    simpa [prefixWord, tailWord_6449431, baseEnd_6449431] using wordTrace_append hprefix tailTrace_6449431
  have hstable : (prefixWord ++ tailWord_6449431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449431).length < 2 ^ (prefixWord ++ tailWord_6449431).sum := by decide
  have hdescent : baseEnd_6449431 < baseStart_6449431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449507 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 3]
def baseStart_6449507 : Nat := 118140960795 + 6449507 * 2 ^ 59
def prefixEnd_6449507 : Nat := 4983230072969 + 3 ^ 40 * 6449507 * 2
def baseEnd_6449507 : Nat := 3311697075537203007901763

theorem tailTrace_6449507 : CollatzResearch.WordTrace tailWord_6449507 prefixEnd_6449507 3311697075537203007901763 := by
  unfold tailWord_6449507
  simp only [CollatzResearch.WordTrace]
  refine ⟨235232845445545101946762775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156821896963696734631175183 235232845445545101946762775)
  ·
    refine ⟨352849268168317652920144163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235232845445545101946762775 352849268168317652920144163)
    ·
      refine ⟨529273902252476479380216245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352849268168317652920144163 529273902252476479380216245)
      ·
        refine ⟨49619428336169669941895273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 529273902252476479380216245 49619428336169669941895273)
        ·
          refine ⟨37214571252127252456421455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49619428336169669941895273 37214571252127252456421455)
          ·
            refine ⟨55821856878190878684632183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37214571252127252456421455 55821856878190878684632183)
            ·
              refine ⟨83732785317286318026948275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55821856878190878684632183 83732785317286318026948275)
              ·
                refine ⟨125599177975929477040422413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83732785317286318026948275 125599177975929477040422413)
                ·
                  refine ⟨47099691740973553890158405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125599177975929477040422413 47099691740973553890158405)
                  ·
                    refine ⟨8831192201432541354404701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47099691740973553890158405 8831192201432541354404701)
                    ·
                      refine ⟨3311697075537203007901763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8831192201432541354404701 3311697075537203007901763)
                      ·
                        rfl

theorem cell23_6449507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_6449507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449507 prefixEnd_6449507 := by exact prefixLift 6449507
  have htrace : WordTrace (prefixWord ++ tailWord_6449507) baseStart_6449507 baseEnd_6449507 := by
    simpa [prefixWord, tailWord_6449507, baseEnd_6449507] using wordTrace_append hprefix tailTrace_6449507
  have hstable : (prefixWord ++ tailWord_6449507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449507).length < 2 ^ (prefixWord ++ tailWord_6449507).sum := by decide
  have hdescent : baseEnd_6449507 < baseStart_6449507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449517 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_6449517 : Nat := 118140960795 + 6449517 * 2 ^ 59
def prefixEnd_6449517 : Nat := 4983230072969 + 3 ^ 40 * 6449517 * 2
def baseEnd_6449517 : Nat := 3311702210343747968776717

theorem tailTrace_6449517 : CollatzResearch.WordTrace tailWord_6449517 prefixEnd_6449517 3311702210343747968776717 := by
  unfold tailWord_6449517
  simp only [CollatzResearch.WordTrace]
  refine ⟨235233210175508873654626805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156822140117005915769751203 235233210175508873654626805)
  ·
    refine ⟨22053113453953956905121263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235233210175508873654626805 22053113453953956905121263)
    ·
      refine ⟨33079670180930935357681895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22053113453953956905121263 33079670180930935357681895)
      ·
        refine ⟨49619505271396403036522843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33079670180930935357681895 49619505271396403036522843)
        ·
          refine ⟨74429257907094604554784265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49619505271396403036522843 74429257907094604554784265)
          ·
            refine ⟨55821943430320953416088199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74429257907094604554784265 55821943430320953416088199)
            ·
              refine ⟨83732915145481430124132299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55821943430320953416088199 83732915145481430124132299)
              ·
                refine ⟨125599372718222145186198449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83732915145481430124132299 125599372718222145186198449)
                ·
                  refine ⟨94199529538666608889648837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125599372718222145186198449 94199529538666608889648837)
                  ·
                    refine ⟨17662411788499989166809157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94199529538666608889648837 17662411788499989166809157)
                    ·
                      refine ⟨3311702210343747968776717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17662411788499989166809157 3311702210343747968776717)
                      ·
                        rfl

theorem cell23_6449517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_6449517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449517 prefixEnd_6449517 := by exact prefixLift 6449517
  have htrace : WordTrace (prefixWord ++ tailWord_6449517) baseStart_6449517 baseEnd_6449517 := by
    simpa [prefixWord, tailWord_6449517, baseEnd_6449517] using wordTrace_append hprefix tailTrace_6449517
  have hstable : (prefixWord ++ tailWord_6449517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449517).length < 2 ^ (prefixWord ++ tailWord_6449517).sum := by decide
  have hdescent : baseEnd_6449517 < baseStart_6449517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449531 : List Nat := [1, 1, 1, 1, 1, 7, 3, 3, 1, 4]
def baseStart_6449531 : Nat := 118140960795 + 6449531 * 2 ^ 59
def prefixEnd_6449531 : Nat := 4983230072969 + 3 ^ 40 * 6449531 * 2
def baseEnd_6449531 : Nat := 1103903133024303638000551

theorem tailTrace_6449531 : CollatzResearch.WordTrace tailWord_6449531 prefixEnd_6449531 1103903133024303638000551 := by
  unfold tailWord_6449531
  simp only [CollatzResearch.WordTrace]
  refine ⟨235233720797458154045636447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156822480531638769363757631 235233720797458154045636447)
  ·
    refine ⟨352850581196187231068454671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235233720797458154045636447 352850581196187231068454671)
    ·
      refine ⟨529275871794280846602682007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352850581196187231068454671 529275871794280846602682007)
      ·
        refine ⟨793913807691421269904023011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529275871794280846602682007 793913807691421269904023011)
        ·
          refine ⟨1190870711537131904856034517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793913807691421269904023011 1190870711537131904856034517)
          ·
            refine ⟨27911032301651529020063309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1190870711537131904856034517 27911032301651529020063309)
            ·
              refine ⟨10466637113119323382523741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27911032301651529020063309 10466637113119323382523741)
              ·
                refine ⟨3924988917419746268446403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10466637113119323382523741 3924988917419746268446403)
                ·
                  refine ⟨5887483376129619402669605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924988917419746268446403 5887483376129619402669605)
                  ·
                    refine ⟨1103903133024303638000551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5887483376129619402669605 1103903133024303638000551)
                    ·
                      rfl

theorem cell23_6449531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 1, 4].length) (baseStart_6449531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449531 prefixEnd_6449531 := by exact prefixLift 6449531
  have htrace : WordTrace (prefixWord ++ tailWord_6449531) baseStart_6449531 baseEnd_6449531 := by
    simpa [prefixWord, tailWord_6449531, baseEnd_6449531] using wordTrace_append hprefix tailTrace_6449531
  have hstable : (prefixWord ++ tailWord_6449531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449531).length < 2 ^ (prefixWord ++ tailWord_6449531).sum := by decide
  have hdescent : baseEnd_6449531 < baseStart_6449531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449538 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_6449538 : Nat := 118140960795 + 6449538 * 2 ^ 59
def prefixEnd_6449538 : Nat := 4983230072969 + 3 ^ 40 * 6449538 * 2
def baseEnd_6449538 : Nat := 3311712993437492386614121

theorem tailTrace_6449538 : CollatzResearch.WordTrace tailWord_6449538 prefixEnd_6449538 3311712993437492386614121 := by
  unfold tailWord_6449538
  simp only [CollatzResearch.WordTrace]
  refine ⟨58808494027108198560285317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156822650738955196160760845 58808494027108198560285317)
  ·
    refine ⟨11026592630082787230053497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58808494027108198560285317 11026592630082787230053497)
    ·
      refine ⟨8269944472562090422540123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11026592630082787230053497 8269944472562090422540123)
      ·
        refine ⟨12404916708843135633810185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8269944472562090422540123 12404916708843135633810185)
        ·
          refine ⟨9303687531632351725357639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12404916708843135633810185 9303687531632351725357639)
          ·
            refine ⟨13955531297448527588036459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9303687531632351725357639 13955531297448527588036459)
            ·
              refine ⟨20933296946172791382054689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13955531297448527588036459 20933296946172791382054689)
              ·
                refine ⟨15699972709629593536541017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20933296946172791382054689 15699972709629593536541017)
                ·
                  refine ⟨11774979532222195152405763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15699972709629593536541017 11774979532222195152405763)
                  ·
                    refine ⟨17662469298333292728608645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11774979532222195152405763 17662469298333292728608645)
                    ·
                      refine ⟨3311712993437492386614121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17662469298333292728608645 3311712993437492386614121)
                      ·
                        rfl

theorem cell23_6449538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_6449538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449538 prefixEnd_6449538 := by exact prefixLift 6449538
  have htrace : WordTrace (prefixWord ++ tailWord_6449538) baseStart_6449538 baseEnd_6449538 := by
    simpa [prefixWord, tailWord_6449538, baseEnd_6449538] using wordTrace_append hprefix tailTrace_6449538
  have hstable : (prefixWord ++ tailWord_6449538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449538).length < 2 ^ (prefixWord ++ tailWord_6449538).sum := by decide
  have hdescent : baseEnd_6449538 < baseStart_6449538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449548 : List Nat := [2, 2, 1, 2, 1, 5, 3, 2, 1, 4]
def baseStart_6449548 : Nat := 118140960795 + 6449548 * 2 ^ 59
def prefixEnd_6449548 : Nat := 4983230072969 + 3 ^ 40 * 6449548 * 2
def baseEnd_6449548 : Nat := 1103906042748012449163025

theorem tailTrace_6449548 : CollatzResearch.WordTrace tailWord_6449548 prefixEnd_6449548 1103906042748012449163025 := by
  unfold tailWord_6449548
  simp only [CollatzResearch.WordTrace]
  refine ⟨117617170419198282974502649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156822893892264377299336865 117617170419198282974502649)
  ·
    refine ⟨88212877814398712230876987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117617170419198282974502649 88212877814398712230876987)
    ·
      refine ⟨132319316721598068346315481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88212877814398712230876987 132319316721598068346315481)
      ·
        refine ⟨99239487541198551259736611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132319316721598068346315481 99239487541198551259736611)
        ·
          refine ⟨148859231311797826889604917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99239487541198551259736611 148859231311797826889604917)
          ·
            refine ⟨13955552935481046270900461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148859231311797826889604917 13955552935481046270900461)
            ·
              refine ⟨5233332350805392351587673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13955552935481046270900461 5233332350805392351587673)
              ·
                refine ⟨3924999263104044263690755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5233332350805392351587673 3924999263104044263690755)
                ·
                  refine ⟨5887498894656066395536133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924999263104044263690755 5887498894656066395536133)
                  ·
                    refine ⟨1103906042748012449163025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5887498894656066395536133 1103906042748012449163025)
                    ·
                      rfl

theorem cell23_6449548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_6449548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449548 prefixEnd_6449548 := by exact prefixLift 6449548
  have htrace : WordTrace (prefixWord ++ tailWord_6449548) baseStart_6449548 baseEnd_6449548 := by
    simpa [prefixWord, tailWord_6449548, baseEnd_6449548] using wordTrace_append hprefix tailTrace_6449548
  have hstable : (prefixWord ++ tailWord_6449548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449548).length < 2 ^ (prefixWord ++ tailWord_6449548).sum := by decide
  have hdescent : baseEnd_6449548 < baseStart_6449548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449557 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 3, 5]
def baseStart_6449557 : Nat := 118140960795 + 6449557 * 2 ^ 59
def prefixEnd_6449557 : Nat := 4983230072969 + 3 ^ 40 * 6449557 * 2
def baseEnd_6449557 : Nat := 1103907583189975937425511

theorem tailTrace_6449557 : CollatzResearch.WordTrace tailWord_6449557 prefixEnd_6449557 1103907583189975937425511 := by
  unfold tailWord_6449557
  simp only [CollatzResearch.WordTrace]
  refine ⟨235234669095363960486082925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156823112730242640324055283 235234669095363960486082925)
  ·
    refine ⟨88213000910761485182281097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235234669095363960486082925 88213000910761485182281097)
    ·
      refine ⟨66159750683071113886710823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88213000910761485182281097 66159750683071113886710823)
      ·
        refine ⟨99239626024606670830066235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66159750683071113886710823 99239626024606670830066235)
        ·
          refine ⟨148859439036910006245099353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99239626024606670830066235 148859439036910006245099353)
          ·
            refine ⟨111644579277682504683824515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148859439036910006245099353 111644579277682504683824515)
            ·
              refine ⟨167466868916523757025736773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111644579277682504683824515 167466868916523757025736773)
              ·
                refine ⟨31400037921848204442325645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167466868916523757025736773 31400037921848204442325645)
                ·
                  refine ⟨11775014220693076665872117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31400037921848204442325645 11775014220693076665872117)
                  ·
                    refine ⟨1103907583189975937425511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11775014220693076665872117 1103907583189975937425511)
                    ·
                      rfl

theorem cell23_6449557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_6449557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449557 prefixEnd_6449557 := by exact prefixLift 6449557
  have htrace : WordTrace (prefixWord ++ tailWord_6449557) baseStart_6449557 baseEnd_6449557 := by
    simpa [prefixWord, tailWord_6449557, baseEnd_6449557] using wordTrace_append hprefix tailTrace_6449557
  have hstable : (prefixWord ++ tailWord_6449557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449557).length < 2 ^ (prefixWord ++ tailWord_6449557).sum := by decide
  have hdescent : baseEnd_6449557 < baseStart_6449557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449591 : List Nat := [1, 1, 3, 1, 3, 4, 3, 1, 1, 5]
def baseStart_6449591 : Nat := 118140960795 + 6449591 * 2 ^ 59
def prefixEnd_6449591 : Nat := 4983230072969 + 3 ^ 40 * 6449591 * 2
def baseEnd_6449591 : Nat := 1103913402637393559750459

theorem tailTrace_6449591 : CollatzResearch.WordTrace tailWord_6449591 prefixEnd_6449591 1103913402637393559750459 := by
  unfold tailWord_6449591
  simp only [CollatzResearch.WordTrace]
  refine ⟨235235909177240784292820627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156823939451493856195213751 235235909177240784292820627)
  ·
    refine ⟨352853863765861176439230941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235235909177240784292820627 352853863765861176439230941)
    ·
      refine ⟨132320198912197941164711603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352853863765861176439230941 132320198912197941164711603)
      ·
        refine ⟨198480298368296911747067405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132320198912197941164711603 198480298368296911747067405)
        ·
          refine ⟨74430111888111341905150277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198480298368296911747067405 74430111888111341905150277)
          ·
            refine ⟨13955645979020876607215677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74430111888111341905150277 13955645979020876607215677)
            ·
              refine ⟨5233367242132828727705879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13955645979020876607215677 5233367242132828727705879)
              ·
                refine ⟨7850050863199243091558819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5233367242132828727705879 7850050863199243091558819)
                ·
                  refine ⟨11775076294798864637338229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7850050863199243091558819 11775076294798864637338229)
                  ·
                    refine ⟨1103913402637393559750459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11775076294798864637338229 1103913402637393559750459)
                    ·
                      rfl

theorem cell23_6449591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_6449591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449591 prefixEnd_6449591 := by exact prefixLift 6449591
  have htrace : WordTrace (prefixWord ++ tailWord_6449591) baseStart_6449591 baseEnd_6449591 := by
    simpa [prefixWord, tailWord_6449591, baseEnd_6449591] using wordTrace_append hprefix tailTrace_6449591
  have hstable : (prefixWord ++ tailWord_6449591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449591).length < 2 ^ (prefixWord ++ tailWord_6449591).sum := by decide
  have hdescent : baseEnd_6449591 < baseStart_6449591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449594 : List Nat := [3, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4]
def baseStart_6449594 : Nat := 118140960795 + 6449594 * 2 ^ 59
def prefixEnd_6449594 : Nat := 4983230072969 + 3 ^ 40 * 6449594 * 2
def baseEnd_6449594 : Nat := 3311741748354144167513863

theorem tailTrace_6449594 : CollatzResearch.WordTrace tailWord_6449594 prefixEnd_6449594 3311741748354144167513863 := by
  unfold tailWord_6449594
  simp only [CollatzResearch.WordTrace]
  refine ⟨58809004649057478951294959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156824012397486610536786557 58809004649057478951294959)
  ·
    refine ⟨88213506973586218426942439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58809004649057478951294959 88213506973586218426942439)
    ·
      refine ⟨132320260460379327640413659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88213506973586218426942439 132320260460379327640413659)
      ·
        refine ⟨198480390690568991460620489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132320260460379327640413659 198480390690568991460620489)
        ·
          refine ⟨148860293017926743595465367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198480390690568991460620489 148860293017926743595465367)
          ·
            refine ⟨223290439526890115393198051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148860293017926743595465367 223290439526890115393198051)
            ·
              refine ⟨334935659290335173089797077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223290439526890115393198051 334935659290335173089797077)
              ·
                refine ⟨7850054514617230619292119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 334935659290335173089797077 7850054514617230619292119)
                ·
                  refine ⟨11775081771925845928938179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7850054514617230619292119 11775081771925845928938179)
                  ·
                    refine ⟨17662622657888768893407269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11775081771925845928938179 17662622657888768893407269)
                    ·
                      refine ⟨3311741748354144167513863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17662622657888768893407269 3311741748354144167513863)
                      ·
                        rfl

theorem cell23_6449594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_6449594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449594 prefixEnd_6449594 := by exact prefixLift 6449594
  have htrace : WordTrace (prefixWord ++ tailWord_6449594) baseStart_6449594 baseEnd_6449594 := by
    simpa [prefixWord, tailWord_6449594, baseEnd_6449594] using wordTrace_append hprefix tailTrace_6449594
  have hstable : (prefixWord ++ tailWord_6449594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449594).length < 2 ^ (prefixWord ++ tailWord_6449594).sum := by decide
  have hdescent : baseEnd_6449594 < baseStart_6449594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449611 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 3, 2, 2]
def baseStart_6449611 : Nat := 118140960795 + 6449611 * 2 ^ 59
def prefixEnd_6449611 : Nat := 4983230072969 + 3 ^ 40 * 6449611 * 2
def baseEnd_6449611 : Nat := 3311750477525270601001285

theorem tailTrace_6449611 : CollatzResearch.WordTrace tailWord_6449611 prefixEnd_6449611 3311750477525270601001285 := by
  unfold tailWord_6449611
  simp only [CollatzResearch.WordTrace]
  refine ⟨235236638637168327708548687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156824425758112218472365791 235236638637168327708548687)
  ·
    refine ⟨352854957955752491562823031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235236638637168327708548687 352854957955752491562823031)
    ·
      refine ⟨529282436933628737344234547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352854957955752491562823031 529282436933628737344234547)
      ·
        refine ⟨793923655400443106016351821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529282436933628737344234547 793923655400443106016351821)
        ·
          refine ⟨297721370775166164756131933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 793923655400443106016351821 297721370775166164756131933)
          ·
            refine ⟨111645514040687311783549475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297721370775166164756131933 111645514040687311783549475)
            ·
              refine ⟨167468271061030967675324213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111645514040687311783549475 167468271061030967675324213)
              ·
                refine ⟨15700150411971653219561645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167468271061030967675324213 15700150411971653219561645)
                ·
                  refine ⟨5887556404489369957335617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15700150411971653219561645 5887556404489369957335617)
                  ·
                    refine ⟨4415667303367027468001713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5887556404489369957335617 4415667303367027468001713)
                    ·
                      refine ⟨3311750477525270601001285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4415667303367027468001713 3311750477525270601001285)
                      ·
                        rfl

theorem cell23_6449611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 2, 2].length) (baseStart_6449611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449611 prefixEnd_6449611 := by exact prefixLift 6449611
  have htrace : WordTrace (prefixWord ++ tailWord_6449611) baseStart_6449611 baseEnd_6449611 := by
    simpa [prefixWord, tailWord_6449611, baseEnd_6449611] using wordTrace_append hprefix tailTrace_6449611
  have hstable : (prefixWord ++ tailWord_6449611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449611).length < 2 ^ (prefixWord ++ tailWord_6449611).sum := by decide
  have hdescent : baseEnd_6449611 < baseStart_6449611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449621 : List Nat := [1, 3, 2, 3, 1, 2, 2, 3, 2, 4]
def baseStart_6449621 : Nat := 118140960795 + 6449621 * 2 ^ 59
def prefixEnd_6449621 : Nat := 4983230072969 + 3 ^ 40 * 6449621 * 2
def baseEnd_6449621 : Nat := 1103918537443938520625413

theorem tailTrace_6449621 : CollatzResearch.WordTrace tailWord_6449621 prefixEnd_6449621 1103918537443938520625413 := by
  unfold tailWord_6449621
  simp only [CollatzResearch.WordTrace]
  refine ⟨235237003367132099416412717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156824668911421399610941811 235237003367132099416412717)
  ·
    refine ⟨88213876262674537281154769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235237003367132099416412717 88213876262674537281154769)
    ·
      refine ⟨66160407197005902960866077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88213876262674537281154769 66160407197005902960866077)
      ·
        refine ⟨24810152698877213610324779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66160407197005902960866077 24810152698877213610324779)
        ·
          refine ⟨37215229048315820415487169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24810152698877213610324779 37215229048315820415487169)
          ·
            refine ⟨27911421786236865311615377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37215229048315820415487169 27911421786236865311615377)
            ·
              refine ⟨20933566339677648983711533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27911421786236865311615377 20933566339677648983711533)
              ·
                refine ⟨7850087377379118368891825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20933566339677648983711533 7850087377379118368891825)
                ·
                  refine ⟨5887565533034338776668869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7850087377379118368891825 5887565533034338776668869)
                  ·
                    refine ⟨1103918537443938520625413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5887565533034338776668869 1103918537443938520625413)
                    ·
                      rfl

theorem cell23_6449621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_6449621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449621 prefixEnd_6449621 := by exact prefixLift 6449621
  have htrace : WordTrace (prefixWord ++ tailWord_6449621) baseStart_6449621 baseEnd_6449621 := by
    simpa [prefixWord, tailWord_6449621, baseEnd_6449621] using wordTrace_append hprefix tailTrace_6449621
  have hstable : (prefixWord ++ tailWord_6449621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449621).length < 2 ^ (prefixWord ++ tailWord_6449621).sum := by decide
  have hdescent : baseEnd_6449621 < baseStart_6449621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449644 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 3]
def baseStart_6449644 : Nat := 118140960795 + 6449644 * 2 ^ 59
def prefixEnd_6449644 : Nat := 4983230072969 + 3 ^ 40 * 6449644 * 2
def baseEnd_6449644 : Nat := 3311767422386868971888633

theorem tailTrace_6449644 : CollatzResearch.WordTrace tailWord_6449644 prefixEnd_6449644 3311767422386868971888633 := by
  unfold tailWord_6449644
  simp only [CollatzResearch.WordTrace]
  refine ⟨117618921123024387172249993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156825228164032516229666657 117618921123024387172249993)
  ·
    refine ⟨88214190842268290379187495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117618921123024387172249993 88214190842268290379187495)
    ·
      refine ⟨132321286263402435568781243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88214190842268290379187495 132321286263402435568781243)
      ·
        refine ⟨198481929395103653353171865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132321286263402435568781243 198481929395103653353171865)
        ·
          refine ⟨148861447046327740014878899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198481929395103653353171865 148861447046327740014878899)
          ·
            refine ⟨223292170569491610022318349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148861447046327740014878899 223292170569491610022318349)
            ·
              refine ⟨83734563963559353758369381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223292170569491610022318349 83734563963559353758369381)
              ·
                refine ⟨15700230743167378829694259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83734563963559353758369381 15700230743167378829694259)
                ·
                  refine ⟨23550346114751068244541389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15700230743167378829694259 23550346114751068244541389)
                  ·
                    refine ⟨8831379793031650591703021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23550346114751068244541389 8831379793031650591703021)
                    ·
                      refine ⟨3311767422386868971888633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8831379793031650591703021 3311767422386868971888633)
                      ·
                        rfl

theorem cell23_6449644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_6449644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449644 prefixEnd_6449644 := by exact prefixLift 6449644
  have htrace : WordTrace (prefixWord ++ tailWord_6449644) baseStart_6449644 baseEnd_6449644 := by
    simpa [prefixWord, tailWord_6449644, baseEnd_6449644] using wordTrace_append hprefix tailTrace_6449644
  have hstable : (prefixWord ++ tailWord_6449644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449644).length < 2 ^ (prefixWord ++ tailWord_6449644).sum := by decide
  have hdescent : baseEnd_6449644 < baseStart_6449644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449645 : List Nat := [1, 5, 1, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_6449645 : Nat := 118140960795 + 6449645 * 2 ^ 59
def prefixEnd_6449645 : Nat := 4983230072969 + 3 ^ 40 * 6449645 * 2
def baseEnd_6449645 : Nat := 3311767935867523467976129

theorem tailTrace_6449645 : CollatzResearch.WordTrace tailWord_6449645 prefixEnd_6449645 3311767935867523467976129 := by
  unfold tailWord_6449645
  simp only [CollatzResearch.WordTrace]
  refine ⟨235237878719045151515286389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156825252479363434343524259 235237878719045151515286389)
  ·
    refine ⟨22053551129910482954558099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235237878719045151515286389 22053551129910482954558099)
    ·
      refine ⟨33080326694865724431837149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22053551129910482954558099 33080326694865724431837149)
      ·
        refine ⟨12405122510574646661938931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33080326694865724431837149 12405122510574646661938931)
        ·
          refine ⟨18607683765861969992908397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12405122510574646661938931 18607683765861969992908397)
          ·
            refine ⟨6977881412198238747340649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18607683765861969992908397 6977881412198238747340649)
            ·
              refine ⟨5233411059148679060505487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6977881412198238747340649 5233411059148679060505487)
              ·
                refine ⟨7850116588723018590758231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5233411059148679060505487 7850116588723018590758231)
                ·
                  refine ⟨11775174883084527886137347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7850116588723018590758231 11775174883084527886137347)
                  ·
                    refine ⟨17662762324626791829206021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11775174883084527886137347 17662762324626791829206021)
                    ·
                      refine ⟨3311767935867523467976129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17662762324626791829206021 3311767935867523467976129)
                      ·
                        rfl

theorem cell23_6449645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_6449645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449645 prefixEnd_6449645 := by exact prefixLift 6449645
  have htrace : WordTrace (prefixWord ++ tailWord_6449645) baseStart_6449645 baseEnd_6449645 := by
    simpa [prefixWord, tailWord_6449645, baseEnd_6449645] using wordTrace_append hprefix tailTrace_6449645
  have hstable : (prefixWord ++ tailWord_6449645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449645).length < 2 ^ (prefixWord ++ tailWord_6449645).sum := by decide
  have hdescent : baseEnd_6449645 < baseStart_6449645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449661 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 4, 1, 3]
def baseStart_6449661 : Nat := 118140960795 + 6449661 * 2 ^ 59
def prefixEnd_6449661 : Nat := 4983230072969 + 3 ^ 40 * 6449661 * 2
def baseEnd_6449661 : Nat := 3311776151557995405376055

theorem tailTrace_6449661 : CollatzResearch.WordTrace tailWord_6449661 prefixEnd_6449661 3311776151557995405376055 := by
  unfold tailWord_6449661
  simp only [CollatzResearch.WordTrace]
  refine ⟨235238462286987186247868837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156825641524658124165245891 235238462286987186247868837)
  ·
    refine ⟨44107211678810097421475407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235238462286987186247868837 44107211678810097421475407)
    ·
      refine ⟨66160817518215146132213111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44107211678810097421475407 66160817518215146132213111)
      ·
        refine ⟨99241226277322719198319667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66160817518215146132213111 99241226277322719198319667)
        ·
          refine ⟨148861839415984078797479501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99241226277322719198319667 148861839415984078797479501)
          ·
            refine ⟨55823189780994029549054813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148861839415984078797479501 55823189780994029549054813)
            ·
              refine ⟨20933696167872761080895555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55823189780994029549054813 20933696167872761080895555)
              ·
                refine ⟨31400544251809141621343333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20933696167872761080895555 31400544251809141621343333)
                ·
                  refine ⟨5887602047214214054001875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31400544251809141621343333 5887602047214214054001875)
                  ·
                    refine ⟨8831403070821321081002813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5887602047214214054001875 8831403070821321081002813)
                    ·
                      refine ⟨3311776151557995405376055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8831403070821321081002813 3311776151557995405376055)
                      ·
                        rfl

theorem cell23_6449661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_6449661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449661 prefixEnd_6449661 := by exact prefixLift 6449661
  have htrace : WordTrace (prefixWord ++ tailWord_6449661) baseStart_6449661 baseEnd_6449661 := by
    simpa [prefixWord, tailWord_6449661, baseEnd_6449661] using wordTrace_append hprefix tailTrace_6449661
  have hstable : (prefixWord ++ tailWord_6449661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449661).length < 2 ^ (prefixWord ++ tailWord_6449661).sum := by decide
  have hdescent : baseEnd_6449661 < baseStart_6449661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449678 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3]
def baseStart_6449678 : Nat := 118140960795 + 6449678 * 2 ^ 59
def prefixEnd_6449678 : Nat := 4983230072969 + 3 ^ 40 * 6449678 * 2
def baseEnd_6449678 : Nat := 3311784880729121838863477

theorem tailTrace_6449678 : CollatzResearch.WordTrace tailWord_6449678 prefixEnd_6449678 3311784880729121838863477 := by
  unfold tailWord_6449678
  simp only [CollatzResearch.WordTrace]
  refine ⟨29404885290990699768904711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156826054885283732100825125 29404885290990699768904711)
  ·
    refine ⟨44107327936486049653357067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29404885290990699768904711 44107327936486049653357067)
    ·
      refine ⟨66160991904729074480035601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44107327936486049653357067 66160991904729074480035601)
      ·
        refine ⟨49620743928546805860026701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66160991904729074480035601 49620743928546805860026701)
        ·
          refine ⟨18607778973205052197510013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49620743928546805860026701 18607778973205052197510013)
          ·
            refine ⟨6977917114951894574066255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18607778973205052197510013 6977917114951894574066255)
            ·
              refine ⟨10466875672427841861099383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6977917114951894574066255 10466875672427841861099383)
              ·
                refine ⟨15700313508641762791649075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10466875672427841861099383 15700313508641762791649075)
                ·
                  refine ⟨23550470262962644187473613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15700313508641762791649075 23550470262962644187473613)
                  ·
                    refine ⟨8831426348610991570302605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23550470262962644187473613 8831426348610991570302605)
                    ·
                      refine ⟨3311784880729121838863477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8831426348610991570302605 3311784880729121838863477)
                      ·
                        rfl

theorem cell23_6449678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_6449678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449678 prefixEnd_6449678 := by exact prefixLift 6449678
  have htrace : WordTrace (prefixWord ++ tailWord_6449678) baseStart_6449678 baseEnd_6449678 := by
    simpa [prefixWord, tailWord_6449678, baseEnd_6449678] using wordTrace_append hprefix tailTrace_6449678
  have hstable : (prefixWord ++ tailWord_6449678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449678).length < 2 ^ (prefixWord ++ tailWord_6449678).sum := by decide
  have hdescent : baseEnd_6449678 < baseStart_6449678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449688 : List Nat := [2, 1, 2, 3, 3, 1, 1, 4, 1, 3, 2]
def baseStart_6449688 : Nat := 118140960795 + 6449688 * 2 ^ 59
def prefixEnd_6449688 : Nat := 4983230072969 + 3 ^ 40 * 6449688 * 2
def baseEnd_6449688 : Nat := 3311790015535666799738431

theorem tailTrace_6449688 : CollatzResearch.WordTrace tailWord_6449688 prefixEnd_6449688 3311790015535666799738431 := by
  unfold tailWord_6449688
  simp only [CollatzResearch.WordTrace]
  refine ⟨117619723528944684929550859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156826298038592913239401145 117619723528944684929550859)
  ·
    refine ⟨176429585293417027394326289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117619723528944684929550859 176429585293417027394326289)
    ·
      refine ⟨132322188970062770545744717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176429585293417027394326289 132322188970062770545744717)
      ·
        refine ⟨49620820863773538954654269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132322188970062770545744717 49620820863773538954654269)
        ·
          refine ⟨18607807823915077107995351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49620820863773538954654269 18607807823915077107995351)
          ·
            refine ⟨27911711735872615661993027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18607807823915077107995351 27911711735872615661993027)
            ·
              refine ⟨41867567603808923492989541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27911711735872615661993027 41867567603808923492989541)
              ·
                refine ⟨7850168925714173154935539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41867567603808923492989541 7850168925714173154935539)
                ·
                  refine ⟨11775253388571259732403309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7850168925714173154935539 11775253388571259732403309)
                  ·
                    refine ⟨4415720020714222399651241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11775253388571259732403309 4415720020714222399651241)
                    ·
                      refine ⟨3311790015535666799738431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4415720020714222399651241 3311790015535666799738431)
                      ·
                        rfl

theorem cell23_6449688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_6449688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449688 prefixEnd_6449688 := by exact prefixLift 6449688
  have htrace : WordTrace (prefixWord ++ tailWord_6449688) baseStart_6449688 baseEnd_6449688 := by
    simpa [prefixWord, tailWord_6449688, baseEnd_6449688] using wordTrace_append hprefix tailTrace_6449688
  have hstable : (prefixWord ++ tailWord_6449688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449688).length < 2 ^ (prefixWord ++ tailWord_6449688).sum := by decide
  have hdescent : baseEnd_6449688 < baseStart_6449688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449701 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 1, 4, 2]
def baseStart_6449701 : Nat := 118140960795 + 6449701 * 2 ^ 59
def prefixEnd_6449701 : Nat := 4983230072969 + 3 ^ 40 * 6449701 * 2
def baseEnd_6449701 : Nat := 3311796690784175248875871

theorem tailTrace_6449701 : CollatzResearch.WordTrace tailWord_6449701 prefixEnd_6449701 3311796690784175248875871 := by
  unfold tailWord_6449701
  simp only [CollatzResearch.WordTrace]
  refine ⟨235239921206842273079324957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156826614137894848719549971 235239921206842273079324957)
  ·
    refine ⟨88214970452565852404746859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235239921206842273079324957 88214970452565852404746859)
    ·
      refine ⟨132322455678848778607120289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88214970452565852404746859 132322455678848778607120289)
      ·
        refine ⟨99241841759136583955340217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132322455678848778607120289 99241841759136583955340217)
        ·
          refine ⟨74431381319352437966505163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99241841759136583955340217 74431381319352437966505163)
          ·
            refine ⟨111647071979028656949757745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74431381319352437966505163 111647071979028656949757745)
            ·
              refine ⟨83735303984271492712318309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111647071979028656949757745 83735303984271492712318309)
              ·
                refine ⟨15700369497050904883559683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83735303984271492712318309 15700369497050904883559683)
                ·
                  refine ⟨23550554245576357325339525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15700369497050904883559683 23550554245576357325339525)
                  ·
                    refine ⟨4415728921045566998501161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23550554245576357325339525 4415728921045566998501161)
                    ·
                      refine ⟨3311796690784175248875871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4415728921045566998501161 3311796690784175248875871)
                      ·
                        rfl

theorem cell23_6449701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_6449701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449701 prefixEnd_6449701 := by exact prefixLift 6449701
  have htrace : WordTrace (prefixWord ++ tailWord_6449701) baseStart_6449701 baseEnd_6449701 := by
    simpa [prefixWord, tailWord_6449701, baseEnd_6449701] using wordTrace_append hprefix tailTrace_6449701
  have hstable : (prefixWord ++ tailWord_6449701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449701).length < 2 ^ (prefixWord ++ tailWord_6449701).sum := by decide
  have hdescent : baseEnd_6449701 < baseStart_6449701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449707 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 9]
def baseStart_6449707 : Nat := 118140960795 + 6449707 * 2 ^ 59
def prefixEnd_6449707 : Nat := 4983230072969 + 3 ^ 40 * 6449707 * 2
def baseEnd_6449707 : Nat := 367977752407566913933427

theorem tailTrace_6449707 : CollatzResearch.WordTrace tailWord_6449707 prefixEnd_6449707 367977752407566913933427 := by
  unfold tailWord_6449707
  simp only [CollatzResearch.WordTrace]
  refine ⟨235240140044820536104043375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156826760029880357402695583 235240140044820536104043375)
  ·
    refine ⟨352860210067230804156065063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235240140044820536104043375 352860210067230804156065063)
    ·
      refine ⟨529290315100846206234097595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352860210067230804156065063 529290315100846206234097595)
      ·
        refine ⟨793935472651269309351146393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529290315100846206234097595 793935472651269309351146393)
        ·
          refine ⟨595451604488451982013359795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793935472651269309351146393 595451604488451982013359795)
          ·
            refine ⟨893177406732677973020039693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595451604488451982013359795 893177406732677973020039693)
            ·
              refine ⟨334941527524754239882514885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 893177406732677973020039693 334941527524754239882514885)
              ·
                refine ⟨62801536410891419977971541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334941527524754239882514885 62801536410891419977971541)
                ·
                  refine ⟨367977752407566913933427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62801536410891419977971541 367977752407566913933427)
                  ·
                    rfl

theorem cell23_6449707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 9].length) (baseStart_6449707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449707 prefixEnd_6449707 := by exact prefixLift 6449707
  have htrace : WordTrace (prefixWord ++ tailWord_6449707) baseStart_6449707 baseEnd_6449707 := by
    simpa [prefixWord, tailWord_6449707, baseEnd_6449707] using wordTrace_append hprefix tailTrace_6449707
  have hstable : (prefixWord ++ tailWord_6449707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449707).length < 2 ^ (prefixWord ++ tailWord_6449707).sum := by decide
  have hdescent : baseEnd_6449707 < baseStart_6449707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449714 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_6449714 : Nat := 118140960795 + 6449714 * 2 ^ 59
def prefixEnd_6449714 : Nat := 4983230072969 + 3 ^ 40 * 6449714 * 2
def baseEnd_6449714 : Nat := 3311803366032683698013311

theorem tailTrace_6449714 : CollatzResearch.WordTrace tailWord_6449714 prefixEnd_6449714 3311803366032683698013311 := by
  unfold tailWord_6449714
  simp only [CollatzResearch.WordTrace]
  refine ⟨58810098838948794074887049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156826930237196784199698797 58810098838948794074887049)
  ·
    refine ⟨44107574129211595556165287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58810098838948794074887049 44107574129211595556165287)
    ·
      refine ⟨66161361193817393334247931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44107574129211595556165287 66161361193817393334247931)
      ·
        refine ⟨99242041790726090001371897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66161361193817393334247931 99242041790726090001371897)
        ·
          refine ⟨74431531343044567501028923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99242041790726090001371897 74431531343044567501028923)
          ·
            refine ⟨111647297014566851251543385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74431531343044567501028923 111647297014566851251543385)
            ·
              refine ⟨83735472760925138438657539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111647297014566851251543385 83735472760925138438657539)
              ·
                refine ⟨125603209141387707657986309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83735472760925138438657539 125603209141387707657986309)
                ·
                  refine ⟨23550601714010195185872433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125603209141387707657986309 23550601714010195185872433)
                  ·
                    refine ⟨17662951285507646389404325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23550601714010195185872433 17662951285507646389404325)
                    ·
                      refine ⟨3311803366032683698013311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17662951285507646389404325 3311803366032683698013311)
                      ·
                        rfl

theorem cell23_6449714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_6449714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449714 prefixEnd_6449714 := by exact prefixLift 6449714
  have htrace : WordTrace (prefixWord ++ tailWord_6449714) baseStart_6449714 baseEnd_6449714 := by
    simpa [prefixWord, tailWord_6449714, baseEnd_6449714] using wordTrace_append hprefix tailTrace_6449714
  have hstable : (prefixWord ++ tailWord_6449714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449714).length < 2 ^ (prefixWord ++ tailWord_6449714).sum := by decide
  have hdescent : baseEnd_6449714 < baseStart_6449714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449735 : List Nat := [1, 1, 4, 1, 4, 2, 1, 3, 2, 2, 2]
def baseStart_6449735 : Nat := 118140960795 + 6449735 * 2 ^ 59
def prefixEnd_6449735 : Nat := 4983230072969 + 3 ^ 40 * 6449735 * 2
def baseEnd_6449735 : Nat := 3311814149126428115850715

theorem tailTrace_6449735 : CollatzResearch.WordTrace tailWord_6449735 prefixEnd_6449735 3311814149126428115850715 := by
  unfold tailWord_6449735
  simp only [CollatzResearch.WordTrace]
  refine ⟨235241161288719096886062659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156827440859146064590708439 235241161288719096886062659)
  ·
    refine ⟨352861741933078645329093989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235241161288719096886062659 352861741933078645329093989)
    ·
      refine ⟨66161576612452245999205123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 352861741933078645329093989 66161576612452245999205123)
      ·
        refine ⟨99242364918678368998807685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66161576612452245999205123 99242364918678368998807685)
        ·
          refine ⟨18607943422252194187276441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99242364918678368998807685 18607943422252194187276441)
          ·
            refine ⟨13955957566689145640457331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18607943422252194187276441 13955957566689145640457331)
            ·
              refine ⟨20933936350033718460685997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13955957566689145640457331 20933936350033718460685997)
              ·
                refine ⟨7850226131262644422757249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20933936350033718460685997 7850226131262644422757249)
                ·
                  refine ⟨5887669598446983317067937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7850226131262644422757249 5887669598446983317067937)
                  ·
                    refine ⟨4415752198835237487800953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5887669598446983317067937 4415752198835237487800953)
                    ·
                      refine ⟨3311814149126428115850715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4415752198835237487800953 3311814149126428115850715)
                      ·
                        rfl

theorem cell23_6449735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_6449735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449735 prefixEnd_6449735 := by exact prefixLift 6449735
  have htrace : WordTrace (prefixWord ++ tailWord_6449735) baseStart_6449735 baseEnd_6449735 := by
    simpa [prefixWord, tailWord_6449735, baseEnd_6449735] using wordTrace_append hprefix tailTrace_6449735
  have hstable : (prefixWord ++ tailWord_6449735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449735).length < 2 ^ (prefixWord ++ tailWord_6449735).sum := by decide
  have hdescent : baseEnd_6449735 < baseStart_6449735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449764 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_6449764 : Nat := 118140960795 + 6449764 * 2 ^ 59
def prefixEnd_6449764 : Nat := 4983230072969 + 3 ^ 40 * 6449764 * 2
def baseEnd_6449764 : Nat := 3311829040065408502388081

theorem tailTrace_6449764 : CollatzResearch.WordTrace tailWord_6449764 prefixEnd_6449764 3311829040065408502388081 := by
  unfold tailWord_6449764
  simp only [CollatzResearch.WordTrace]
  refine ⟨117621109502807017419434173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156828146003742689892578897 117621109502807017419434173)
  ·
    refine ⟨44107916063552631532287815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117621109502807017419434173 44107916063552631532287815)
    ·
      refine ⟨66161874095328947298431723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44107916063552631532287815 66161874095328947298431723)
      ·
        refine ⟨99242811142993420947647585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66161874095328947298431723 99242811142993420947647585)
        ·
          refine ⟨74432108357245065710735689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99242811142993420947647585 74432108357245065710735689)
          ·
            refine ⟨55824081267933799283051767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74432108357245065710735689 55824081267933799283051767)
            ·
              refine ⟨83736121901900698924577651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55824081267933799283051767 83736121901900698924577651)
              ·
                refine ⟨125604182852851048386866477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83736121901900698924577651 125604182852851048386866477)
                ·
                  refine ⟨47101568569819143145074929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125604182852851048386866477 47101568569819143145074929)
                  ·
                    refine ⟨35326176427364357358806197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47101568569819143145074929 35326176427364357358806197)
                    ·
                      refine ⟨3311829040065408502388081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35326176427364357358806197 3311829040065408502388081)
                      ·
                        rfl

theorem cell23_6449764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_6449764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449764 prefixEnd_6449764 := by exact prefixLift 6449764
  have htrace : WordTrace (prefixWord ++ tailWord_6449764) baseStart_6449764 baseEnd_6449764 := by
    simpa [prefixWord, tailWord_6449764, baseEnd_6449764] using wordTrace_append hprefix tailTrace_6449764
  have hstable : (prefixWord ++ tailWord_6449764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449764).length < 2 ^ (prefixWord ++ tailWord_6449764).sum := by decide
  have hdescent : baseEnd_6449764 < baseStart_6449764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449804 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_6449804 : Nat := 118140960795 + 6449804 * 2 ^ 59
def prefixEnd_6449804 : Nat := 4983230072969 + 3 ^ 40 * 6449804 * 2
def baseEnd_6449804 : Nat := 3311849579291588345887897

theorem tailTrace_6449804 : CollatzResearch.WordTrace tailWord_6449804 prefixEnd_6449804 3311849579291588345887897 := by
  unfold tailWord_6449804
  simp only [CollatzResearch.WordTrace]
  refine ⟨117621838962734560835162233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156829118616979414446882977 117621838962734560835162233)
  ·
    refine ⟨88216379222050920626371675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117621838962734560835162233 88216379222050920626371675)
    ·
      refine ⟨132324568833076380939557513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88216379222050920626371675 132324568833076380939557513)
      ·
        refine ⟨99243426624807285704668135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132324568833076380939557513 99243426624807285704668135)
        ·
          refine ⟨148865139937210928557002203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99243426624807285704668135 148865139937210928557002203)
          ·
            refine ⟨223297709905816392835503305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148865139937210928557002203 223297709905816392835503305)
            ·
              refine ⟨167473282429362294626627479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223297709905816392835503305 167473282429362294626627479)
              ·
                refine ⟨251209923644043441939941219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167473282429362294626627479 251209923644043441939941219)
                ·
                  refine ⟨376814885466065162909911829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251209923644043441939941219 376814885466065162909911829)
                  ·
                    refine ⟨17663197756221804511402117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 376814885466065162909911829 17663197756221804511402117)
                    ·
                      refine ⟨3311849579291588345887897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17663197756221804511402117 3311849579291588345887897)
                      ·
                        rfl

theorem cell23_6449804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_6449804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449804 prefixEnd_6449804 := by exact prefixLift 6449804
  have htrace : WordTrace (prefixWord ++ tailWord_6449804) baseStart_6449804 baseEnd_6449804 := by
    simpa [prefixWord, tailWord_6449804, baseEnd_6449804] using wordTrace_append hprefix tailTrace_6449804
  have hstable : (prefixWord ++ tailWord_6449804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449804).length < 2 ^ (prefixWord ++ tailWord_6449804).sum := by decide
  have hdescent : baseEnd_6449804 < baseStart_6449804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449911 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 4]
def baseStart_6449911 : Nat := 118140960795 + 6449911 * 2 ^ 59
def prefixEnd_6449911 : Nat := 4983230072969 + 3 ^ 40 * 6449911 * 2
def baseEnd_6449911 : Nat := 3311904521721619427249905

theorem tailTrace_6449911 : CollatzResearch.WordTrace tailWord_6449911 prefixEnd_6449911 3311904521721619427249905 := by
  unfold tailWord_6449911
  simp only [CollatzResearch.WordTrace]
  refine ⟨235247580536081478944469587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156831720357387652629646391 235247580536081478944469587)
  ·
    refine ⟨352871370804122218416704381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235247580536081478944469587 352871370804122218416704381)
    ·
      refine ⟨132326764051545831906264143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352871370804122218416704381 132326764051545831906264143)
      ·
        refine ⟨198490146077318747859396215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132326764051545831906264143 198490146077318747859396215)
        ·
          refine ⟨297735219115978121789094323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198490146077318747859396215 297735219115978121789094323)
          ·
            refine ⟨446602828673967182683641485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297735219115978121789094323 446602828673967182683641485)
            ·
              refine ⟨167476060752737693506365557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 446602828673967182683641485 167476060752737693506365557)
              ·
                refine ⟨15700880695569158766221771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167476060752737693506365557 15700880695569158766221771)
                ·
                  refine ⟨23551321043353738149332657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15700880695569158766221771 23551321043353738149332657)
                  ·
                    refine ⟨17663490782515303611999493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23551321043353738149332657 17663490782515303611999493)
                    ·
                      refine ⟨3311904521721619427249905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17663490782515303611999493 3311904521721619427249905)
                      ·
                        rfl

theorem cell23_6449911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_6449911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449911 prefixEnd_6449911 := by exact prefixLift 6449911
  have htrace : WordTrace (prefixWord ++ tailWord_6449911) baseStart_6449911 baseEnd_6449911 := by
    simpa [prefixWord, tailWord_6449911, baseEnd_6449911] using wordTrace_append hprefix tailTrace_6449911
  have hstable : (prefixWord ++ tailWord_6449911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449911).length < 2 ^ (prefixWord ++ tailWord_6449911).sum := by decide
  have hdescent : baseEnd_6449911 < baseStart_6449911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449928 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_6449928 : Nat := 118140960795 + 6449928 * 2 ^ 59
def prefixEnd_6449928 : Nat := 4983230072969 + 3 ^ 40 * 6449928 * 2
def baseEnd_6449928 : Nat := 3311913250892745860737327

theorem tailTrace_6449928 : CollatzResearch.WordTrace tailWord_6449928 prefixEnd_6449928 3311913250892745860737327 := by
  unfold tailWord_6449928
  simp only [CollatzResearch.WordTrace]
  refine ⟨117624100288509945423919219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156832133718013260565225625 117624100288509945423919219)
  ·
    refine ⟨176436150432764918135878829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117624100288509945423919219 176436150432764918135878829)
    ·
      refine ⟨66163556412286844300954561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176436150432764918135878829 66163556412286844300954561)
      ·
        refine ⟨49622667309215133225715921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66163556412286844300954561 49622667309215133225715921)
        ·
          refine ⟨37217000481911349919286941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49622667309215133225715921 37217000481911349919286941)
          ·
            refine ⟨13956375180716756219732603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37217000481911349919286941 13956375180716756219732603)
            ·
              refine ⟨20934562771075134329598905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13956375180716756219732603 20934562771075134329598905)
              ·
                refine ⟨15700922078306350747199179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20934562771075134329598905 15700922078306350747199179)
                ·
                  refine ⟨23551383117459526120798769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15700922078306350747199179 23551383117459526120798769)
                  ·
                    refine ⟨17663537338094644590599077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23551383117459526120798769 17663537338094644590599077)
                    ·
                      refine ⟨3311913250892745860737327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17663537338094644590599077 3311913250892745860737327)
                      ·
                        rfl

theorem cell23_6449928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_6449928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449928 prefixEnd_6449928 := by exact prefixLift 6449928
  have htrace : WordTrace (prefixWord ++ tailWord_6449928) baseStart_6449928 baseEnd_6449928 := by
    simpa [prefixWord, tailWord_6449928, baseEnd_6449928] using wordTrace_append hprefix tailTrace_6449928
  have hstable : (prefixWord ++ tailWord_6449928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449928).length < 2 ^ (prefixWord ++ tailWord_6449928).sum := by decide
  have hdescent : baseEnd_6449928 < baseStart_6449928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449932 : List Nat := [2, 2, 1, 2, 2, 1, 1, 7, 1, 2, 2]
def baseStart_6449932 : Nat := 118140960795 + 6449932 * 2 ^ 59
def prefixEnd_6449932 : Nat := 4983230072969 + 3 ^ 40 * 6449932 * 2
def baseEnd_6449932 : Nat := 3311915304815363845087309

theorem tailTrace_6449932 : CollatzResearch.WordTrace tailWord_6449932 prefixEnd_6449932 3311915304815363845087309 := by
  unfold tailWord_6449932
  simp only [CollatzResearch.WordTrace]
  refine ⟨117624173234502699765492025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156832230979336933020656033 117624173234502699765492025)
  ·
    refine ⟨88218129925877024824119019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117624173234502699765492025 88218129925877024824119019)
    ·
      refine ⟨132327194888815537236178529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88218129925877024824119019 132327194888815537236178529)
      ·
        refine ⟨99245396166611652927133897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132327194888815537236178529 99245396166611652927133897)
        ·
          refine ⟨74434047124958739695350423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99245396166611652927133897 74434047124958739695350423)
          ·
            refine ⟨111651070687438109543025635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74434047124958739695350423 111651070687438109543025635)
            ·
              refine ⟨167476606031157164314538453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111651070687438109543025635 167476606031157164314538453)
              ·
                refine ⟨3925232953855246038621995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 167476606031157164314538453 3925232953855246038621995)
                ·
                  refine ⟨5887849430782869057932993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925232953855246038621995 5887849430782869057932993)
                  ·
                    refine ⟨4415887073087151793449745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5887849430782869057932993 4415887073087151793449745)
                    ·
                      refine ⟨3311915304815363845087309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4415887073087151793449745 3311915304815363845087309)
                      ·
                        rfl

theorem cell23_6449932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_6449932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449932 prefixEnd_6449932 := by exact prefixLift 6449932
  have htrace : WordTrace (prefixWord ++ tailWord_6449932) baseStart_6449932 baseEnd_6449932 := by
    simpa [prefixWord, tailWord_6449932, baseEnd_6449932] using wordTrace_append hprefix tailTrace_6449932
  have hstable : (prefixWord ++ tailWord_6449932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449932).length < 2 ^ (prefixWord ++ tailWord_6449932).sum := by decide
  have hdescent : baseEnd_6449932 < baseStart_6449932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449935 : List Nat := [1, 1, 2, 1, 1, 1, 9, 1, 1, 2, 3]
def baseStart_6449935 : Nat := 118140960795 + 6449935 * 2 ^ 59
def prefixEnd_6449935 : Nat := 4983230072969 + 3 ^ 40 * 6449935 * 2
def baseEnd_6449935 : Nat := 3311916845257327333349795

theorem tailTrace_6449935 : CollatzResearch.WordTrace tailWord_6449935 prefixEnd_6449935 3311916845257327333349795 := by
  unfold tailWord_6449935
  simp only [CollatzResearch.WordTrace]
  refine ⟨235248455887994531043343259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156832303925329687362228839 235248455887994531043343259)
  ·
    refine ⟨352872683831991796565014889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235248455887994531043343259 352872683831991796565014889)
    ·
      refine ⟨264654512873993847423761167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352872683831991796565014889 264654512873993847423761167)
      ·
        refine ⟨396981769310990771135641751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264654512873993847423761167 396981769310990771135641751)
        ·
          refine ⟨595472653966486156703462627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396981769310990771135641751 595472653966486156703462627)
          ·
            refine ⟨893208980949729235055193941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595472653966486156703462627 893208980949729235055193941)
            ·
              refine ⟨5233646372752319736651527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 893208980949729235055193941 5233646372752319736651527)
              ·
                refine ⟨7850469559128479604977291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5233646372752319736651527 7850469559128479604977291)
                ·
                  refine ⟨11775704338692719407465937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7850469559128479604977291 11775704338692719407465937)
                  ·
                    refine ⟨8831778254019539555599453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11775704338692719407465937 8831778254019539555599453)
                    ·
                      refine ⟨3311916845257327333349795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8831778254019539555599453 3311916845257327333349795)
                      ·
                        rfl

theorem cell23_6449935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 1, 2, 3].length) (baseStart_6449935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449935 prefixEnd_6449935 := by exact prefixLift 6449935
  have htrace : WordTrace (prefixWord ++ tailWord_6449935) baseStart_6449935 baseEnd_6449935 := by
    simpa [prefixWord, tailWord_6449935, baseEnd_6449935] using wordTrace_append hprefix tailTrace_6449935
  have hstable : (prefixWord ++ tailWord_6449935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449935).length < 2 ^ (prefixWord ++ tailWord_6449935).sum := by decide
  have hdescent : baseEnd_6449935 < baseStart_6449935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449938 : List Nat := [3, 2, 4, 1, 2, 11]
def baseStart_6449938 : Nat := 118140960795 + 6449938 * 2 ^ 59
def prefixEnd_6449938 : Nat := 4983230072969 + 3 ^ 40 * 6449938 * 2
def baseEnd_6449938 : Nat := 13629293768309838772067

theorem tailTrace_6449938 : CollatzResearch.WordTrace tailWord_6449938 prefixEnd_6449938 13629293768309838772067 := by
  unfold tailWord_6449938
  simp only [CollatzResearch.WordTrace]
  refine ⟨58812141326745915638925617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156832376871322441703801645 58812141326745915638925617)
  ·
    refine ⟨44109105995059436729194213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58812141326745915638925617 44109105995059436729194213)
    ·
      refine ⟨8270457374073644386723915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44109105995059436729194213 8270457374073644386723915)
      ·
        refine ⟨12405686061110466580085873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8270457374073644386723915 12405686061110466580085873)
        ·
          refine ⟨9304264545832849935064405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12405686061110466580085873 9304264545832849935064405)
          ·
            refine ⟨13629293768309838772067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9304264545832849935064405 13629293768309838772067)
            ·
              rfl

theorem cell23_6449938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 11].length) (baseStart_6449938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449938 prefixEnd_6449938 := by exact prefixLift 6449938
  have htrace : WordTrace (prefixWord ++ tailWord_6449938) baseStart_6449938 baseEnd_6449938 := by
    simpa [prefixWord, tailWord_6449938, baseEnd_6449938] using wordTrace_append hprefix tailTrace_6449938
  have hstable : (prefixWord ++ tailWord_6449938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449938).length < 2 ^ (prefixWord ++ tailWord_6449938).sum := by decide
  have hdescent : baseEnd_6449938 < baseStart_6449938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449951 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 2, 7]
def baseStart_6449951 : Nat := 118140960795 + 6449951 * 2 ^ 59
def prefixEnd_6449951 : Nat := 4983230072969 + 3 ^ 40 * 6449951 * 2
def baseEnd_6449951 : Nat := 1103975020315933090249907

theorem tailTrace_6449951 : CollatzResearch.WordTrace tailWord_6449951 prefixEnd_6449951 1103975020315933090249907 := by
  unfold tailWord_6449951
  simp only [CollatzResearch.WordTrace]
  refine ⟨235249039455936565775925707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156832692970624377183950471 235249039455936565775925707)
  ·
    refine ⟨352873559183904848663888561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235249039455936565775925707 352873559183904848663888561)
    ·
      refine ⟨264655169387928636497916421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352873559183904848663888561 264655169387928636497916421)
      ·
        refine ⟨49622844260236619343359329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264655169387928636497916421 49622844260236619343359329)
        ·
          refine ⟨37217133195177464507519497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49622844260236619343359329 37217133195177464507519497)
          ·
            refine ⟨27912849896383098380639623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37217133195177464507519497 27912849896383098380639623)
            ·
              refine ⟨41869274844574647570959435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27912849896383098380639623 41869274844574647570959435)
              ·
                refine ⟨62803912266861971356439153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41869274844574647570959435 62803912266861971356439153)
                ·
                  refine ⟨47102934200146478517329365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62803912266861971356439153 47102934200146478517329365)
                  ·
                    refine ⟨1103975020315933090249907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47102934200146478517329365 1103975020315933090249907)
                    ·
                      rfl

theorem cell23_6449951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 7].length) (baseStart_6449951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449951 prefixEnd_6449951 := by exact prefixLift 6449951
  have htrace : WordTrace (prefixWord ++ tailWord_6449951) baseStart_6449951 baseEnd_6449951 := by
    simpa [prefixWord, tailWord_6449951, baseEnd_6449951] using wordTrace_append hprefix tailTrace_6449951
  have hstable : (prefixWord ++ tailWord_6449951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449951).length < 2 ^ (prefixWord ++ tailWord_6449951).sum := by decide
  have hdescent : baseEnd_6449951 < baseStart_6449951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449962 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6449962 : Nat := 118140960795 + 6449962 * 2 ^ 59
def prefixEnd_6449962 : Nat := 4983230072969 + 3 ^ 40 * 6449962 * 2
def baseEnd_6449962 : Nat := 3311930709234998727712171

theorem tailTrace_6449962 : CollatzResearch.WordTrace tailWord_6449962 prefixEnd_6449962 3311930709234998727712171 := by
  unfold tailWord_6449962
  simp only [CollatzResearch.WordTrace]
  refine ⟨58812360164724178663644035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156832960439264476436384093 58812360164724178663644035)
  ·
    refine ⟨88218540247086267995466053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58812360164724178663644035 88218540247086267995466053)
    ·
      refine ⟨16540976296328675249149885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88218540247086267995466053 16540976296328675249149885)
      ·
        refine ⟨6202866111123253218431207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16540976296328675249149885 6202866111123253218431207)
        ·
          refine ⟨9304299166684879827646811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6202866111123253218431207 9304299166684879827646811)
          ·
            refine ⟨13956448750027319741470217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9304299166684879827646811 13956448750027319741470217)
            ·
              refine ⟨10467336562520489806102663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13956448750027319741470217 10467336562520489806102663)
              ·
                refine ⟨15701004843780734709153995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10467336562520489806102663 15701004843780734709153995)
                ·
                  refine ⟨23551507265671102063730993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15701004843780734709153995 23551507265671102063730993)
                  ·
                    refine ⟨17663630449253326547798245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23551507265671102063730993 17663630449253326547798245)
                    ·
                      refine ⟨3311930709234998727712171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17663630449253326547798245 3311930709234998727712171)
                      ·
                        rfl

theorem cell23_6449962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6449962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449962 prefixEnd_6449962 := by exact prefixLift 6449962
  have htrace : WordTrace (prefixWord ++ tailWord_6449962) baseStart_6449962 baseEnd_6449962 := by
    simpa [prefixWord, tailWord_6449962, baseEnd_6449962] using wordTrace_append hprefix tailTrace_6449962
  have hstable : (prefixWord ++ tailWord_6449962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449962).length < 2 ^ (prefixWord ++ tailWord_6449962).sum := by decide
  have hdescent : baseEnd_6449962 < baseStart_6449962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449975 : List Nat := [1, 1, 3, 1, 2, 1, 4, 4, 1, 3, 2]
def baseStart_6449975 : Nat := 118140960795 + 6449975 * 2 ^ 59
def prefixEnd_6449975 : Nat := 4983230072969 + 3 ^ 40 * 6449975 * 2
def baseEnd_6449975 : Nat := 3311937384483507176849611

theorem tailTrace_6449975 : CollatzResearch.WordTrace tailWord_6449975 prefixEnd_6449975 3311937384483507176849611 := by
  unfold tailWord_6449975
  simp only [CollatzResearch.WordTrace]
  refine ⟨235249914807849617874799379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156833276538566411916532919 235249914807849617874799379)
  ·
    refine ⟨352874872211774426812199069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235249914807849617874799379 352874872211774426812199069)
    ·
      refine ⟨132328077079415410054574651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352874872211774426812199069 132328077079415410054574651)
      ·
        refine ⟨198492115619123115081861977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132328077079415410054574651 198492115619123115081861977)
        ·
          refine ⟨148869086714342336311396483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198492115619123115081861977 148869086714342336311396483)
          ·
            refine ⟨223303630071513504467094725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148869086714342336311396483 223303630071513504467094725)
            ·
              refine ⟨41869430638408782087580261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223303630071513504467094725 41869430638408782087580261)
              ·
                refine ⟨7850518244701646641421299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41869430638408782087580261 7850518244701646641421299)
                ·
                  refine ⟨11775777367052469962131949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7850518244701646641421299 11775777367052469962131949)
                  ·
                    refine ⟨4415916512644676235799481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11775777367052469962131949 4415916512644676235799481)
                    ·
                      refine ⟨3311937384483507176849611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4415916512644676235799481 3311937384483507176849611)
                      ·
                        rfl

theorem cell23_6449975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 3, 2].length) (baseStart_6449975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449975 prefixEnd_6449975 := by exact prefixLift 6449975
  have htrace : WordTrace (prefixWord ++ tailWord_6449975) baseStart_6449975 baseEnd_6449975 := by
    simpa [prefixWord, tailWord_6449975, baseEnd_6449975] using wordTrace_append hprefix tailTrace_6449975
  have hstable : (prefixWord ++ tailWord_6449975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449975).length < 2 ^ (prefixWord ++ tailWord_6449975).sum := by decide
  have hdescent : baseEnd_6449975 < baseStart_6449975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6449991 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_6449991 : Nat := 118140960795 + 6449991 * 2 ^ 59
def prefixEnd_6449991 : Nat := 4983230072969 + 3 ^ 40 * 6449991 * 2
def baseEnd_6449991 : Nat := 3311945600173979114249537

theorem tailTrace_6449991 : CollatzResearch.WordTrace tailWord_6449991 prefixEnd_6449991 3311945600173979114249537 := by
  unfold tailWord_6449991
  simp only [CollatzResearch.WordTrace]
  refine ⟨235250498375791652607381827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156833665583861101738254551 235250498375791652607381827)
  ·
    refine ⟨352875747563687478911072741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235250498375791652607381827 352875747563687478911072741)
    ·
      refine ⟨66164202668191402295826139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 352875747563687478911072741 66164202668191402295826139)
      ·
        refine ⟨99246304002287103443739209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66164202668191402295826139 99246304002287103443739209)
        ·
          refine ⟨74434728001715327582804407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99246304002287103443739209 74434728001715327582804407)
          ·
            refine ⟨111652092002572991374206611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74434728001715327582804407 111652092002572991374206611)
            ·
              refine ⟨167478138003859487061309917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111652092002572991374206611 167478138003859487061309917)
              ·
                refine ⟨62804301751447307647991219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167478138003859487061309917 62804301751447307647991219)
                ·
                  refine ⟨94206452627170961471986829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62804301751447307647991219 94206452627170961471986829)
                  ·
                    refine ⟨35327419735189110551995061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94206452627170961471986829 35327419735189110551995061)
                    ·
                      refine ⟨3311945600173979114249537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35327419735189110551995061 3311945600173979114249537)
                      ·
                        rfl

theorem cell23_6449991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_6449991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6449991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6449991 prefixEnd_6449991 := by exact prefixLift 6449991
  have htrace : WordTrace (prefixWord ++ tailWord_6449991) baseStart_6449991 baseEnd_6449991 := by
    simpa [prefixWord, tailWord_6449991, baseEnd_6449991] using wordTrace_append hprefix tailTrace_6449991
  have hstable : (prefixWord ++ tailWord_6449991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6449991).length < 2 ^ (prefixWord ++ tailWord_6449991).sum := by decide
  have hdescent : baseEnd_6449991 < baseStart_6449991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6449991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450045 : List Nat := [1, 4, 1, 1, 2, 1, 5, 3, 5]
def baseStart_6450045 : Nat := 118140960795 + 6450045 * 2 ^ 59
def prefixEnd_6450045 : Nat := 4983230072969 + 3 ^ 40 * 6450045 * 2
def baseEnd_6450045 : Nat := 367997036458813544774921

theorem tailTrace_6450045 : CollatzResearch.WordTrace tailWord_6450045 prefixEnd_6450045 367997036458813544774921 := by
  unfold tailWord_6450045
  simp only [CollatzResearch.WordTrace]
  refine ⟨235252467917596019829847589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156834978611730679886565059 235252467917596019829847589)
  ·
    refine ⟨44109837734549253718096423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235252467917596019829847589 44109837734549253718096423)
    ·
      refine ⟨66164756601823880577144635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44109837734549253718096423 66164756601823880577144635)
      ·
        refine ⟨99247134902735820865716953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66164756601823880577144635 99247134902735820865716953)
        ·
          refine ⟨74435351177051865649287715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99247134902735820865716953 74435351177051865649287715)
          ·
            refine ⟨111653026765577798473931573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74435351177051865649287715 111653026765577798473931573)
            ·
              refine ⟨10467471259272918606931085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111653026765577798473931573 10467471259272918606931085)
              ·
                refine ⟨3925301722227344477599157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10467471259272918606931085 3925301722227344477599157)
                ·
                  refine ⟨367997036458813544774921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3925301722227344477599157 367997036458813544774921)
                  ·
                    rfl

theorem cell23_6450045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_6450045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450045 prefixEnd_6450045 := by exact prefixLift 6450045
  have htrace : WordTrace (prefixWord ++ tailWord_6450045) baseStart_6450045 baseEnd_6450045 := by
    simpa [prefixWord, tailWord_6450045, baseEnd_6450045] using wordTrace_append hprefix tailTrace_6450045
  have hstable : (prefixWord ++ tailWord_6450045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450045).length < 2 ^ (prefixWord ++ tailWord_6450045).sum := by decide
  have hdescent : baseEnd_6450045 < baseStart_6450045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450128 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 3]
def baseStart_6450128 : Nat := 118140960795 + 6450128 * 2 ^ 59
def prefixEnd_6450128 : Nat := 4983230072969 + 3 ^ 40 * 6450128 * 2
def baseEnd_6450128 : Nat := 3312015947023645078236407

theorem tailTrace_6450128 : CollatzResearch.WordTrace tailWord_6450128 prefixEnd_6450128 3312015947023645078236407 := by
  unfold tailWord_6450128
  simp only [CollatzResearch.WordTrace]
  refine ⟨117627747588147662502559519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156836996784196883336746025 117627747588147662502559519)
  ·
    refine ⟨176441621382221493753839279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117627747588147662502559519 176441621382221493753839279)
    ·
      refine ⟨264662432073332240630758919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176441621382221493753839279 264662432073332240630758919)
      ·
        refine ⟨396993648109998360946138379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264662432073332240630758919 396993648109998360946138379)
        ·
          refine ⟨595490472164997541419207569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396993648109998360946138379 595490472164997541419207569)
          ·
            refine ⟨446617854123748156064405677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595490472164997541419207569 446617854123748156064405677)
            ·
              refine ⟨167481695296405558524152129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 446617854123748156064405677 167481695296405558524152129)
              ·
                refine ⟨125611271472304168893114097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167481695296405558524152129 125611271472304168893114097)
                ·
                  refine ⟨94208453604228126669835573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125611271472304168893114097 94208453604228126669835573)
                  ·
                    refine ⟨8832042525396386875297085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94208453604228126669835573 8832042525396386875297085)
                    ·
                      refine ⟨3312015947023645078236407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8832042525396386875297085 3312015947023645078236407)
                      ·
                        rfl

theorem cell23_6450128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 3].length) (baseStart_6450128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450128 prefixEnd_6450128 := by exact prefixLift 6450128
  have htrace : WordTrace (prefixWord ++ tailWord_6450128) baseStart_6450128 baseEnd_6450128 := by
    simpa [prefixWord, tailWord_6450128, baseEnd_6450128] using wordTrace_append hprefix tailTrace_6450128
  have hstable : (prefixWord ++ tailWord_6450128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450128).length < 2 ^ (prefixWord ++ tailWord_6450128).sum := by decide
  have hdescent : baseEnd_6450128 < baseStart_6450128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450202 : List Nat := [3, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4]
def baseStart_6450202 : Nat := 118140960795 + 6450202 * 2 ^ 59
def prefixEnd_6450202 : Nat := 4983230072969 + 3 ^ 40 * 6450202 * 2
def baseEnd_6450202 : Nat := 3312053944592077788711067

theorem tailTrace_6450202 : CollatzResearch.WordTrace tailWord_6450202 prefixEnd_6450202 3312053944592077788711067 := by
  unfold tailWord_6450202
  simp only [CollatzResearch.WordTrace]
  refine ⟨58814548544506808910828215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156838796118684823762208573 58814548544506808910828215)
  ·
    refine ⟨88221822816760213366242323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58814548544506808910828215 88221822816760213366242323)
    ·
      refine ⟨132332734225140320049363485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88221822816760213366242323 132332734225140320049363485)
      ·
        refine ⟨49624775334427620018511307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132332734225140320049363485 49624775334427620018511307)
        ·
          refine ⟨74437163001641430027766961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49624775334427620018511307 74437163001641430027766961)
          ·
            refine ⟨55827872251231072520825221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74437163001641430027766961 55827872251231072520825221)
            ·
              refine ⟨10467726047105826097654729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55827872251231072520825221 10467726047105826097654729)
              ·
                refine ⟨7850794535329369573241047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10467726047105826097654729 7850794535329369573241047)
                ·
                  refine ⟨11776191802994054359861571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7850794535329369573241047 11776191802994054359861571)
                  ·
                    refine ⟨17664287704491081539792357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11776191802994054359861571 17664287704491081539792357)
                    ·
                      refine ⟨3312053944592077788711067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17664287704491081539792357 3312053944592077788711067)
                      ·
                        rfl

theorem cell23_6450202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_6450202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450202 prefixEnd_6450202 := by exact prefixLift 6450202
  have htrace : WordTrace (prefixWord ++ tailWord_6450202) baseStart_6450202 baseEnd_6450202 := by
    simpa [prefixWord, tailWord_6450202, baseEnd_6450202] using wordTrace_append hprefix tailTrace_6450202
  have hstable : (prefixWord ++ tailWord_6450202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450202).length < 2 ^ (prefixWord ++ tailWord_6450202).sum := by decide
  have hdescent : baseEnd_6450202 < baseStart_6450202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450212 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_6450212 : Nat := 118140960795 + 6450212 * 2 ^ 59
def prefixEnd_6450212 : Nat := 4983230072969 + 3 ^ 40 * 6450212 * 2
def baseEnd_6450212 : Nat := 1104019693132874249862007

theorem tailTrace_6450212 : CollatzResearch.WordTrace tailWord_6450212 prefixEnd_6450212 1104019693132874249862007 := by
  unfold tailWord_6450212
  simp only [CollatzResearch.WordTrace]
  refine ⟨117629279453995503675588445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156839039271994004900784593 117629279453995503675588445)
  ·
    refine ⟨44110979795248313878345667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117629279453995503675588445 44110979795248313878345667)
    ·
      refine ⟨66166469692872470817518501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44110979795248313878345667 66166469692872470817518501)
      ·
        refine ⟨12406213067413588278284719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66166469692872470817518501 12406213067413588278284719)
        ·
          refine ⟨18609319601120382417427079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12406213067413588278284719 18609319601120382417427079)
          ·
            refine ⟨27913979401680573626140619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18609319601120382417427079 27913979401680573626140619)
            ·
              refine ⟨41870969102520860439210929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27913979401680573626140619 41870969102520860439210929)
              ·
                refine ⟨31403226826890645329408197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41870969102520860439210929 31403226826890645329408197)
                ·
                  refine ⟨5888105030041995999264037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31403226826890645329408197 5888105030041995999264037)
                  ·
                    refine ⟨1104019693132874249862007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5888105030041995999264037 1104019693132874249862007)
                    ·
                      rfl

theorem cell23_6450212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_6450212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450212 prefixEnd_6450212 := by exact prefixLift 6450212
  have htrace : WordTrace (prefixWord ++ tailWord_6450212) baseStart_6450212 baseEnd_6450212 := by
    simpa [prefixWord, tailWord_6450212, baseEnd_6450212] using wordTrace_append hprefix tailTrace_6450212
  have hstable : (prefixWord ++ tailWord_6450212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450212).length < 2 ^ (prefixWord ++ tailWord_6450212).sum := by decide
  have hdescent : baseEnd_6450212 < baseStart_6450212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450222 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_6450222 : Nat := 118140960795 + 6450222 * 2 ^ 59
def prefixEnd_6450222 : Nat := 4983230072969 + 3 ^ 40 * 6450222 * 2
def baseEnd_6450222 : Nat := 3312064214205167710460975

theorem tailTrace_6450222 : CollatzResearch.WordTrace tailWord_6450222 prefixEnd_6450222 3312064214205167710460975 := by
  unfold tailWord_6450222
  simp only [CollatzResearch.WordTrace]
  refine ⟨29407365454744347382380115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156839282425303186039360613 29407365454744347382380115)
  ·
    refine ⟨44111048182116521073570173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29407365454744347382380115 44111048182116521073570173)
    ·
      refine ⟨16541643068293695402588815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44111048182116521073570173 16541643068293695402588815)
      ·
        refine ⟨24812464602440543103883223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16541643068293695402588815 24812464602440543103883223)
        ·
          refine ⟨37218696903660814655824835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24812464602440543103883223 37218696903660814655824835)
          ·
            refine ⟨55828045355491221983737253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37218696903660814655824835 55828045355491221983737253)
            ·
              refine ⟨10467758504154604121950735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55828045355491221983737253 10467758504154604121950735)
              ·
                refine ⟨15701637756231906182926103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10467758504154604121950735 15701637756231906182926103)
                ·
                  refine ⟨23552456634347859274389155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15701637756231906182926103 23552456634347859274389155)
                  ·
                    refine ⟨35328684951521788911583733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23552456634347859274389155 35328684951521788911583733)
                    ·
                      refine ⟨3312064214205167710460975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35328684951521788911583733 3312064214205167710460975)
                      ·
                        rfl

theorem cell23_6450222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_6450222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450222 prefixEnd_6450222 := by exact prefixLift 6450222
  have htrace : WordTrace (prefixWord ++ tailWord_6450222) baseStart_6450222 baseEnd_6450222 := by
    simpa [prefixWord, tailWord_6450222, baseEnd_6450222] using wordTrace_append hprefix tailTrace_6450222
  have hstable : (prefixWord ++ tailWord_6450222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450222).length < 2 ^ (prefixWord ++ tailWord_6450222).sum := by decide
  have hdescent : baseEnd_6450222 < baseStart_6450222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450236 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 3, 2, 2]
def baseStart_6450236 : Nat := 118140960795 + 6450236 * 2 ^ 59
def prefixEnd_6450236 : Nat := 4983230072969 + 3 ^ 40 * 6450236 * 2
def baseEnd_6450236 : Nat := 3312071402934330655685911

theorem tailTrace_6450236 : CollatzResearch.WordTrace tailWord_6450236 prefixEnd_6450236 3312071402934330655685911 := by
  unfold tailWord_6450236
  simp only [CollatzResearch.WordTrace]
  refine ⟨117629717129952029725025281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156839622839936039633367041 117629717129952029725025281)
  ·
    refine ⟨88222287847464022293768961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117629717129952029725025281 88222287847464022293768961)
    ·
      refine ⟨66166715885598016720326721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88222287847464022293768961 66166715885598016720326721)
      ·
        refine ⟨49625036914198512540245041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66166715885598016720326721 49625036914198512540245041)
        ·
          refine ⟨37218777685648884405183781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49625036914198512540245041 37218777685648884405183781)
          ·
            refine ⟨6978520816059165825971959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37218777685648884405183781 6978520816059165825971959)
            ·
              refine ⟨10467781224088748738957939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6978520816059165825971959 10467781224088748738957939)
              ·
                refine ⟨15701671836133123108436909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10467781224088748738957939 15701671836133123108436909)
                ·
                  refine ⟨5888126938549921165663841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15701671836133123108436909 5888126938549921165663841)
                  ·
                    refine ⟨4416095203912440874247881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5888126938549921165663841 4416095203912440874247881)
                    ·
                      refine ⟨3312071402934330655685911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416095203912440874247881 3312071402934330655685911)
                      ·
                        rfl

theorem cell23_6450236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_6450236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450236 prefixEnd_6450236 := by exact prefixLift 6450236
  have htrace : WordTrace (prefixWord ++ tailWord_6450236) baseStart_6450236 baseEnd_6450236 := by
    simpa [prefixWord, tailWord_6450236, baseEnd_6450236] using wordTrace_append hprefix tailTrace_6450236
  have hstable : (prefixWord ++ tailWord_6450236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450236).length < 2 ^ (prefixWord ++ tailWord_6450236).sum := by decide
  have hdescent : baseEnd_6450236 < baseStart_6450236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450246 : List Nat := [6, 1, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_6450246 : Nat := 118140960795 + 6450246 * 2 ^ 59
def prefixEnd_6450246 : Nat := 4983230072969 + 3 ^ 40 * 6450246 * 2
def baseEnd_6450246 : Nat := 1104025512580291872186955

theorem tailTrace_6450246 : CollatzResearch.WordTrace tailWord_6450246 prefixEnd_6450246 1104025512580291872186955 := by
  unfold tailWord_6450246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7351868718433369723684831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156839865993245220771943061 7351868718433369723684831)
  ·
    refine ⟨11027803077650054585527247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7351868718433369723684831 11027803077650054585527247)
    ·
      refine ⟨16541704616475081878290871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11027803077650054585527247 16541704616475081878290871)
      ·
        refine ⟨24812556924712622817436307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16541704616475081878290871 24812556924712622817436307)
        ·
          refine ⟨37218835387068934226154461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24812556924712622817436307 37218835387068934226154461)
          ·
            refine ⟨13957063270150850334807923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37218835387068934226154461 13957063270150850334807923)
            ·
              refine ⟨20935594905226275502211885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13957063270150850334807923 20935594905226275502211885)
              ·
                refine ⟨7850848089459853313329457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20935594905226275502211885 7850848089459853313329457)
                ·
                  refine ⟨5888136067094889984997093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7850848089459853313329457 5888136067094889984997093)
                  ·
                    refine ⟨1104025512580291872186955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5888136067094889984997093 1104025512580291872186955)
                    ·
                      rfl

theorem cell23_6450246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_6450246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450246 prefixEnd_6450246 := by exact prefixLift 6450246
  have htrace : WordTrace (prefixWord ++ tailWord_6450246) baseStart_6450246 baseEnd_6450246 := by
    simpa [prefixWord, tailWord_6450246, baseEnd_6450246] using wordTrace_append hprefix tailTrace_6450246
  have hstable : (prefixWord ++ tailWord_6450246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450246).length < 2 ^ (prefixWord ++ tailWord_6450246).sum := by decide
  have hdescent : baseEnd_6450246 < baseStart_6450246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450286 : List Nat := [4, 1, 2, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_6450286 : Nat := 118140960795 + 6450286 * 2 ^ 59
def prefixEnd_6450286 : Nat := 4983230072969 + 3 ^ 40 * 6450286 * 2
def baseEnd_6450286 : Nat := 3312097076967055460060681

theorem tailTrace_6450286 : CollatzResearch.WordTrace tailWord_6450286 prefixEnd_6450286 3312097076967055460060681 := by
  unfold tailWord_6450286
  simp only [CollatzResearch.WordTrace]
  refine ⟨29407657238715364748671339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156840838606481945326247141 29407657238715364748671339)
  ·
    refine ⟨44111485858073047123007009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29407657238715364748671339 44111485858073047123007009)
    ·
      refine ⟨33083614393554785342255257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44111485858073047123007009 33083614393554785342255257)
      ·
        refine ⟨24812710795166089006691443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33083614393554785342255257 24812710795166089006691443)
        ·
          refine ⟨37219066192749133510037165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24812710795166089006691443 37219066192749133510037165)
          ·
            refine ⟨13957149822280925066263937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37219066192749133510037165 13957149822280925066263937)
            ·
              refine ⟨10467862366710693799697953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13957149822280925066263937 10467862366710693799697953)
              ·
                refine ⟨7850896775033020349773465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10467862366710693799697953 7850896775033020349773465)
                ·
                  refine ⟨5888172581274765262330099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7850896775033020349773465 5888172581274765262330099)
                  ·
                    refine ⟨8832258871912147893495149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5888172581274765262330099 8832258871912147893495149)
                    ·
                      refine ⟨3312097076967055460060681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8832258871912147893495149 3312097076967055460060681)
                      ·
                        rfl

theorem cell23_6450286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_6450286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450286 prefixEnd_6450286 := by exact prefixLift 6450286
  have htrace : WordTrace (prefixWord ++ tailWord_6450286) baseStart_6450286 baseEnd_6450286 := by
    simpa [prefixWord, tailWord_6450286, baseEnd_6450286] using wordTrace_append hprefix tailTrace_6450286
  have hstable : (prefixWord ++ tailWord_6450286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450286).length < 2 ^ (prefixWord ++ tailWord_6450286).sum := by decide
  have hdescent : baseEnd_6450286 < baseStart_6450286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450295 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 3]
def baseStart_6450295 : Nat := 118140960795 + 6450295 * 2 ^ 59
def prefixEnd_6450295 : Nat := 4983230072969 + 3 ^ 40 * 6450295 * 2
def baseEnd_6450295 : Nat := 3312101698292945924848139

theorem tailTrace_6450295 : CollatzResearch.WordTrace tailWord_6450295 prefixEnd_6450295 3312101698292945924848139 := by
  unfold tailWord_6450295
  simp only [CollatzResearch.WordTrace]
  refine ⟨235261586166690312526448339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156841057444460208350965559 235261586166690312526448339)
  ·
    refine ⟨352892379250035468789672509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235261586166690312526448339 352892379250035468789672509)
    ·
      refine ⟨132334642218763300796127191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352892379250035468789672509 132334642218763300796127191)
      ·
        refine ⟨198501963328144951194190787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132334642218763300796127191 198501963328144951194190787)
        ·
          refine ⟨297752944992217426791286181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198501963328144951194190787 297752944992217426791286181)
          ·
            refine ⟨55828677186040767523366159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 297752944992217426791286181 55828677186040767523366159)
            ·
              refine ⟨83743015779061151285049239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55828677186040767523366159 83743015779061151285049239)
              ·
                refine ⟨125614523668591726927573859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83743015779061151285049239 125614523668591726927573859)
                ·
                  refine ⟨188421785502887590391360789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125614523668591726927573859 188421785502887590391360789)
                  ·
                    refine ⟨8832271195447855799595037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 188421785502887590391360789 8832271195447855799595037)
                    ·
                      refine ⟨3312101698292945924848139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8832271195447855799595037 3312101698292945924848139)
                      ·
                        rfl

theorem cell23_6450295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_6450295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450295 prefixEnd_6450295 := by exact prefixLift 6450295
  have htrace : WordTrace (prefixWord ++ tailWord_6450295) baseStart_6450295 baseEnd_6450295 := by
    simpa [prefixWord, tailWord_6450295, baseEnd_6450295] using wordTrace_append hprefix tailTrace_6450295
  have hstable : (prefixWord ++ tailWord_6450295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450295).length < 2 ^ (prefixWord ++ tailWord_6450295).sum := by decide
  have hdescent : baseEnd_6450295 < baseStart_6450295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450343 : List Nat := [1, 1, 6, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_6450343 : Nat := 118140960795 + 6450343 * 2 ^ 59
def prefixEnd_6450343 : Nat := 4983230072969 + 3 ^ 40 * 6450343 * 2
def baseEnd_6450343 : Nat := 3312126345364361737047919

theorem tailTrace_6450343 : CollatzResearch.WordTrace tailWord_6450343 prefixEnd_6450343 3312126345364361737047919 := by
  unfold tailWord_6450343
  simp only [CollatzResearch.WordTrace]
  refine ⟨235263336870516416724195683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156842224580344277816130455 235263336870516416724195683)
  ·
    refine ⟨352895005305774625086293525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235263336870516416724195683 352895005305774625086293525)
    ·
      refine ⟨16541953373708185550920009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 352895005305774625086293525 16541953373708185550920009)
      ·
        refine ⟨12406465030281139163190007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16541953373708185550920009 12406465030281139163190007)
        ·
          refine ⟨18609697545421708744785011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12406465030281139163190007 18609697545421708744785011)
          ·
            refine ⟨27914546318132563117177517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18609697545421708744785011 27914546318132563117177517)
            ·
              refine ⟨10467954869299711168941569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27914546318132563117177517 10467954869299711168941569)
              ·
                refine ⟨7850966151974783376706177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10467954869299711168941569 7850966151974783376706177)
                ·
                  refine ⟨5888224613981087532529633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7850966151974783376706177 5888224613981087532529633)
                  ·
                    refine ⟨4416168460485815649397225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5888224613981087532529633 4416168460485815649397225)
                    ·
                      refine ⟨3312126345364361737047919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416168460485815649397225 3312126345364361737047919)
                      ·
                        rfl

theorem cell23_6450343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_6450343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450343 prefixEnd_6450343 := by exact prefixLift 6450343
  have htrace : WordTrace (prefixWord ++ tailWord_6450343) baseStart_6450343 baseEnd_6450343 := by
    simpa [prefixWord, tailWord_6450343, baseEnd_6450343] using wordTrace_append hprefix tailTrace_6450343
  have hstable : (prefixWord ++ tailWord_6450343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450343).length < 2 ^ (prefixWord ++ tailWord_6450343).sum := by decide
  have hdescent : baseEnd_6450343 < baseStart_6450343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450349 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 7]
def baseStart_6450349 : Nat := 118140960795 + 6450349 * 2 ^ 59
def prefixEnd_6450349 : Nat := 4983230072969 + 3 ^ 40 * 6450349 * 2
def baseEnd_6450349 : Nat := 368014380694254301508099

theorem tailTrace_6450349 : CollatzResearch.WordTrace tailWord_6450349 prefixEnd_6450349 368014380694254301508099 := by
  unfold tailWord_6450349
  simp only [CollatzResearch.WordTrace]
  refine ⟨235263555708494679748914101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156842370472329786499276067 235263555708494679748914101)
  ·
    refine ⟨22055958347671376226460697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235263555708494679748914101 22055958347671376226460697)
    ·
      refine ⟨16541968760753532169845523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22055958347671376226460697 16541968760753532169845523)
      ·
        refine ⟨24812953141130298254768285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16541968760753532169845523 24812953141130298254768285)
        ·
          refine ⟨9304857427923861845538107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24812953141130298254768285 9304857427923861845538107)
          ·
            refine ⟨13957286141885792768307161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9304857427923861845538107 13957286141885792768307161)
            ·
              refine ⟨10467964606414344576230371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13957286141885792768307161 10467964606414344576230371)
              ·
                refine ⟨15701946909621516864345557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10467964606414344576230371 15701946909621516864345557)
                ·
                  refine ⟨368014380694254301508099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15701946909621516864345557 368014380694254301508099)
                  ·
                    rfl

theorem cell23_6450349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_6450349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450349 prefixEnd_6450349 := by exact prefixLift 6450349
  have htrace : WordTrace (prefixWord ++ tailWord_6450349) baseStart_6450349 baseEnd_6450349 := by
    simpa [prefixWord, tailWord_6450349, baseEnd_6450349] using wordTrace_append hprefix tailTrace_6450349
  have hstable : (prefixWord ++ tailWord_6450349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450349).length < 2 ^ (prefixWord ++ tailWord_6450349).sum := by decide
  have hdescent : baseEnd_6450349 < baseStart_6450349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450355 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 5]
def baseStart_6450355 : Nat := 118140960795 + 6450355 * 2 ^ 59
def prefixEnd_6450355 : Nat := 4983230072969 + 3 ^ 40 * 6450355 * 2
def baseEnd_6450355 : Nat := 3312132507132215690097863

theorem tailTrace_6450355 : CollatzResearch.WordTrace tailWord_6450355 prefixEnd_6450355 3312132507132215690097863 := by
  unfold tailWord_6450355
  simp only [CollatzResearch.WordTrace]
  refine ⟨235263774546472942773632519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156842516364315295182421679 235263774546472942773632519)
  ·
    refine ⟨352895661819709414160448779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235263774546472942773632519 352895661819709414160448779)
    ·
      refine ⟨529343492729564121240673169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352895661819709414160448779 529343492729564121240673169)
      ·
        refine ⟨397007619547173090930504877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529343492729564121240673169 397007619547173090930504877)
        ·
          refine ⟨148877857330189909098939329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397007619547173090930504877 148877857330189909098939329)
          ·
            refine ⟨111658392997642431824204497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148877857330189909098939329 111658392997642431824204497)
            ·
              refine ⟨83743794748231823868153373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111658392997642431824204497 83743794748231823868153373)
              ·
                refine ⟨31403923030586933950557515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83743794748231823868153373 31403923030586933950557515)
                ·
                  refine ⟨47105884545880400925836273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31403923030586933950557515 47105884545880400925836273)
                  ·
                    refine ⟨35329413409410300694377205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47105884545880400925836273 35329413409410300694377205)
                    ·
                      refine ⟨3312132507132215690097863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35329413409410300694377205 3312132507132215690097863)
                      ·
                        rfl

theorem cell23_6450355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_6450355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450355 prefixEnd_6450355 := by exact prefixLift 6450355
  have htrace : WordTrace (prefixWord ++ tailWord_6450355) baseStart_6450355 baseEnd_6450355 := by
    simpa [prefixWord, tailWord_6450355, baseEnd_6450355] using wordTrace_append hprefix tailTrace_6450355
  have hstable : (prefixWord ++ tailWord_6450355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450355).length < 2 ^ (prefixWord ++ tailWord_6450355).sum := by decide
  have hdescent : baseEnd_6450355 < baseStart_6450355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450385 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_6450385 : Nat := 118140960795 + 6450385 * 2 ^ 59
def prefixEnd_6450385 : Nat := 4983230072969 + 3 ^ 40 * 6450385 * 2
def baseEnd_6450385 : Nat := 3312147911551850572722725

theorem tailTrace_6450385 : CollatzResearch.WordTrace tailWord_6450385 prefixEnd_6450385 3312147911551850572722725 := by
  unfold tailWord_6450385
  simp only [CollatzResearch.WordTrace]
  refine ⟨235264868736364257897224609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156843245824242838598149739 235264868736364257897224609)
  ·
    refine ⟨176448651552273193422918457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235264868736364257897224609 176448651552273193422918457)
    ·
      refine ⟨132336488664204895067188843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176448651552273193422918457 132336488664204895067188843)
      ·
        refine ⟨198504732996307342600783265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132336488664204895067188843 198504732996307342600783265)
        ·
          refine ⟨148878549747230506950587449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198504732996307342600783265 148878549747230506950587449)
          ·
            refine ⟨111658912310422880212940587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148878549747230506950587449 111658912310422880212940587)
            ·
              refine ⟨167488368465634320319410881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111658912310422880212940587 167488368465634320319410881)
              ·
                refine ⟨125616276349225740239558161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167488368465634320319410881 125616276349225740239558161)
                ·
                  refine ⟨94212207261919305179668621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125616276349225740239558161 94212207261919305179668621)
                  ·
                    refine ⟨35329577723219739442375733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94212207261919305179668621 35329577723219739442375733)
                    ·
                      refine ⟨3312147911551850572722725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35329577723219739442375733 3312147911551850572722725)
                      ·
                        rfl

theorem cell23_6450385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_6450385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450385 prefixEnd_6450385 := by exact prefixLift 6450385
  have htrace : WordTrace (prefixWord ++ tailWord_6450385) baseStart_6450385 baseEnd_6450385 := by
    simpa [prefixWord, tailWord_6450385, baseEnd_6450385] using wordTrace_append hprefix tailTrace_6450385
  have hstable : (prefixWord ++ tailWord_6450385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450385).length < 2 ^ (prefixWord ++ tailWord_6450385).sum := by decide
  have hdescent : baseEnd_6450385 < baseStart_6450385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450395 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4]
def baseStart_6450395 : Nat := 118140960795 + 6450395 * 2 ^ 59
def prefixEnd_6450395 : Nat := 4983230072969 + 3 ^ 40 * 6450395 * 2
def baseEnd_6450395 : Nat := 3312153046358395533597679

theorem tailTrace_6450395 : CollatzResearch.WordTrace tailWord_6450395 prefixEnd_6450395 3312153046358395533597679 := by
  unfold tailWord_6450395
  simp only [CollatzResearch.WordTrace]
  refine ⟨235265233466328029605088639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156843488977552019736725759 235265233466328029605088639)
  ·
    refine ⟨352897850199492044407632959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235265233466328029605088639 352897850199492044407632959)
    ·
      refine ⟨529346775299238066611449439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352897850199492044407632959 529346775299238066611449439)
      ·
        refine ⟨794020162948857099917174159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529346775299238066611449439 794020162948857099917174159)
        ·
          refine ⟨1191030244423285649875761239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794020162948857099917174159 1191030244423285649875761239)
          ·
            refine ⟨1786545366634928474813641859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191030244423285649875761239 1786545366634928474813641859)
            ·
              refine ⟨2679818049952392712220462789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1786545366634928474813641859 2679818049952392712220462789)
              ·
                refine ⟨502465884366073633541336773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2679818049952392712220462789 502465884366073633541336773)
                ·
                  refine ⟨94212353318638806289000645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502465884366073633541336773 94212353318638806289000645)
                  ·
                    refine ⟨17664816247244776179187621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94212353318638806289000645 17664816247244776179187621)
                    ·
                      refine ⟨3312153046358395533597679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17664816247244776179187621 3312153046358395533597679)
                      ·
                        rfl

theorem cell23_6450395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4].length) (baseStart_6450395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450395 prefixEnd_6450395 := by exact prefixLift 6450395
  have htrace : WordTrace (prefixWord ++ tailWord_6450395) baseStart_6450395 baseEnd_6450395 := by
    simpa [prefixWord, tailWord_6450395, baseEnd_6450395] using wordTrace_append hprefix tailTrace_6450395
  have hstable : (prefixWord ++ tailWord_6450395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450395).length < 2 ^ (prefixWord ++ tailWord_6450395).sum := by decide
  have hdescent : baseEnd_6450395 < baseStart_6450395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450436 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_6450436 : Nat := 118140960795 + 6450436 * 2 ^ 59
def prefixEnd_6450436 : Nat := 4983230072969 + 3 ^ 40 * 6450436 * 2
def baseEnd_6450436 : Nat := 3312174099065229873184991

theorem tailTrace_6450436 : CollatzResearch.WordTrace tailWord_6450436 prefixEnd_6450436 3312174099065229873184991 := by
  unfold tailWord_6450436
  simp only [CollatzResearch.WordTrace]
  refine ⟨117633364429589746803665581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156844485906119662404887441 117633364429589746803665581)
  ·
    refine ⟨44112511661096155051374593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117633364429589746803665581 44112511661096155051374593)
    ·
      refine ⟨33084383745822116288530945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44112511661096155051374593 33084383745822116288530945)
      ·
        refine ⟨24813287809366587216398209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33084383745822116288530945 24813287809366587216398209)
        ·
          refine ⟨18609965857024940412298657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24813287809366587216398209 18609965857024940412298657)
          ·
            refine ⟨13957474392768705309223993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18609965857024940412298657 13957474392768705309223993)
            ·
              refine ⟨10468105794576528981917995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13957474392768705309223993 10468105794576528981917995)
              ·
                refine ⟨15702158691864793472876993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10468105794576528981917995 15702158691864793472876993)
                ·
                  refine ⟨11776619018898595104657745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15702158691864793472876993 11776619018898595104657745)
                  ·
                    refine ⟨8832464264173946328493309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11776619018898595104657745 8832464264173946328493309)
                    ·
                      refine ⟨3312174099065229873184991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8832464264173946328493309 3312174099065229873184991)
                      ·
                        rfl

theorem cell23_6450436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_6450436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450436 prefixEnd_6450436 := by exact prefixLift 6450436
  have htrace : WordTrace (prefixWord ++ tailWord_6450436) baseStart_6450436 baseEnd_6450436 := by
    simpa [prefixWord, tailWord_6450436, baseEnd_6450436] using wordTrace_append hprefix tailTrace_6450436
  have hstable : (prefixWord ++ tailWord_6450436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450436).length < 2 ^ (prefixWord ++ tailWord_6450436).sum := by decide
  have hdescent : baseEnd_6450436 < baseStart_6450436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450493 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6450493 : Nat := 118140960795 + 6450493 * 2 ^ 59
def prefixEnd_6450493 : Nat := 4983230072969 + 3 ^ 40 * 6450493 * 2
def baseEnd_6450493 : Nat := 3312203367462536150172229

theorem tailTrace_6450493 : CollatzResearch.WordTrace tailWord_6450493 prefixEnd_6450493 3312203367462536150172229 := by
  unfold tailWord_6450493
  simp only [CollatzResearch.WordTrace]
  refine ⟨235268807819972992342156133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156845871879981994894770755 235268807819972992342156133)
  ·
    refine ⟨44112901466244936064154275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235268807819972992342156133 44112901466244936064154275)
    ·
      refine ⟨66169352199367404096231413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44112901466244936064154275 66169352199367404096231413)
      ·
        refine ⟨6203376768690694134021695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66169352199367404096231413 6203376768690694134021695)
        ·
          refine ⟨9305065153036041201032543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6203376768690694134021695 9305065153036041201032543)
          ·
            refine ⟨13957597729554061801548815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9305065153036041201032543 13957597729554061801548815)
            ·
              refine ⟨20936396594331092702323223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13957597729554061801548815 20936396594331092702323223)
              ·
                refine ⟨31404594891496639053484835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20936396594331092702323223 31404594891496639053484835)
                ·
                  refine ⟨47106892337244958580227253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31404594891496639053484835 47106892337244958580227253)
                  ·
                    refine ⟨4416271156616714866896305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47106892337244958580227253 4416271156616714866896305)
                    ·
                      refine ⟨3312203367462536150172229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416271156616714866896305 3312203367462536150172229)
                      ·
                        rfl

theorem cell23_6450493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6450493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450493 prefixEnd_6450493 := by exact prefixLift 6450493
  have htrace : WordTrace (prefixWord ++ tailWord_6450493) baseStart_6450493 baseEnd_6450493 := by
    simpa [prefixWord, tailWord_6450493, baseEnd_6450493] using wordTrace_append hprefix tailTrace_6450493
  have hstable : (prefixWord ++ tailWord_6450493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450493).length < 2 ^ (prefixWord ++ tailWord_6450493).sum := by decide
  have hdescent : baseEnd_6450493 < baseStart_6450493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450500 : List Nat := [2, 3, 4, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_6450500 : Nat := 118140960795 + 6450500 * 2 ^ 59
def prefixEnd_6450500 : Nat := 4983230072969 + 3 ^ 40 * 6450500 * 2
def baseEnd_6450500 : Nat := 3312206961827117622784697

theorem tailTrace_6450500 : CollatzResearch.WordTrace tailWord_6450500 prefixEnd_6450500 3312206961827117622784697 := by
  unfold tailWord_6450500
  simp only [CollatzResearch.WordTrace]
  refine ⟨117634531565473816268830477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156846042087298421691773969 117634531565473816268830477)
  ·
    refine ⟨44112949337052681100811429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117634531565473816268830477 44112949337052681100811429)
    ·
      refine ⟨8271178000697377706402143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44112949337052681100811429 8271178000697377706402143)
      ·
        refine ⟨12406767001046066559603215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8271178000697377706402143 12406767001046066559603215)
        ·
          refine ⟨18610150501569099839404823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12406767001046066559603215 18610150501569099839404823)
          ·
            refine ⟨27915225752353649759107235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18610150501569099839404823 27915225752353649759107235)
            ·
              refine ⟨41872838628530474638660853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27915225752353649759107235 41872838628530474638660853)
              ·
                refine ⟨3925578621424731997374455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41872838628530474638660853 3925578621424731997374455)
                ·
                  refine ⟨5888367932137097996061683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925578621424731997374455 5888367932137097996061683)
                  ·
                    refine ⟨8832551898205646994092525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5888367932137097996061683 8832551898205646994092525)
                    ·
                      refine ⟨3312206961827117622784697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8832551898205646994092525 3312206961827117622784697)
                      ·
                        rfl

theorem cell23_6450500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_6450500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450500 prefixEnd_6450500 := by exact prefixLift 6450500
  have htrace : WordTrace (prefixWord ++ tailWord_6450500) baseStart_6450500 baseEnd_6450500 := by
    simpa [prefixWord, tailWord_6450500, baseEnd_6450500] using wordTrace_append hprefix tailTrace_6450500
  have hstable : (prefixWord ++ tailWord_6450500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450500).length < 2 ^ (prefixWord ++ tailWord_6450500).sum := by decide
  have hdescent : baseEnd_6450500 < baseStart_6450500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450539 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 8, 1, 3]
def baseStart_6450539 : Nat := 118140960795 + 6450539 * 2 ^ 59
def prefixEnd_6450539 : Nat := 4983230072969 + 3 ^ 40 * 6450539 * 2
def baseEnd_6450539 : Nat := 3312226987572642970197017

theorem tailTrace_6450539 : CollatzResearch.WordTrace tailWord_6450539 prefixEnd_6450539 3312226987572642970197017 := by
  unfold tailWord_6450539
  simp only [CollatzResearch.WordTrace]
  refine ⟨235270485577806342198330671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156846990385204228132220447 235270485577806342198330671)
  ·
    refine ⟨352905728366709513297496007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235270485577806342198330671 352905728366709513297496007)
    ·
      refine ⟨529358592550064269946244011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352905728366709513297496007 529358592550064269946244011)
      ·
        refine ⟨794037888825096404919366017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529358592550064269946244011 794037888825096404919366017)
        ·
          refine ⟨595528416618822303689524513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 794037888825096404919366017 595528416618822303689524513)
          ·
            refine ⟨446646312464116727767143385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595528416618822303689524513 446646312464116727767143385)
            ·
              refine ⟨334984734348087545825357539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446646312464116727767143385 334984734348087545825357539)
              ·
                refine ⟨502477101522131318738036309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334984734348087545825357539 502477101522131318738036309)
                ·
                  refine ⟨5888403533462476391461363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 502477101522131318738036309 5888403533462476391461363)
                  ·
                    refine ⟨8832605300193714587192045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5888403533462476391461363 8832605300193714587192045)
                    ·
                      refine ⟨3312226987572642970197017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8832605300193714587192045 3312226987572642970197017)
                      ·
                        rfl

theorem cell23_6450539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 1, 3].length) (baseStart_6450539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450539 prefixEnd_6450539 := by exact prefixLift 6450539
  have htrace : WordTrace (prefixWord ++ tailWord_6450539) baseStart_6450539 baseEnd_6450539 := by
    simpa [prefixWord, tailWord_6450539, baseEnd_6450539] using wordTrace_append hprefix tailTrace_6450539
  have hstable : (prefixWord ++ tailWord_6450539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450539).length < 2 ^ (prefixWord ++ tailWord_6450539).sum := by decide
  have hdescent : baseEnd_6450539 < baseStart_6450539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450574 : List Nat := [4, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2]
def baseStart_6450574 : Nat := 118140960795 + 6450574 * 2 ^ 59
def prefixEnd_6450574 : Nat := 4983230072969 + 3 ^ 40 * 6450574 * 2
def baseEnd_6450574 : Nat := 3312244959395550333259357

theorem tailTrace_6450574 : CollatzResearch.WordTrace tailWord_6450574 prefixEnd_6450574 3312244959395550333259357 := by
  unfold tailWord_6450574
  simp only [CollatzResearch.WordTrace]
  refine ⟨29408970266584942896981847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156847841421786362117236517 29408970266584942896981847)
  ·
    refine ⟨44113455399877414345472771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29408970266584942896981847 44113455399877414345472771)
    ·
      refine ⟨66170183099816121518209157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44113455399877414345472771 66170183099816121518209157)
      ·
        refine ⟨12406909331215522784664217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66170183099816121518209157 12406909331215522784664217)
        ·
          refine ⟨9305181998411642088498163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12406909331215522784664217 9305181998411642088498163)
          ·
            refine ⟨13957772997617463132747245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9305181998411642088498163 13957772997617463132747245)
            ·
              refine ⟨5234164874106548674780217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13957772997617463132747245 5234164874106548674780217)
              ·
                refine ⟨3925623655579911506085163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5234164874106548674780217 3925623655579911506085163)
                ·
                  refine ⟨5888435483369867259127745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925623655579911506085163 5888435483369867259127745)
                  ·
                    refine ⟨4416326612527400444345809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5888435483369867259127745 4416326612527400444345809)
                    ·
                      refine ⟨3312244959395550333259357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416326612527400444345809 3312244959395550333259357)
                      ·
                        rfl

theorem cell23_6450574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_6450574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450574 prefixEnd_6450574 := by exact prefixLift 6450574
  have htrace : WordTrace (prefixWord ++ tailWord_6450574) baseStart_6450574 baseEnd_6450574 := by
    simpa [prefixWord, tailWord_6450574, baseEnd_6450574] using wordTrace_append hprefix tailTrace_6450574
  have hstable : (prefixWord ++ tailWord_6450574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450574).length < 2 ^ (prefixWord ++ tailWord_6450574).sum := by decide
  have hdescent : baseEnd_6450574 < baseStart_6450574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450596 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 1, 4, 2]
def baseStart_6450596 : Nat := 118140960795 + 6450596 * 2 ^ 59
def prefixEnd_6450596 : Nat := 4983230072969 + 3 ^ 40 * 6450596 * 2
def baseEnd_6450596 : Nat := 3312256255969949247184255

theorem tailTrace_6450596 : CollatzResearch.WordTrace tailWord_6450596 prefixEnd_6450596 3312256255969949247184255 := by
  unfold tailWord_6450596
  simp only [CollatzResearch.WordTrace]
  refine ⟨117636282269299920466577821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156848376359066560622103761 117636282269299920466577821)
  ·
    refine ⟨44113605850987470174966683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117636282269299920466577821 44113605850987470174966683)
    ·
      refine ⟨66170408776481205262450025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44113605850987470174966683 66170408776481205262450025)
      ·
        refine ⟨49627806582360903946837519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66170408776481205262450025 49627806582360903946837519)
        ·
          refine ⟨74441709873541355920256279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49627806582360903946837519 74441709873541355920256279)
          ·
            refine ⟨111662564810312033880384419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74441709873541355920256279 111662564810312033880384419)
            ·
              refine ⟨167493847215468050820576629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111662564810312033880384419 167493847215468050820576629)
              ·
                refine ⟨15702548176450129764429059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167493847215468050820576629 15702548176450129764429059)
                ·
                  refine ⟨23553822264675194646643589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15702548176450129764429059 23553822264675194646643589)
                  ·
                    refine ⟨4416341674626598996245673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23553822264675194646643589 4416341674626598996245673)
                    ·
                      refine ⟨3312256255969949247184255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416341674626598996245673 3312256255969949247184255)
                      ·
                        rfl

theorem cell23_6450596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_6450596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450596 prefixEnd_6450596 := by exact prefixLift 6450596
  have htrace : WordTrace (prefixWord ++ tailWord_6450596) baseStart_6450596 baseEnd_6450596 := by
    simpa [prefixWord, tailWord_6450596, baseEnd_6450596] using wordTrace_append hprefix tailTrace_6450596
  have hstable : (prefixWord ++ tailWord_6450596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450596).length < 2 ^ (prefixWord ++ tailWord_6450596).sum := by decide
  have hdescent : baseEnd_6450596 < baseStart_6450596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450599 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_6450599 : Nat := 118140960795 + 6450599 * 2 ^ 59
def prefixEnd_6450599 : Nat := 4983230072969 + 3 ^ 40 * 6450599 * 2
def baseEnd_6450599 : Nat := 3312257796411912735446741

theorem tailTrace_6450599 : CollatzResearch.WordTrace tailWord_6450599 prefixEnd_6450599 3312257796411912735446741 := by
  unfold tailWord_6450599
  simp only [CollatzResearch.WordTrace]
  refine ⟨235272673957588972445514851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156848449305059314963676567 235272673957588972445514851)
  ·
    refine ⟨352909010936383458668272277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235272673957588972445514851 352909010936383458668272277)
    ·
      refine ⟨16542609887642974625075263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 352909010936383458668272277 16542609887642974625075263)
      ·
        refine ⟨24813914831464461937612895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16542609887642974625075263 24813914831464461937612895)
        ·
          refine ⟨37220872247196692906419343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24813914831464461937612895 37220872247196692906419343)
          ·
            refine ⟨55831308370795039359629015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37220872247196692906419343 55831308370795039359629015)
            ·
              refine ⟨83746962556192559039443523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55831308370795039359629015 83746962556192559039443523)
              ·
                refine ⟨125620443834288838559165285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83746962556192559039443523 125620443834288838559165285)
                ·
                  refine ⟨23553833218929157229843491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125620443834288838559165285 23553833218929157229843491)
                  ·
                    refine ⟨35330749828393735844765237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23553833218929157229843491 35330749828393735844765237)
                    ·
                      refine ⟨3312257796411912735446741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35330749828393735844765237 3312257796411912735446741)
                      ·
                        rfl

theorem cell23_6450599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_6450599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450599 prefixEnd_6450599 := by exact prefixLift 6450599
  have htrace : WordTrace (prefixWord ++ tailWord_6450599) baseStart_6450599 baseEnd_6450599 := by
    simpa [prefixWord, tailWord_6450599, baseEnd_6450599] using wordTrace_append hprefix tailTrace_6450599
  have hstable : (prefixWord ++ tailWord_6450599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450599).length < 2 ^ (prefixWord ++ tailWord_6450599).sum := by decide
  have hdescent : baseEnd_6450599 < baseStart_6450599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450600 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_6450600 : Nat := 118140960795 + 6450600 * 2 ^ 59
def prefixEnd_6450600 : Nat := 4983230072969 + 3 ^ 40 * 6450600 * 2
def baseEnd_6450600 : Nat := 3312258309892567231534237

theorem tailTrace_6450600 : CollatzResearch.WordTrace tailWord_6450600 prefixEnd_6450600 3312258309892567231534237 := by
  unfold tailWord_6450600
  simp only [CollatzResearch.WordTrace]
  refine ⟨117636355215292674808150627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156848473620390233077534169 117636355215292674808150627)
  ·
    refine ⟨176454532822939012212225941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117636355215292674808150627 176454532822939012212225941)
    ·
      refine ⟨8271306226075266197448091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 176454532822939012212225941 8271306226075266197448091)
      ·
        refine ⟨12406959339112899296172137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8271306226075266197448091 12406959339112899296172137)
        ·
          refine ⟨9305219504334674472129103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12406959339112899296172137 9305219504334674472129103)
          ·
            refine ⟨13957829256502011708193655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9305219504334674472129103 13957829256502011708193655)
            ·
              refine ⟨20936743884753017562290483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13957829256502011708193655 20936743884753017562290483)
              ·
                refine ⟨31405115827129526343435725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20936743884753017562290483 31405115827129526343435725)
                ·
                  refine ⟨11776918435173572378788397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31405115827129526343435725 11776918435173572378788397)
                  ·
                    refine ⟨4416344413190089642045649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11776918435173572378788397 4416344413190089642045649)
                    ·
                      refine ⟨3312258309892567231534237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416344413190089642045649 3312258309892567231534237)
                      ·
                        rfl

theorem cell23_6450600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_6450600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450600 prefixEnd_6450600 := by exact prefixLift 6450600
  have htrace : WordTrace (prefixWord ++ tailWord_6450600) baseStart_6450600 baseEnd_6450600 := by
    simpa [prefixWord, tailWord_6450600, baseEnd_6450600] using wordTrace_append hprefix tailTrace_6450600
  have hstable : (prefixWord ++ tailWord_6450600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450600).length < 2 ^ (prefixWord ++ tailWord_6450600).sum := by decide
  have hdescent : baseEnd_6450600 < baseStart_6450600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450613 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_6450613 : Nat := 118140960795 + 6450613 * 2 ^ 59
def prefixEnd_6450613 : Nat := 4983230072969 + 3 ^ 40 * 6450613 * 2
def baseEnd_6450613 : Nat := 3312264985141075680671677

theorem tailTrace_6450613 : CollatzResearch.WordTrace tailWord_6450613 prefixEnd_6450613 3312264985141075680671677 := by
  unfold tailWord_6450613
  simp only [CollatzResearch.WordTrace]
  refine ⟨235273184579538252836524493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156848789719692168557682995 235273184579538252836524493)
  ·
    refine ⟨88227444217326844813696685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235273184579538252836524493 88227444217326844813696685)
    ·
      refine ⟨33085291581497566805136257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88227444217326844813696685 33085291581497566805136257)
      ·
        refine ⟨24813968686123175103852193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33085291581497566805136257 24813968686123175103852193)
        ·
          refine ⟨18610476514592381327889145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24813968686123175103852193 18610476514592381327889145)
          ·
            refine ⟨13957857385944285995916859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18610476514592381327889145 13957857385944285995916859)
            ·
              refine ⟨20936786078916428993875289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13957857385944285995916859 20936786078916428993875289)
              ·
                refine ⟨15702589559187321745406467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20936786078916428993875289 15702589559187321745406467)
                ·
                  refine ⟨23553884338780982618109701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15702589559187321745406467 23553884338780982618109701)
                  ·
                    refine ⟨4416353313521434240895569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23553884338780982618109701 4416353313521434240895569)
                    ·
                      refine ⟨3312264985141075680671677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416353313521434240895569 3312264985141075680671677)
                      ·
                        rfl

theorem cell23_6450613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_6450613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450613 prefixEnd_6450613 := by exact prefixLift 6450613
  have htrace : WordTrace (prefixWord ++ tailWord_6450613) baseStart_6450613 baseEnd_6450613 := by
    simpa [prefixWord, tailWord_6450613, baseEnd_6450613] using wordTrace_append hprefix tailTrace_6450613
  have hstable : (prefixWord ++ tailWord_6450613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450613).length < 2 ^ (prefixWord ++ tailWord_6450613).sum := by decide
  have hdescent : baseEnd_6450613 < baseStart_6450613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450666 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 1, 7]
def baseStart_6450666 : Nat := 118140960795 + 6450666 * 2 ^ 59
def prefixEnd_6450666 : Nat := 4983230072969 + 3 ^ 40 * 6450666 * 2
def baseEnd_6450666 : Nat := 1104097399871921324436311

theorem tailTrace_6450666 : CollatzResearch.WordTrace tailWord_6450666 prefixEnd_6450666 1104097399871921324436311 := by
  unfold tailWord_6450666
  simp only [CollatzResearch.WordTrace]
  refine ⟨58818779412086560722050963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156850078432230828592135901 58818779412086560722050963)
  ·
    refine ⟨88228169118129841083076445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58818779412086560722050963 88228169118129841083076445)
    ·
      refine ⟨33085563419298690406153667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88228169118129841083076445 33085563419298690406153667)
      ·
        refine ⟨49628345128948035609230501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33085563419298690406153667 49628345128948035609230501)
        ·
          refine ⟨9305314711677756676730719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49628345128948035609230501 9305314711677756676730719)
          ·
            refine ⟨13957972067516635015096079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9305314711677756676730719 13957972067516635015096079)
            ·
              refine ⟨20936958101274952522644119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13957972067516635015096079 20936958101274952522644119)
              ·
                refine ⟨31405437151912428783966179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20936958101274952522644119 31405437151912428783966179)
                ·
                  refine ⟨47108155727868643175949269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31405437151912428783966179 47108155727868643175949269)
                  ·
                    refine ⟨1104097399871921324436311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47108155727868643175949269 1104097399871921324436311)
                    ·
                      rfl

theorem cell23_6450666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_6450666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450666 prefixEnd_6450666 := by exact prefixLift 6450666
  have htrace : WordTrace (prefixWord ++ tailWord_6450666) baseStart_6450666 baseEnd_6450666 := by
    simpa [prefixWord, tailWord_6450666, baseEnd_6450666] using wordTrace_append hprefix tailTrace_6450666
  have hstable : (prefixWord ++ tailWord_6450666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450666).length < 2 ^ (prefixWord ++ tailWord_6450666).sum := by decide
  have hdescent : baseEnd_6450666 < baseStart_6450666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450696 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 3, 4]
def baseStart_6450696 : Nat := 118140960795 + 6450696 * 2 ^ 59
def prefixEnd_6450696 : Nat := 4983230072969 + 3 ^ 40 * 6450696 * 2
def baseEnd_6450696 : Nat := 1104102534678466285311265

theorem tailTrace_6450696 : CollatzResearch.WordTrace tailWord_6450696 prefixEnd_6450696 1104102534678466285311265 := by
  unfold tailWord_6450696
  simp only [CollatzResearch.WordTrace]
  refine ⟨117638105919118779005897971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156850807892158372007863961 117638105919118779005897971)
  ·
    refine ⟨176457158878678168508846957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117638105919118779005897971 176457158878678168508846957)
    ·
      refine ⟨66171434579504313190817609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176457158878678168508846957 66171434579504313190817609)
      ·
        refine ⟨49628575934628234893113207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66171434579504313190817609 49628575934628234893113207)
        ·
          refine ⟨74442863901942352339669811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49628575934628234893113207 74442863901942352339669811)
          ·
            refine ⟨111664295852913528509504717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74442863901942352339669811 111664295852913528509504717)
            ·
              refine ⟨41874110944842573191064269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111664295852913528509504717 41874110944842573191064269)
              ·
                refine ⟨15702791604315964946649101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41874110944842573191064269 15702791604315964946649101)
                ·
                  refine ⟨5888546851618486854993413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15702791604315964946649101 5888546851618486854993413)
                  ·
                    refine ⟨1104102534678466285311265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5888546851618486854993413 1104102534678466285311265)
                    ·
                      rfl

theorem cell23_6450696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_6450696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450696 prefixEnd_6450696 := by exact prefixLift 6450696
  have htrace : WordTrace (prefixWord ++ tailWord_6450696) baseStart_6450696 baseEnd_6450696 := by
    simpa [prefixWord, tailWord_6450696, baseEnd_6450696] using wordTrace_append hprefix tailTrace_6450696
  have hstable : (prefixWord ++ tailWord_6450696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450696).length < 2 ^ (prefixWord ++ tailWord_6450696).sum := by decide
  have hdescent : baseEnd_6450696 < baseStart_6450696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450774 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_6450774 : Nat := 118140960795 + 6450774 * 2 ^ 59
def prefixEnd_6450774 : Nat := 4983230072969 + 3 ^ 40 * 6450774 * 2
def baseEnd_6450774 : Nat := 3312347655526449550758437

theorem tailTrace_6450774 : CollatzResearch.WordTrace tailWord_6450774 prefixEnd_6450774 3312347655526449550758437 := by
  unfold tailWord_6450774
  simp only [CollatzResearch.WordTrace]
  refine ⟨14704941045747186083320961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156852704487969984888756917 14704941045747186083320961)
  ·
    refine ⟨11028705784310389562490721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14704941045747186083320961 11028705784310389562490721)
    ·
      refine ⟨8271529338232792171868041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11028705784310389562490721 8271529338232792171868041)
      ·
        refine ⟨6203647003674594128901031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8271529338232792171868041 6203647003674594128901031)
        ·
          refine ⟨9305470505511891193351547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6203647003674594128901031 9305470505511891193351547)
          ·
            refine ⟨13958205758267836790027321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9305470505511891193351547 13958205758267836790027321)
            ·
              refine ⟨10468654318700877592520491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13958205758267836790027321 10468654318700877592520491)
              ·
                refine ⟨15702981478051316388780737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10468654318700877592520491 15702981478051316388780737)
                ·
                  refine ⟨11777236108538487291585553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15702981478051316388780737 11777236108538487291585553)
                  ·
                    refine ⟨8832927081403865468689165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11777236108538487291585553 8832927081403865468689165)
                    ·
                      refine ⟨3312347655526449550758437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8832927081403865468689165 3312347655526449550758437)
                      ·
                        rfl

theorem cell23_6450774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_6450774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450774 prefixEnd_6450774 := by exact prefixLift 6450774
  have htrace : WordTrace (prefixWord ++ tailWord_6450774) baseStart_6450774 baseEnd_6450774 := by
    simpa [prefixWord, tailWord_6450774, baseEnd_6450774] using wordTrace_append hprefix tailTrace_6450774
  have hstable : (prefixWord ++ tailWord_6450774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450774).length < 2 ^ (prefixWord ++ tailWord_6450774).sum := by decide
  have hdescent : baseEnd_6450774 < baseStart_6450774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450780 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_6450780 : Nat := 118140960795 + 6450780 * 2 ^ 59
def prefixEnd_6450780 : Nat := 4983230072969 + 3 ^ 40 * 6450780 * 2
def baseEnd_6450780 : Nat := 3312350736410376527283409

theorem tailTrace_6450780 : CollatzResearch.WordTrace tailWord_6450780 prefixEnd_6450780 3312350736410376527283409 := by
  unfold tailWord_6450780
  simp only [CollatzResearch.WordTrace]
  refine ⟨117639637784966620178926897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156852850379955493571902529 117639637784966620178926897)
  ·
    refine ⟨88229728338724965134195173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117639637784966620178926897 88229728338724965134195173)
    ·
      refine ⟨16543074063510930962661595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88229728338724965134195173 16543074063510930962661595)
      ·
        refine ⟨24814611095266396443992393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16543074063510930962661595 24814611095266396443992393)
        ·
          refine ⟨18610958321449797332994295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24814611095266396443992393 18610958321449797332994295)
          ·
            refine ⟨27916437482174695999491443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18610958321449797332994295 27916437482174695999491443)
            ·
              refine ⟨41874656223262043999237165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27916437482174695999491443 41874656223262043999237165)
              ·
                refine ⟨15702996083723266499713937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41874656223262043999237165 15702996083723266499713937)
                ·
                  refine ⟨11777247062792449874785453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15702996083723266499713937 11777247062792449874785453)
                  ·
                    refine ⟨4416467648547168703044545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11777247062792449874785453 4416467648547168703044545)
                    ·
                      refine ⟨3312350736410376527283409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416467648547168703044545 3312350736410376527283409)
                      ·
                        rfl

theorem cell23_6450780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_6450780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450780 prefixEnd_6450780 := by exact prefixLift 6450780
  have htrace : WordTrace (prefixWord ++ tailWord_6450780) baseStart_6450780 baseEnd_6450780 := by
    simpa [prefixWord, tailWord_6450780, baseEnd_6450780] using wordTrace_append hprefix tailTrace_6450780
  have hstable : (prefixWord ++ tailWord_6450780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450780).length < 2 ^ (prefixWord ++ tailWord_6450780).sum := by decide
  have hdescent : baseEnd_6450780 < baseStart_6450780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450813 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_6450813 : Nat := 118140960795 + 6450813 * 2 ^ 59
def prefixEnd_6450813 : Nat := 4983230072969 + 3 ^ 40 * 6450813 * 2
def baseEnd_6450813 : Nat := 3312367681271974898170757

theorem tailTrace_6450813 : CollatzResearch.WordTrace tailWord_6450813 prefixEnd_6450813 3312367681271974898170757 := by
  unfold tailWord_6450813
  simp only [CollatzResearch.WordTrace]
  refine ⟨235280479178813686993805093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156853652785875791329203395 235280479178813686993805093)
  ·
    refine ⟨44115089846027566311338455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235280479178813686993805093 44115089846027566311338455)
    ·
      refine ⟨66172634769041349467007683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44115089846027566311338455 66172634769041349467007683)
      ·
        refine ⟨99258952153562024200511525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66172634769041349467007683 99258952153562024200511525)
        ·
          refine ⟨18611053528792879537595911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99258952153562024200511525 18611053528792879537595911)
          ·
            refine ⟨27916580293189319306393867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18611053528792879537595911 27916580293189319306393867)
            ·
              refine ⟨41874870439783978959590801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27916580293189319306393867 41874870439783978959590801)
              ·
                refine ⟨31406152829837984219693101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41874870439783978959590801 31406152829837984219693101)
                ·
                  refine ⟨11777307311189244082384913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31406152829837984219693101 11777307311189244082384913)
                  ·
                    refine ⟨8832980483391933061788685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11777307311189244082384913 8832980483391933061788685)
                    ·
                      refine ⟨3312367681271974898170757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8832980483391933061788685 3312367681271974898170757)
                      ·
                        rfl

theorem cell23_6450813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_6450813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450813 prefixEnd_6450813 := by exact prefixLift 6450813
  have htrace : WordTrace (prefixWord ++ tailWord_6450813) baseStart_6450813 baseEnd_6450813 := by
    simpa [prefixWord, tailWord_6450813, baseEnd_6450813] using wordTrace_append hprefix tailTrace_6450813
  have hstable : (prefixWord ++ tailWord_6450813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450813).length < 2 ^ (prefixWord ++ tailWord_6450813).sum := by decide
  have hdescent : baseEnd_6450813 < baseStart_6450813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450823 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_6450823 : Nat := 118140960795 + 6450823 * 2 ^ 59
def prefixEnd_6450823 : Nat := 4983230072969 + 3 ^ 40 * 6450823 * 2
def baseEnd_6450823 : Nat := 3312372816078519859045711

theorem tailTrace_6450823 : CollatzResearch.WordTrace tailWord_6450823 prefixEnd_6450823 3312372816078519859045711 := by
  unfold tailWord_6450823
  simp only [CollatzResearch.WordTrace]
  refine ⟨235280843908777458701669123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156853895939184972467779415 235280843908777458701669123)
  ·
    refine ⟨352921265863166188052503685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235280843908777458701669123 352921265863166188052503685)
    ·
      refine ⟨66172737349343660259844441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 352921265863166188052503685 66172737349343660259844441)
      ·
        refine ⟨49629553012007745194883331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66172737349343660259844441 49629553012007745194883331)
        ·
          refine ⟨74444329518011617792324997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49629553012007745194883331 74444329518011617792324997)
          ·
            refine ⟨13958311784627178336060937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74444329518011617792324997 13958311784627178336060937)
            ·
              refine ⟨10468733838470383752045703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13958311784627178336060937 10468733838470383752045703)
              ·
                refine ⟨15703100757705575628068555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10468733838470383752045703 15703100757705575628068555)
                ·
                  refine ⟨23554651136558363442102833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15703100757705575628068555 23554651136558363442102833)
                  ·
                    refine ⟨17665988352418772581577125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23554651136558363442102833 17665988352418772581577125)
                    ·
                      refine ⟨3312372816078519859045711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17665988352418772581577125 3312372816078519859045711)
                      ·
                        rfl

theorem cell23_6450823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_6450823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450823 prefixEnd_6450823 := by exact prefixLift 6450823
  have htrace : WordTrace (prefixWord ++ tailWord_6450823) baseStart_6450823 baseEnd_6450823 := by
    simpa [prefixWord, tailWord_6450823, baseEnd_6450823] using wordTrace_append hprefix tailTrace_6450823
  have hstable : (prefixWord ++ tailWord_6450823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450823).length < 2 ^ (prefixWord ++ tailWord_6450823).sum := by decide
  have hdescent : baseEnd_6450823 < baseStart_6450823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450844 : List Nat := [2, 2, 3, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_6450844 : Nat := 118140960795 + 6450844 * 2 ^ 59
def prefixEnd_6450844 : Nat := 4983230072969 + 3 ^ 40 * 6450844 * 2
def baseEnd_6450844 : Nat := 3312383599172264276883115

theorem tailTrace_6450844 : CollatzResearch.WordTrace tailWord_6450844 prefixEnd_6450844 3312383599172264276883115 := by
  unfold tailWord_6450844
  simp only [CollatzResearch.WordTrace]
  refine ⟨117640804920850689644091793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156854406561134252858789057 117640804920850689644091793)
  ·
    refine ⟨88230603690638017233068845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117640804920850689644091793 88230603690638017233068845)
    ·
      refine ⟨33086476383989256462400817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88230603690638017233068845 33086476383989256462400817)
      ·
        refine ⟨24814857287991942346800613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33086476383989256462400817 24814857287991942346800613)
        ·
          refine ⟨4652785741498489190025115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24814857287991942346800613 4652785741498489190025115)
          ·
            refine ⟨6979178612247733785037673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4652785741498489190025115 6979178612247733785037673)
            ·
              refine ⟨5234383959185800338778255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6979178612247733785037673 5234383959185800338778255)
              ·
                refine ⟨7851575938778700508167383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234383959185800338778255 7851575938778700508167383)
                ·
                  refine ⟨11777363908168050762251075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7851575938778700508167383 11777363908168050762251075)
                  ·
                    refine ⟨17666045862252076143376613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11777363908168050762251075 17666045862252076143376613)
                    ·
                      refine ⟨3312383599172264276883115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17666045862252076143376613 3312383599172264276883115)
                      ·
                        rfl

theorem cell23_6450844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_6450844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450844 prefixEnd_6450844 := by exact prefixLift 6450844
  have htrace : WordTrace (prefixWord ++ tailWord_6450844) baseStart_6450844 baseEnd_6450844 := by
    simpa [prefixWord, tailWord_6450844, baseEnd_6450844] using wordTrace_append hprefix tailTrace_6450844
  have hstable : (prefixWord ++ tailWord_6450844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450844).length < 2 ^ (prefixWord ++ tailWord_6450844).sum := by decide
  have hdescent : baseEnd_6450844 < baseStart_6450844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450847 : List Nat := [1, 1, 2, 7, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6450847 : Nat := 118140960795 + 6450847 * 2 ^ 59
def prefixEnd_6450847 : Nat := 4983230072969 + 3 ^ 40 * 6450847 * 2
def baseEnd_6450847 : Nat := 3312385139614227765145601

theorem tailTrace_6450847 : CollatzResearch.WordTrace tailWord_6450847 prefixEnd_6450847 3312385139614227765145601 := by
  unfold tailWord_6450847
  simp only [CollatzResearch.WordTrace]
  refine ⟨235281719260690510800542795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156854479507127007200361863 235281719260690510800542795)
  ·
    refine ⟨352922578891035766200814193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235281719260690510800542795 352922578891035766200814193)
    ·
      refine ⟨264691934168276824650610645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352922578891035766200814193 264691934168276824650610645)
      ·
        refine ⟨6203717207068988077748687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 264691934168276824650610645 6203717207068988077748687)
        ·
          refine ⟨9305575810603482116623031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6203717207068988077748687 9305575810603482116623031)
          ·
            refine ⟨13958363715905223174934547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9305575810603482116623031 13958363715905223174934547)
            ·
              refine ⟨20937545573857834762401821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13958363715905223174934547 20937545573857834762401821)
              ·
                refine ⟨7851579590196688035900683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20937545573857834762401821 7851579590196688035900683)
                ·
                  refine ⟨11777369385295032053851025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7851579590196688035900683 11777369385295032053851025)
                  ·
                    refine ⟨8833027038971274040388269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11777369385295032053851025 8833027038971274040388269)
                    ·
                      refine ⟨3312385139614227765145601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8833027038971274040388269 3312385139614227765145601)
                      ·
                        rfl

theorem cell23_6450847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6450847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450847 prefixEnd_6450847 := by exact prefixLift 6450847
  have htrace : WordTrace (prefixWord ++ tailWord_6450847) baseStart_6450847 baseEnd_6450847 := by
    simpa [prefixWord, tailWord_6450847, baseEnd_6450847] using wordTrace_append hprefix tailTrace_6450847
  have hstable : (prefixWord ++ tailWord_6450847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450847).length < 2 ^ (prefixWord ++ tailWord_6450847).sum := by decide
  have hdescent : baseEnd_6450847 < baseStart_6450847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450866 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_6450866 : Nat := 118140960795 + 6450866 * 2 ^ 59
def prefixEnd_6450866 : Nat := 4983230072969 + 3 ^ 40 * 6450866 * 2
def baseEnd_6450866 : Nat := 3312394895746663190808013

theorem tailTrace_6450866 : CollatzResearch.WordTrace tailWord_6450866 prefixEnd_6450866 3312394895746663190808013 := by
  unfold tailWord_6450866
  simp only [CollatzResearch.WordTrace]
  refine ⟨58820603061905419261371113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156854941498414451363656301 58820603061905419261371113)
  ·
    refine ⟨44115452296429064446028335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58820603061905419261371113 44115452296429064446028335)
    ·
      refine ⟨66173178444643596669042503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44115452296429064446028335 66173178444643596669042503)
      ·
        refine ⟨99259767666965395003563755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66173178444643596669042503 99259767666965395003563755)
        ·
          refine ⟨148889651500448092505345633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99259767666965395003563755 148889651500448092505345633)
          ·
            refine ⟨111667238625336069379009225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148889651500448092505345633 111667238625336069379009225)
            ·
              refine ⟨83750428969002052034256919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111667238625336069379009225 83750428969002052034256919)
              ·
                refine ⟨125625643453503078051385379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83750428969002052034256919 125625643453503078051385379)
                ·
                  refine ⟨188438465180254617077078069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125625643453503078051385379 188438465180254617077078069)
                  ·
                    refine ⟨17666106110648870350976069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 188438465180254617077078069 17666106110648870350976069)
                    ·
                      refine ⟨3312394895746663190808013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17666106110648870350976069 3312394895746663190808013)
                      ·
                        rfl

theorem cell23_6450866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_6450866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450866 prefixEnd_6450866 := by exact prefixLift 6450866
  have htrace : WordTrace (prefixWord ++ tailWord_6450866) baseStart_6450866 baseEnd_6450866 := by
    simpa [prefixWord, tailWord_6450866, baseEnd_6450866] using wordTrace_append hprefix tailTrace_6450866
  have hstable : (prefixWord ++ tailWord_6450866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450866).length < 2 ^ (prefixWord ++ tailWord_6450866).sum := by decide
  have hdescent : baseEnd_6450866 < baseStart_6450866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450877 : List Nat := [1, 4, 1, 2, 1, 2, 5, 1, 2, 1, 3]
def baseStart_6450877 : Nat := 118140960795 + 6450877 * 2 ^ 59
def prefixEnd_6450877 : Nat := 4983230072969 + 3 ^ 40 * 6450877 * 2
def baseEnd_6450877 : Nat := 3312400544033862647770463

theorem tailTrace_6450877 : CollatzResearch.WordTrace tailWord_6450877 prefixEnd_6450877 3312400544033862647770463 := by
  unfold tailWord_6450877
  simp only [CollatzResearch.WordTrace]
  refine ⟨235282813450581825924134885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156855208967054550616089923 235282813450581825924134885)
  ·
    refine ⟨44115527521984092360775291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235282813450581825924134885 44115527521984092360775291)
    ·
      refine ⟨66173291282976138541162937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44115527521984092360775291 66173291282976138541162937)
      ·
        refine ⟨49629968462232103905872203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66173291282976138541162937 49629968462232103905872203)
        ·
          refine ⟨74444952693348155858808305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49629968462232103905872203 74444952693348155858808305)
          ·
            refine ⟨55833714520011116894106229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74444952693348155858808305 55833714520011116894106229)
            ·
              refine ⟨5234410736251042208822459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55833714520011116894106229 5234410736251042208822459)
              ·
                refine ⟨7851616104376563313233689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234410736251042208822459 7851616104376563313233689)
                ·
                  refine ⟨5888712078282422484925267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7851616104376563313233689 5888712078282422484925267)
                  ·
                    refine ⟨8833068117423633727387901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5888712078282422484925267 8833068117423633727387901)
                    ·
                      refine ⟨3312400544033862647770463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8833068117423633727387901 3312400544033862647770463)
                      ·
                        rfl

theorem cell23_6450877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_6450877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450877 prefixEnd_6450877 := by exact prefixLift 6450877
  have htrace : WordTrace (prefixWord ++ tailWord_6450877) baseStart_6450877 baseEnd_6450877 := by
    simpa [prefixWord, tailWord_6450877, baseEnd_6450877] using wordTrace_append hprefix tailTrace_6450877
  have hstable : (prefixWord ++ tailWord_6450877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450877).length < 2 ^ (prefixWord ++ tailWord_6450877).sum := by decide
  have hdescent : baseEnd_6450877 < baseStart_6450877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450896 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 4]
def baseStart_6450896 : Nat := 118140960795 + 6450896 * 2 ^ 59
def prefixEnd_6450896 : Nat := 4983230072969 + 3 ^ 40 * 6450896 * 2
def baseEnd_6450896 : Nat := 3312410300166298073432875

theorem tailTrace_6450896 : CollatzResearch.WordTrace tailWord_6450896 prefixEnd_6450896 3312410300166298073432875 := by
  unfold tailWord_6450896
  simp only [CollatzResearch.WordTrace]
  refine ⟨117641753218756496084538271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156855670958341994779384361 117641753218756496084538271)
  ·
    refine ⟨176462629828134744126807407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117641753218756496084538271 176462629828134744126807407)
    ·
      refine ⟨264693944742202116190211111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176462629828134744126807407 264693944742202116190211111)
      ·
        refine ⟨397040917113303174285316667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264693944742202116190211111 397040917113303174285316667)
        ·
          refine ⟨595561375669954761427975001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397040917113303174285316667 595561375669954761427975001)
          ·
            refine ⟨446671031752466071070981251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595561375669954761427975001 446671031752466071070981251)
            ·
              refine ⟨670006547628699106606471877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446671031752466071070981251 670006547628699106606471877)
              ·
                refine ⟨125626227680381082488713477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 670006547628699106606471877 125626227680381082488713477)
                ·
                  refine ⟨23554917690071452966633777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125626227680381082488713477 23554917690071452966633777)
                  ·
                    refine ⟨17666188267553589724975333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23554917690071452966633777 17666188267553589724975333)
                    ·
                      refine ⟨3312410300166298073432875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17666188267553589724975333 3312410300166298073432875)
                      ·
                        rfl

theorem cell23_6450896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_6450896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450896 prefixEnd_6450896 := by exact prefixLift 6450896
  have htrace : WordTrace (prefixWord ++ tailWord_6450896) baseStart_6450896 baseEnd_6450896 := by
    simpa [prefixWord, tailWord_6450896, baseEnd_6450896] using wordTrace_append hprefix tailTrace_6450896
  have hstable : (prefixWord ++ tailWord_6450896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450896).length < 2 ^ (prefixWord ++ tailWord_6450896).sum := by decide
  have hdescent : baseEnd_6450896 < baseStart_6450896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450916 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_6450916 : Nat := 118140960795 + 6450916 * 2 ^ 59
def prefixEnd_6450916 : Nat := 4983230072969 + 3 ^ 40 * 6450916 * 2
def baseEnd_6450916 : Nat := 3312420569779387995182783

theorem tailTrace_6450916 : CollatzResearch.WordTrace tailWord_6450916 prefixEnd_6450916 3312420569779387995182783 := by
  unfold tailWord_6450916
  simp only [CollatzResearch.WordTrace]
  refine ⟨117642117948720267792402301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156856157264960357056536401 117642117948720267792402301)
  ·
    refine ⟨44115794230770100422150863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117642117948720267792402301 44115794230770100422150863)
    ·
      refine ⟨66173691346155150633226295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44115794230770100422150863 66173691346155150633226295)
      ·
        refine ⟨99260537019232725949839443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66173691346155150633226295 99260537019232725949839443)
        ·
          refine ⟨148890805528849088924759165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99260537019232725949839443 148890805528849088924759165)
          ·
            refine ⟨55834052073318408346784687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148890805528849088924759165 55834052073318408346784687)
            ·
              refine ⟨83751078109977612520177031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55834052073318408346784687 83751078109977612520177031)
              ·
                refine ⟨125626617164966418780265547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83751078109977612520177031 125626617164966418780265547)
                ·
                  refine ⟨188439925747449628170398321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125626617164966418780265547 188439925747449628170398321)
                  ·
                    refine ⟨141329944310587221127798741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188439925747449628170398321 141329944310587221127798741)
                    ·
                      refine ⟨3312420569779387995182783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141329944310587221127798741 3312420569779387995182783)
                      ·
                        rfl

theorem cell23_6450916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_6450916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450916 prefixEnd_6450916 := by exact prefixLift 6450916
  have htrace : WordTrace (prefixWord ++ tailWord_6450916) baseStart_6450916 baseEnd_6450916 := by
    simpa [prefixWord, tailWord_6450916, baseEnd_6450916] using wordTrace_append hprefix tailTrace_6450916
  have hstable : (prefixWord ++ tailWord_6450916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450916).length < 2 ^ (prefixWord ++ tailWord_6450916).sum := by decide
  have hdescent : baseEnd_6450916 < baseStart_6450916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450917 : List Nat := [1, 3, 1, 4, 1, 1, 2, 4, 2, 2, 2]
def baseStart_6450917 : Nat := 118140960795 + 6450917 * 2 ^ 59
def prefixEnd_6450917 : Nat := 4983230072969 + 3 ^ 40 * 6450917 * 2
def baseEnd_6450917 : Nat := 3312421083260042491270279

theorem tailTrace_6450917 : CollatzResearch.WordTrace tailWord_6450917 prefixEnd_6450917 3312421083260042491270279 := by
  unfold tailWord_6450917
  simp only [CollatzResearch.WordTrace]
  refine ⟨235284272370436912755591005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156856181580291275170394003 235284272370436912755591005)
  ·
    refine ⟨88231602138913842283346627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235284272370436912755591005 88231602138913842283346627)
    ·
      refine ⟨132347403208370763425019941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88231602138913842283346627 132347403208370763425019941)
      ·
        refine ⟨24815138101569518142191239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132347403208370763425019941 24815138101569518142191239)
        ·
          refine ⟨37222707152354277213286859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24815138101569518142191239 37222707152354277213286859)
          ·
            refine ⟨55834060728531415819930289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37222707152354277213286859 55834060728531415819930289)
            ·
              refine ⟨41875545546398561864947717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55834060728531415819930289 41875545546398561864947717)
              ·
                refine ⟨7851664789949730349677697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41875545546398561864947717 7851664789949730349677697)
                ·
                  refine ⟨5888748592462297762258273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7851664789949730349677697 5888748592462297762258273)
                  ·
                    refine ⟨4416561444346723321693705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5888748592462297762258273 4416561444346723321693705)
                    ·
                      refine ⟨3312421083260042491270279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416561444346723321693705 3312421083260042491270279)
                      ·
                        rfl

theorem cell23_6450917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_6450917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450917 prefixEnd_6450917 := by exact prefixLift 6450917
  have htrace : WordTrace (prefixWord ++ tailWord_6450917) baseStart_6450917 baseEnd_6450917 := by
    simpa [prefixWord, tailWord_6450917, baseEnd_6450917] using wordTrace_append hprefix tailTrace_6450917
  have hstable : (prefixWord ++ tailWord_6450917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450917).length < 2 ^ (prefixWord ++ tailWord_6450917).sum := by decide
  have hdescent : baseEnd_6450917 < baseStart_6450917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450923 : List Nat := [1, 1, 1, 1, 2, 4, 2, 6, 5]
def baseStart_6450923 : Nat := 118140960795 + 6450923 * 2 ^ 59
def prefixEnd_6450923 : Nat := 4983230072969 + 3 ^ 40 * 6450923 * 2
def baseEnd_6450923 : Nat := 368047129349329940866139

theorem tailTrace_6450923 : CollatzResearch.WordTrace tailWord_6450923 prefixEnd_6450923 368047129349329940866139 := by
  unfold tailWord_6450923
  simp only [CollatzResearch.WordTrace]
  refine ⟨235284491208415175780309423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156856327472276783853539615 235284491208415175780309423)
  ·
    refine ⟨352926736812622763670464135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235284491208415175780309423 352926736812622763670464135)
    ·
      refine ⟨529390105218934145505696203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352926736812622763670464135 529390105218934145505696203)
      ·
        refine ⟨794085157828401218258544305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529390105218934145505696203 794085157828401218258544305)
        ·
          refine ⟨595563868371300913693908229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 794085157828401218258544305 595563868371300913693908229)
          ·
            refine ⟨111668225319618921317607793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 595563868371300913693908229 111668225319618921317607793)
            ·
              refine ⟨83751168989714190988205845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111668225319618921317607793 83751168989714190988205845)
              ·
                refine ⟨3925836046392852702572149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83751168989714190988205845 3925836046392852702572149)
                ·
                  refine ⟨368047129349329940866139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3925836046392852702572149 368047129349329940866139)
                  ·
                    rfl

theorem cell23_6450923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 5].length) (baseStart_6450923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450923 prefixEnd_6450923 := by exact prefixLift 6450923
  have htrace : WordTrace (prefixWord ++ tailWord_6450923) baseStart_6450923 baseEnd_6450923 := by
    simpa [prefixWord, tailWord_6450923, baseEnd_6450923] using wordTrace_append hprefix tailTrace_6450923
  have hstable : (prefixWord ++ tailWord_6450923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450923).length < 2 ^ (prefixWord ++ tailWord_6450923).sum := by decide
  have hdescent : baseEnd_6450923 < baseStart_6450923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450934 : List Nat := [5, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_6450934 : Nat := 118140960795 + 6450934 * 2 ^ 59
def prefixEnd_6450934 : Nat := 4983230072969 + 3 ^ 40 * 6450934 * 2
def baseEnd_6450934 : Nat := 3312429812431168924757701

theorem tailTrace_6450934 : CollatzResearch.WordTrace tailWord_6450934 prefixEnd_6450934 3312429812431168924757701 := by
  unfold tailWord_6450934
  simp only [CollatzResearch.WordTrace]
  refine ⟨14705305775710957791184991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156856594940916883105973237 14705305775710957791184991)
  ·
    refine ⟨22057958663566436686777487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14705305775710957791184991 22057958663566436686777487)
    ·
      refine ⟨33086937995349655030166231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22057958663566436686777487 33086937995349655030166231)
      ·
        refine ⟨49630406993024482545249347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33086937995349655030166231 49630406993024482545249347)
        ·
          refine ⟨74445610489536723817874021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49630406993024482545249347 74445610489536723817874021)
          ·
            refine ⟨13958551966788135715851379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74445610489536723817874021 13958551966788135715851379)
            ·
              refine ⟨20937827950182203573777069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13958551966788135715851379 20937827950182203573777069)
              ·
                refine ⟨7851685481318326340166401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20937827950182203573777069 7851685481318326340166401)
                ·
                  refine ⟨5888764110988744755124801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7851685481318326340166401 5888764110988744755124801)
                  ·
                    refine ⟨4416573083241558566343601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5888764110988744755124801 4416573083241558566343601)
                    ·
                      refine ⟨3312429812431168924757701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416573083241558566343601 3312429812431168924757701)
                      ·
                        rfl

theorem cell23_6450934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_6450934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450934 prefixEnd_6450934 := by exact prefixLift 6450934
  have htrace : WordTrace (prefixWord ++ tailWord_6450934) baseStart_6450934 baseEnd_6450934 := by
    simpa [prefixWord, tailWord_6450934, baseEnd_6450934] using wordTrace_append hprefix tailTrace_6450934
  have hstable : (prefixWord ++ tailWord_6450934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450934).length < 2 ^ (prefixWord ++ tailWord_6450934).sum := by decide
  have hdescent : baseEnd_6450934 < baseStart_6450934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450936 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 1, 7]
def baseStart_6450936 : Nat := 118140960795 + 6450936 * 2 ^ 59
def prefixEnd_6450936 : Nat := 4983230072969 + 3 ^ 40 * 6450936 * 2
def baseEnd_6450936 : Nat := 1104143613130825972310897

theorem tailTrace_6450936 : CollatzResearch.WordTrace tailWord_6450936 prefixEnd_6450936 1104143613130825972310897 := by
  unfold tailWord_6450936
  simp only [CollatzResearch.WordTrace]
  refine ⟨117642482678684039500266331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156856643571578719333688441 117642482678684039500266331)
  ·
    refine ⟨176463724018026059250399497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117642482678684039500266331 176463724018026059250399497)
    ·
      refine ⟨132347793013519544437799623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176463724018026059250399497 132347793013519544437799623)
      ·
        refine ⟨198521689520279316656699435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132347793013519544437799623 198521689520279316656699435)
        ·
          refine ⟨297782534280418974985049153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198521689520279316656699435 297782534280418974985049153)
          ·
            refine ⟨223336900710314231238786865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297782534280418974985049153 223336900710314231238786865)
            ·
              refine ⟨167502675532735673429090149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223336900710314231238786865 167502675532735673429090149)
              ·
                refine ⟨31406751662387938767954403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167502675532735673429090149 31406751662387938767954403)
                ·
                  refine ⟨47110127493581908151931605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31406751662387938767954403 47110127493581908151931605)
                  ·
                    refine ⟨1104143613130825972310897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47110127493581908151931605 1104143613130825972310897)
                    ·
                      rfl

theorem cell23_6450936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_6450936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450936 prefixEnd_6450936 := by exact prefixLift 6450936
  have htrace : WordTrace (prefixWord ++ tailWord_6450936) baseStart_6450936 baseEnd_6450936 := by
    simpa [prefixWord, tailWord_6450936, baseEnd_6450936] using wordTrace_append hprefix tailTrace_6450936
  have hstable : (prefixWord ++ tailWord_6450936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450936).length < 2 ^ (prefixWord ++ tailWord_6450936).sum := by decide
  have hdescent : baseEnd_6450936 < baseStart_6450936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451000 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 3, 4]
def baseStart_6451000 : Nat := 118140960795 + 6451000 * 2 ^ 59
def prefixEnd_6451000 : Nat := 4983230072969 + 3 ^ 40 * 6451000 * 2
def baseEnd_6451000 : Nat := 1104154567384788555510799

theorem tailTrace_6451000 : CollatzResearch.WordTrace tailWord_6451000 prefixEnd_6451000 1104154567384788555510799 := by
  unfold tailWord_6451000
  simp only [CollatzResearch.WordTrace]
  refine ⟨117643649814568108965431227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156858199752757478620574969 117643649814568108965431227)
  ·
    refine ⟨176465474721852163448146841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117643649814568108965431227 176465474721852163448146841)
    ·
      refine ⟨132349106041389122586110131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176465474721852163448146841 132349106041389122586110131)
      ·
        refine ⟨198523659062083683879165197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132349106041389122586110131 198523659062083683879165197)
        ·
          refine ⟨74446372148281381454686949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198523659062083683879165197 74446372148281381454686949)
          ·
            refine ⟨13958694777802759022753803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74446372148281381454686949 13958694777802759022753803)
            ·
              refine ⟨20938042166704138534130705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13958694777802759022753803 20938042166704138534130705)
              ·
                refine ⟨15703531625028103900598029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20938042166704138534130705 15703531625028103900598029)
                ·
                  refine ⟨5888824359385538962724261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15703531625028103900598029 5888824359385538962724261)
                  ·
                    refine ⟨1104154567384788555510799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5888824359385538962724261 1104154567384788555510799)
                    ·
                      rfl

theorem cell23_6451000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_6451000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451000 prefixEnd_6451000 := by exact prefixLift 6451000
  have htrace : WordTrace (prefixWord ++ tailWord_6451000) baseStart_6451000 baseEnd_6451000 := by
    simpa [prefixWord, tailWord_6451000, baseEnd_6451000] using wordTrace_append hprefix tailTrace_6451000
  have hstable : (prefixWord ++ tailWord_6451000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451000).length < 2 ^ (prefixWord ++ tailWord_6451000).sum := by decide
  have hdescent : baseEnd_6451000 < baseStart_6451000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451007 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 2, 1, 4]
def baseStart_6451007 : Nat := 118140960795 + 6451007 * 2 ^ 59
def prefixEnd_6451007 : Nat := 4983230072969 + 3 ^ 40 * 6451007 * 2
def baseEnd_6451007 : Nat := 3312467296518947139144865

theorem tailTrace_6451007 : CollatzResearch.WordTrace tailWord_6451007 prefixEnd_6451007 3312467296518947139144865 := by
  unfold tailWord_6451007
  simp only [CollatzResearch.WordTrace]
  refine ⟨235287554940110858126367275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156858369960073905417578183 235287554940110858126367275)
  ·
    refine ⟨352931332410166287189550913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235287554940110858126367275 352931332410166287189550913)
    ·
      refine ⟨264698499307624715392163185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352931332410166287189550913 264698499307624715392163185)
      ·
        refine ⟨198523874480718536544122389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264698499307624715392163185 198523874480718536544122389)
        ·
          refine ⟨9305806616283681400505737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 198523874480718536544122389 9305806616283681400505737)
          ·
            refine ⟨6979354962212761050379303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9305806616283681400505737 6979354962212761050379303)
            ·
              refine ⟨10469032443319141575568955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6979354962212761050379303 10469032443319141575568955)
              ·
                refine ⟨15703548664978712363353433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10469032443319141575568955 15703548664978712363353433)
                ·
                  refine ⟨11777661498734034272515075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15703548664978712363353433 11777661498734034272515075)
                  ·
                    refine ⟨17666492248101051408772613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11777661498734034272515075 17666492248101051408772613)
                    ·
                      refine ⟨3312467296518947139144865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17666492248101051408772613 3312467296518947139144865)
                      ·
                        rfl

theorem cell23_6451007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_6451007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451007 prefixEnd_6451007 := by exact prefixLift 6451007
  have htrace : WordTrace (prefixWord ++ tailWord_6451007) baseStart_6451007 baseEnd_6451007 := by
    simpa [prefixWord, tailWord_6451007, baseEnd_6451007] using wordTrace_append hprefix tailTrace_6451007
  have hstable : (prefixWord ++ tailWord_6451007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451007).length < 2 ^ (prefixWord ++ tailWord_6451007).sum := by decide
  have hdescent : baseEnd_6451007 < baseStart_6451007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451017 : List Nat := [1, 2, 1, 1, 2, 4, 4, 3, 1, 4]
def baseStart_6451017 : Nat := 118140960795 + 6451017 * 2 ^ 59
def prefixEnd_6451017 : Nat := 4983230072969 + 3 ^ 40 * 6451017 * 2
def baseEnd_6451017 : Nat := 1104157477108497366673273

theorem tailTrace_6451017 : CollatzResearch.WordTrace tailWord_6451017 prefixEnd_6451017 1104157477108497366673273 := by
  unfold tailWord_6451017
  simp only [CollatzResearch.WordTrace]
  refine ⟨235287919670074629834231305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156858613113383086556154203 235287919670074629834231305)
  ·
    refine ⟨176465939752555972375673479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235287919670074629834231305 176465939752555972375673479)
    ·
      refine ⟨264698909628833958563510219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176465939752555972375673479 264698909628833958563510219)
      ·
        refine ⟨397048364443250937845265329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264698909628833958563510219 397048364443250937845265329)
        ·
          refine ⟨297786273332438203383948997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397048364443250937845265329 297786273332438203383948997)
          ·
            refine ⟨55834926249832163134490437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 297786273332438203383948997 55834926249832163134490437)
            ·
              refine ⟨10469048671843530587716957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55834926249832163134490437 10469048671843530587716957)
              ·
                refine ⟨3925893251941323970393859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10469048671843530587716957 3925893251941323970393859)
                ·
                  refine ⟨5888839877911985955590789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925893251941323970393859 5888839877911985955590789)
                  ·
                    refine ⟨1104157477108497366673273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5888839877911985955590789 1104157477108497366673273)
                    ·
                      rfl

theorem cell23_6451017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 1, 4].length) (baseStart_6451017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451017 prefixEnd_6451017 := by exact prefixLift 6451017
  have htrace : WordTrace (prefixWord ++ tailWord_6451017) baseStart_6451017 baseEnd_6451017 := by
    simpa [prefixWord, tailWord_6451017, baseEnd_6451017] using wordTrace_append hprefix tailTrace_6451017
  have hstable : (prefixWord ++ tailWord_6451017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451017).length < 2 ^ (prefixWord ++ tailWord_6451017).sum := by decide
  have hdescent : baseEnd_6451017 < baseStart_6451017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451053 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_6451053 : Nat := 118140960795 + 6451053 * 2 ^ 59
def prefixEnd_6451053 : Nat := 4983230072969 + 3 ^ 40 * 6451053 * 2
def baseEnd_6451053 : Nat := 3312490916629053959169653

theorem tailTrace_6451053 : CollatzResearch.WordTrace tailWord_6451053 prefixEnd_6451053 3312490916629053959169653 := by
  unfold tailWord_6451053
  simp only [CollatzResearch.WordTrace]
  refine ⟨235289232697944207982541813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156859488465296138655027875 235289232697944207982541813)
  ·
    refine ⟨22058365565432269498363295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235289232697944207982541813 22058365565432269498363295)
    ·
      refine ⟨33087548348148404247544943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22058365565432269498363295 33087548348148404247544943)
      ·
        refine ⟨49631322522222606371317415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33087548348148404247544943 49631322522222606371317415)
        ·
          refine ⟨74446983783333909556976123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49631322522222606371317415 74446983783333909556976123)
          ·
            refine ⟨111670475675000864335464185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74446983783333909556976123 111670475675000864335464185)
            ·
              refine ⟨83752856756250648251598139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111670475675000864335464185 83752856756250648251598139)
              ·
                refine ⟨125629285134375972377397209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83752856756250648251598139 125629285134375972377397209)
                ·
                  refine ⟨94221963850781979283047907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125629285134375972377397209 94221963850781979283047907)
                  ·
                    refine ⟨141332945776172968924571861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94221963850781979283047907 141332945776172968924571861)
                    ·
                      refine ⟨3312490916629053959169653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141332945776172968924571861 3312490916629053959169653)
                      ·
                        rfl

theorem cell23_6451053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_6451053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451053 prefixEnd_6451053 := by exact prefixLift 6451053
  have htrace : WordTrace (prefixWord ++ tailWord_6451053) baseStart_6451053 baseEnd_6451053 := by
    simpa [prefixWord, tailWord_6451053, baseEnd_6451053] using wordTrace_append hprefix tailTrace_6451053
  have hstable : (prefixWord ++ tailWord_6451053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451053).length < 2 ^ (prefixWord ++ tailWord_6451053).sum := by decide
  have hdescent : baseEnd_6451053 < baseStart_6451053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451093 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_6451093 : Nat := 118140960795 + 6451093 * 2 ^ 59
def prefixEnd_6451093 : Nat := 4983230072969 + 3 ^ 40 * 6451093 * 2
def baseEnd_6451093 : Nat := 3312511455855233802669469

theorem tailTrace_6451093 : CollatzResearch.WordTrace tailWord_6451093 prefixEnd_6451093 3312511455855233802669469 := by
  unfold tailWord_6451093
  simp only [CollatzResearch.WordTrace]
  refine ⟨235290691617799294813997933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156860461078532863209331955 235290691617799294813997933)
  ·
    refine ⟨88234009356674735555249225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235290691617799294813997933 88234009356674735555249225)
    ·
      refine ⟨66175507017506051666436919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88234009356674735555249225 66175507017506051666436919)
      ·
        refine ⟨99263260526259077499655379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66175507017506051666436919 99263260526259077499655379)
        ·
          refine ⟨148894890789388616249483069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99263260526259077499655379 148894890789388616249483069)
          ·
            refine ⟨55835584046020731093556151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148894890789388616249483069 55835584046020731093556151)
            ·
              refine ⟨83753376069031096640334227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55835584046020731093556151 83753376069031096640334227)
              ·
                refine ⟨125630064103546644960501341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83753376069031096640334227 125630064103546644960501341)
                ·
                  refine ⟨47111274038829991860188003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125630064103546644960501341 47111274038829991860188003)
                  ·
                    refine ⟨70666911058244987790282005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47111274038829991860188003 70666911058244987790282005)
                    ·
                      refine ⟨3312511455855233802669469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70666911058244987790282005 3312511455855233802669469)
                      ·
                        rfl

theorem cell23_6451093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_6451093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451093 prefixEnd_6451093 := by exact prefixLift 6451093
  have htrace : WordTrace (prefixWord ++ tailWord_6451093) baseStart_6451093 baseEnd_6451093 := by
    simpa [prefixWord, tailWord_6451093, baseEnd_6451093] using wordTrace_append hprefix tailTrace_6451093
  have hstable : (prefixWord ++ tailWord_6451093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451093).length < 2 ^ (prefixWord ++ tailWord_6451093).sum := by decide
  have hdescent : baseEnd_6451093 < baseStart_6451093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451124 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_6451124 : Nat := 118140960795 + 6451124 * 2 ^ 59
def prefixEnd_6451124 : Nat := 4983230072969 + 3 ^ 40 * 6451124 * 2
def baseEnd_6451124 : Nat := 1104175791251841060460609

theorem tailTrace_6451124 : CollatzResearch.WordTrace tailWord_6451124 prefixEnd_6451124 1104175791251841060460609 := by
  unfold tailWord_6451124
  simp only [CollatzResearch.WordTrace]
  refine ⟨117645911140343493554188213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156861214853791324738917617 117645911140343493554188213)
  ·
    refine ⟨11029304169407202520705145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117645911140343493554188213 11029304169407202520705145)
    ·
      refine ⟨8271978127055401890528859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11029304169407202520705145 8271978127055401890528859)
      ·
        refine ⟨12407967190583102835793289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8271978127055401890528859 12407967190583102835793289)
        ·
          refine ⟨9305975392937327126844967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12407967190583102835793289 9305975392937327126844967)
          ·
            refine ⟨13958963089405990690267451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9305975392937327126844967 13958963089405990690267451)
            ·
              refine ⟨20938444634108986035401177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13958963089405990690267451 20938444634108986035401177)
              ·
                refine ⟨15703833475581739526550883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20938444634108986035401177 15703833475581739526550883)
                ·
                  refine ⟨23555750213372609289826325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15703833475581739526550883 23555750213372609289826325)
                  ·
                    refine ⟨1104175791251841060460609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23555750213372609289826325 1104175791251841060460609)
                    ·
                      rfl

theorem cell23_6451124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_6451124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451124 prefixEnd_6451124 := by exact prefixLift 6451124
  have htrace : WordTrace (prefixWord ++ tailWord_6451124) baseStart_6451124 baseEnd_6451124 := by
    simpa [prefixWord, tailWord_6451124, baseEnd_6451124] using wordTrace_append hprefix tailTrace_6451124
  have hstable : (prefixWord ++ tailWord_6451124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451124).length < 2 ^ (prefixWord ++ tailWord_6451124).sum := by decide
  have hdescent : baseEnd_6451124 < baseStart_6451124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451148 : List Nat := [2, 2, 1, 4, 1, 2, 4, 2, 1, 2, 2]
def baseStart_6451148 : Nat := 118140960795 + 6451148 * 2 ^ 59
def prefixEnd_6451148 : Nat := 4983230072969 + 3 ^ 40 * 6451148 * 2
def baseEnd_6451148 : Nat := 3312539697291231087481717

theorem tailTrace_6451148 : CollatzResearch.WordTrace tailWord_6451148 prefixEnd_6451148 3312539697291231087481717 := by
  unfold tailWord_6451148
  simp only [CollatzResearch.WordTrace]
  refine ⟨117646348816300019603625049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156861798421733359471500065 117646348816300019603625049)
  ·
    refine ⟨88234761612225014702718787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117646348816300019603625049 88234761612225014702718787)
    ·
      refine ⟨132352142418337522054078181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88234761612225014702718787 132352142418337522054078181)
      ·
        refine ⟨24816026703438285385139659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132352142418337522054078181 24816026703438285385139659)
        ·
          refine ⟨37224040055157428077709489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24816026703438285385139659 37224040055157428077709489)
          ·
            refine ⟨27918030041368071058282117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37224040055157428077709489 27918030041368071058282117)
            ·
              refine ⟨5234630632756513323427897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27918030041368071058282117 5234630632756513323427897)
              ·
                refine ⟨3925972974567384992570923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5234630632756513323427897 3925972974567384992570923)
                ·
                  refine ⟨5888959461851077488856385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925972974567384992570923 5888959461851077488856385)
                  ·
                    refine ⟨4416719596388308116642289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5888959461851077488856385 4416719596388308116642289)
                    ·
                      refine ⟨3312539697291231087481717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416719596388308116642289 3312539697291231087481717)
                      ·
                        rfl

theorem cell23_6451148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_6451148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451148 prefixEnd_6451148 := by exact prefixLift 6451148
  have htrace : WordTrace (prefixWord ++ tailWord_6451148) baseStart_6451148 baseEnd_6451148 := by
    simpa [prefixWord, tailWord_6451148, baseEnd_6451148] using wordTrace_append hprefix tailTrace_6451148
  have hstable : (prefixWord ++ tailWord_6451148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451148).length < 2 ^ (prefixWord ++ tailWord_6451148).sum := by decide
  have hdescent : baseEnd_6451148 < baseStart_6451148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451154 : List Nat := [3, 2, 2, 3, 3, 1, 1, 8]
def baseStart_6451154 : Nat := 118140960795 + 6451154 * 2 ^ 59
def prefixEnd_6451154 : Nat := 4983230072969 + 3 ^ 40 * 6451154 * 2
def baseEnd_6451154 : Nat := 122686769562042891259507

theorem tailTrace_6451154 : CollatzResearch.WordTrace tailWord_6451154 prefixEnd_6451154 122686769562042891259507 := by
  unfold tailWord_6451154
  simp only [CollatzResearch.WordTrace]
  refine ⟨58823229117644575557992129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156861944313718868154645677 58823229117644575557992129)
  ·
    refine ⟨44117421838233431668494097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58823229117644575557992129 44117421838233431668494097)
    ·
      refine ⟨33088066378675073751370573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44117421838233431668494097 33088066378675073751370573)
      ·
        refine ⟨12408024892003152656763965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33088066378675073751370573 12408024892003152656763965)
        ·
          refine ⟨4653009334501182246286487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12408024892003152656763965 4653009334501182246286487)
          ·
            refine ⟨6979514001751773369429731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4653009334501182246286487 6979514001751773369429731)
            ·
              refine ⟨10469271002627660054144597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6979514001751773369429731 10469271002627660054144597)
              ·
                refine ⟨122686769562042891259507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10469271002627660054144597 122686769562042891259507)
                ·
                  rfl

theorem cell23_6451154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 8].length) (baseStart_6451154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451154 prefixEnd_6451154 := by exact prefixLift 6451154
  have htrace : WordTrace (prefixWord ++ tailWord_6451154) baseStart_6451154 baseEnd_6451154 := by
    simpa [prefixWord, tailWord_6451154, baseEnd_6451154] using wordTrace_append hprefix tailTrace_6451154
  have hstable : (prefixWord ++ tailWord_6451154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451154).length < 2 ^ (prefixWord ++ tailWord_6451154).sum := by decide
  have hdescent : baseEnd_6451154 < baseStart_6451154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451198 : List Nat := [4, 2, 2, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_6451198 : Nat := 118140960795 + 6451198 * 2 ^ 59
def prefixEnd_6451198 : Nat := 4983230072969 + 3 ^ 40 * 6451198 * 2
def baseEnd_6451198 : Nat := 3312565371323955891856487

theorem tailTrace_6451198 : CollatzResearch.WordTrace tailWord_6451198 prefixEnd_6451198 3312565371323955891856487 := by
  unfold tailWord_6451198
  simp only [CollatzResearch.WordTrace]
  refine ⟨29411815160302362218321281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156863014188279265164380165 29411815160302362218321281)
  ·
    refine ⟨22058861370226771663740961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29411815160302362218321281 22058861370226771663740961)
    ·
      refine ⟨16544146027670078747805721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22058861370226771663740961 16544146027670078747805721)
      ·
        refine ⟨12408109520752559060854291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16544146027670078747805721 12408109520752559060854291)
        ·
          refine ⟨18612164281128838591281437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12408109520752559060854291 18612164281128838591281437)
          ·
            refine ⟨6979561605423314471730539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18612164281128838591281437 6979561605423314471730539)
            ·
              refine ⟨10469342408134971707595809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6979561605423314471730539 10469342408134971707595809)
              ·
                refine ⟨7852006806101228780696857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10469342408134971707595809 7852006806101228780696857)
                ·
                  refine ⟨5889005104575921585522643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7852006806101228780696857 5889005104575921585522643)
                  ·
                    refine ⟨8833507656863882378283965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5889005104575921585522643 8833507656863882378283965)
                    ·
                      refine ⟨3312565371323955891856487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8833507656863882378283965 3312565371323955891856487)
                      ·
                        rfl

theorem cell23_6451198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_6451198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451198 prefixEnd_6451198 := by exact prefixLift 6451198
  have htrace : WordTrace (prefixWord ++ tailWord_6451198) baseStart_6451198 baseEnd_6451198 := by
    simpa [prefixWord, tailWord_6451198, baseEnd_6451198] using wordTrace_append hprefix tailTrace_6451198
  have hstable : (prefixWord ++ tailWord_6451198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451198).length < 2 ^ (prefixWord ++ tailWord_6451198).sum := by decide
  have hdescent : baseEnd_6451198 < baseStart_6451198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451221 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 1, 4, 2]
def baseStart_6451221 : Nat := 118140960795 + 6451221 * 2 ^ 59
def prefixEnd_6451221 : Nat := 4983230072969 + 3 ^ 40 * 6451221 * 2
def baseEnd_6451221 : Nat := 3312577181379009301868881

theorem tailTrace_6451221 : CollatzResearch.WordTrace tailWord_6451221 prefixEnd_6451221 3312577181379009301868881 := by
  unfold tailWord_6451221
  simp only [CollatzResearch.WordTrace]
  refine ⟨235295360161335572674657517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156863573440890381783105011 235295360161335572674657517)
  ·
    refine ⟨88235760060500839752996569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235295360161335572674657517 88235760060500839752996569)
    ·
      refine ⟨66176820045375629814747427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88235760060500839752996569 66176820045375629814747427)
      ·
        refine ⟨99265230068063444722121141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66176820045375629814747427 99265230068063444722121141)
        ·
          refine ⟨9306115318880947942698857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99265230068063444722121141 9306115318880947942698857)
          ·
            refine ⟨6979586489160710957024143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9306115318880947942698857 6979586489160710957024143)
            ·
              refine ⟨10469379733741066435536215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6979586489160710957024143 10469379733741066435536215)
              ·
                refine ⟨15704069600611599653304323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10469379733741066435536215 15704069600611599653304323)
                ·
                  refine ⟨23556104400917399479956485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15704069600611599653304323 23556104400917399479956485)
                  ·
                    refine ⟨4416769575172012402491841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23556104400917399479956485 4416769575172012402491841)
                    ·
                      refine ⟨3312577181379009301868881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416769575172012402491841 3312577181379009301868881)
                      ·
                        rfl

theorem cell23_6451221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_6451221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451221 prefixEnd_6451221 := by exact prefixLift 6451221
  have htrace : WordTrace (prefixWord ++ tailWord_6451221) baseStart_6451221 baseEnd_6451221 := by
    simpa [prefixWord, tailWord_6451221, baseEnd_6451221] using wordTrace_append hprefix tailTrace_6451221
  have hstable : (prefixWord ++ tailWord_6451221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451221).length < 2 ^ (prefixWord ++ tailWord_6451221).sum := by decide
  have hdescent : baseEnd_6451221 < baseStart_6451221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451287 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 3, 4]
def baseStart_6451287 : Nat := 118140960795 + 6451287 * 2 ^ 59
def prefixEnd_6451287 : Nat := 4983230072969 + 3 ^ 40 * 6451287 * 2
def baseEnd_6451287 : Nat := 1104203690367402014547859

theorem tailTrace_6451287 : CollatzResearch.WordTrace tailWord_6451287 prefixEnd_6451287 1104203690367402014547859 := by
  unfold tailWord_6451287
  simp only [CollatzResearch.WordTrace]
  refine ⟨235297767379096465946560115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156865178252730977297706743 235297767379096465946560115)
  ·
    refine ⟨352946651068644698919840173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235297767379096465946560115 352946651068644698919840173)
    ·
      refine ⟨132354994150741762094940065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352946651068644698919840173 132354994150741762094940065)
      ·
        refine ⟨99266245613056321571205049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132354994150741762094940065 99266245613056321571205049)
        ·
          refine ⟨74449684209792241178403787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99266245613056321571205049 74449684209792241178403787)
          ·
            refine ⟨111674526314688361767605681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74449684209792241178403787 111674526314688361767605681)
            ·
              refine ⟨83755894736016271325704261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111674526314688361767605681 83755894736016271325704261)
              ·
                refine ⟨15704230263003050873569549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83755894736016271325704261 15704230263003050873569549)
                ·
                  refine ⟨5889086348626144077588581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15704230263003050873569549 5889086348626144077588581)
                  ·
                    refine ⟨1104203690367402014547859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5889086348626144077588581 1104203690367402014547859)
                    ·
                      rfl

theorem cell23_6451287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_6451287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451287 prefixEnd_6451287 := by exact prefixLift 6451287
  have htrace : WordTrace (prefixWord ++ tailWord_6451287) baseStart_6451287 baseEnd_6451287 := by
    simpa [prefixWord, tailWord_6451287, baseEnd_6451287] using wordTrace_append hprefix tailTrace_6451287
  have hstable : (prefixWord ++ tailWord_6451287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451287).length < 2 ^ (prefixWord ++ tailWord_6451287).sum := by decide
  have hdescent : baseEnd_6451287 < baseStart_6451287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451300 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 10]
def baseStart_6451300 : Nat := 118140960795 + 6451300 * 2 ^ 59
def prefixEnd_6451300 : Nat := 4983230072969 + 3 ^ 40 * 6451300 * 2
def baseEnd_6451300 : Nat := 368068638483412721420113

theorem tailTrace_6451300 : CollatzResearch.WordTrace tailWord_6451300 prefixEnd_6451300 368068638483412721420113 := by
  unfold tailWord_6451300
  simp only [CollatzResearch.WordTrace]
  refine ⟨117649120764024684583391677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156865494352032912777855569 117649120764024684583391677)
  ·
    refine ⟨44118420286509256718771879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117649120764024684583391677 44118420286509256718771879)
    ·
      refine ⟨66177630429763885078157819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44118420286509256718771879 66177630429763885078157819)
      ·
        refine ⟨99266445644645827617236729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66177630429763885078157819 99266445644645827617236729)
        ·
          refine ⟨74449834233484370712927547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99266445644645827617236729 74449834233484370712927547)
          ·
            refine ⟨111674751350226556069391321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74449834233484370712927547 111674751350226556069391321)
            ·
              refine ⟨83756063512669917052043491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111674751350226556069391321 83756063512669917052043491)
              ·
                refine ⟨125634095269004875578065237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83756063512669917052043491 125634095269004875578065237)
                ·
                  refine ⟨368068638483412721420113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 125634095269004875578065237 368068638483412721420113)
                  ·
                    rfl

theorem cell23_6451300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_6451300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451300 prefixEnd_6451300 := by exact prefixLift 6451300
  have htrace : WordTrace (prefixWord ++ tailWord_6451300) baseStart_6451300 baseEnd_6451300 := by
    simpa [prefixWord, tailWord_6451300, baseEnd_6451300] using wordTrace_append hprefix tailTrace_6451300
  have hstable : (prefixWord ++ tailWord_6451300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451300).length < 2 ^ (prefixWord ++ tailWord_6451300).sum := by decide
  have hdescent : baseEnd_6451300 < baseStart_6451300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451314 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_6451314 : Nat := 118140960795 + 6451314 * 2 ^ 59
def prefixEnd_6451314 : Nat := 4983230072969 + 3 ^ 40 * 6451314 * 2
def baseEnd_6451314 : Nat := 3312624935079877438005953

theorem tailTrace_6451314 : CollatzResearch.WordTrace tailWord_6451314 prefixEnd_6451314 3312624935079877438005953 := by
  unfold tailWord_6451314
  simp only [CollatzResearch.WordTrace]
  refine ⟨58824688037499662389448249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156865834766665766371861997 58824688037499662389448249)
  ·
    refine ⟨44118516028124746792086187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58824688037499662389448249 44118516028124746792086187)
    ·
      refine ⟨66177774042187120188129281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44118516028124746792086187 66177774042187120188129281)
      ·
        refine ⟨49633330531640340141096961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66177774042187120188129281 49633330531640340141096961)
        ·
          refine ⟨37224997898730255105822721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49633330531640340141096961 37224997898730255105822721)
          ·
            refine ⟨27918748424047691329367041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37224997898730255105822721 27918748424047691329367041)
            ·
              refine ⟨20939061318035768497025281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27918748424047691329367041 20939061318035768497025281)
              ·
                refine ⟨15704295988526826372768961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20939061318035768497025281 15704295988526826372768961)
                ·
                  refine ⟨11778221991395119779576721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15704295988526826372768961 11778221991395119779576721)
                  ·
                    refine ⟨8833666493546339834682541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11778221991395119779576721 8833666493546339834682541)
                    ·
                      refine ⟨3312624935079877438005953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8833666493546339834682541 3312624935079877438005953)
                      ·
                        rfl

theorem cell23_6451314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_6451314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451314 prefixEnd_6451314 := by exact prefixLift 6451314
  have htrace : WordTrace (prefixWord ++ tailWord_6451314) baseStart_6451314 baseEnd_6451314 := by
    simpa [prefixWord, tailWord_6451314, baseEnd_6451314] using wordTrace_append hprefix tailTrace_6451314
  have hstable : (prefixWord ++ tailWord_6451314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451314).length < 2 ^ (prefixWord ++ tailWord_6451314).sum := by decide
  have hdescent : baseEnd_6451314 < baseStart_6451314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451320 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_6451320 : Nat := 118140960795 + 6451320 * 2 ^ 59
def prefixEnd_6451320 : Nat := 4983230072969 + 3 ^ 40 * 6451320 * 2
def baseEnd_6451320 : Nat := 3312628015963804414530925

theorem tailTrace_6451320 : CollatzResearch.WordTrace tailWord_6451320 prefixEnd_6451320 3312628015963804414530925 := by
  unfold tailWord_6451320
  simp only [CollatzResearch.WordTrace]
  refine ⟨117649485493988456291255707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156865980658651275055007609 117649485493988456291255707)
  ·
    refine ⟨176474228240982684436883561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117649485493988456291255707 176474228240982684436883561)
    ·
      refine ⟨132355671180737013327662671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176474228240982684436883561 132355671180737013327662671)
      ·
        refine ⟨198533506771105519991494007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132355671180737013327662671 198533506771105519991494007)
        ·
          refine ⟨297800260156658279987241011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198533506771105519991494007 297800260156658279987241011)
          ·
            refine ⟨446700390234987419980861517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297800260156658279987241011 446700390234987419980861517)
            ·
              refine ⟨167512646338120282492823069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 446700390234987419980861517 167512646338120282492823069)
              ·
                refine ⟨62817242376795105934808651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167512646338120282492823069 62817242376795105934808651)
                ·
                  refine ⟨94225863565192658902212977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62817242376795105934808651 94225863565192658902212977)
                  ·
                    refine ⟨70669397673894494176659733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94225863565192658902212977 70669397673894494176659733)
                    ·
                      refine ⟨3312628015963804414530925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70669397673894494176659733 3312628015963804414530925)
                      ·
                        rfl

theorem cell23_6451320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_6451320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451320 prefixEnd_6451320 := by exact prefixLift 6451320
  have htrace : WordTrace (prefixWord ++ tailWord_6451320) baseStart_6451320 baseEnd_6451320 := by
    simpa [prefixWord, tailWord_6451320, baseEnd_6451320] using wordTrace_append hprefix tailTrace_6451320
  have hstable : (prefixWord ++ tailWord_6451320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451320).length < 2 ^ (prefixWord ++ tailWord_6451320).sum := by decide
  have hdescent : baseEnd_6451320 < baseStart_6451320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451321 : List Nat := [1, 2, 1, 3, 4, 2, 1, 4, 1, 4]
def baseStart_6451321 : Nat := 118140960795 + 6451321 * 2 ^ 59
def prefixEnd_6451321 : Nat := 4983230072969 + 3 ^ 40 * 6451321 * 2
def baseEnd_6451321 : Nat := 1104209509814819636872807

theorem tailTrace_6451321 : CollatzResearch.WordTrace tailWord_6451321 prefixEnd_6451321 1104209509814819636872807 := by
  unfold tailWord_6451321
  simp only [CollatzResearch.WordTrace]
  refine ⟨235299007460973289753297817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156866004973982193168865211 235299007460973289753297817)
  ·
    refine ⟨176474255595729967314973363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235299007460973289753297817 176474255595729967314973363)
    ·
      refine ⟨264711383393594950972460045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176474255595729967314973363 264711383393594950972460045)
      ·
        refine ⟨99266768772598106614672517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264711383393594950972460045 99266768772598106614672517)
        ·
          refine ⟨18612519144862144990251097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99266768772598106614672517 18612519144862144990251097)
          ·
            refine ⟨13959389358646608742688323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18612519144862144990251097 13959389358646608742688323)
            ·
              refine ⟨20939084037969913114032485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13959389358646608742688323 20939084037969913114032485)
              ·
                refine ⟨3926078257119358708881091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20939084037969913114032485 3926078257119358708881091)
                ·
                  refine ⟨5889117385679038063321637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926078257119358708881091 5889117385679038063321637)
                  ·
                    refine ⟨1104209509814819636872807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5889117385679038063321637 1104209509814819636872807)
                    ·
                      rfl

theorem cell23_6451321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 1, 4].length) (baseStart_6451321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451321 prefixEnd_6451321 := by exact prefixLift 6451321
  have htrace : WordTrace (prefixWord ++ tailWord_6451321) baseStart_6451321 baseEnd_6451321 := by
    simpa [prefixWord, tailWord_6451321, baseEnd_6451321] using wordTrace_append hprefix tailTrace_6451321
  have hstable : (prefixWord ++ tailWord_6451321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451321).length < 2 ^ (prefixWord ++ tailWord_6451321).sum := by decide
  have hdescent : baseEnd_6451321 < baseStart_6451321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451344 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 3, 1, 3]
def baseStart_6451344 : Nat := 118140960795 + 6451344 * 2 ^ 59
def prefixEnd_6451344 : Nat := 4983230072969 + 3 ^ 40 * 6451344 * 2
def baseEnd_6451344 : Nat := 3312640339499512320630815

theorem tailTrace_6451344 : CollatzResearch.WordTrace tailWord_6451344 prefixEnd_6451344 3312640339499512320630815 := by
  unfold tailWord_6451344
  simp only [CollatzResearch.WordTrace]
  refine ⟨117649923169944982340692543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156866564226593309787590057 117649923169944982340692543)
  ·
    refine ⟨176474884754917473511038815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117649923169944982340692543 176474884754917473511038815)
    ·
      refine ⟨264712327132376210266558223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176474884754917473511038815 264712327132376210266558223)
      ·
        refine ⟨397068490698564315399837335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264712327132376210266558223 397068490698564315399837335)
        ·
          refine ⟨595602736047846473099756003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397068490698564315399837335 595602736047846473099756003)
          ·
            refine ⟨893404104071769709649634005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595602736047846473099756003 893404104071769709649634005)
            ·
              refine ⟨20939158689182102569913297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 893404104071769709649634005 20939158689182102569913297)
              ·
                refine ⟨15704369016886576927434973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20939158689182102569913297 15704369016886576927434973)
                ·
                  refine ⟨5889138381332466347788115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15704369016886576927434973 5889138381332466347788115)
                  ·
                    refine ⟨8833707571998699521682173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5889138381332466347788115 8833707571998699521682173)
                    ·
                      refine ⟨3312640339499512320630815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8833707571998699521682173 3312640339499512320630815)
                      ·
                        rfl

theorem cell23_6451344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 3, 1, 3].length) (baseStart_6451344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451344 prefixEnd_6451344 := by exact prefixLift 6451344
  have htrace : WordTrace (prefixWord ++ tailWord_6451344) baseStart_6451344 baseEnd_6451344 := by
    simpa [prefixWord, tailWord_6451344, baseEnd_6451344] using wordTrace_append hprefix tailTrace_6451344
  have hstable : (prefixWord ++ tailWord_6451344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451344).length < 2 ^ (prefixWord ++ tailWord_6451344).sum := by decide
  have hdescent : baseEnd_6451344 < baseStart_6451344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451347 : List Nat := [1, 1, 1, 2, 1, 2, 3, 6, 1, 5]
def baseStart_6451347 : Nat := 118140960795 + 6451347 * 2 ^ 59
def prefixEnd_6451347 : Nat := 4983230072969 + 3 ^ 40 * 6451347 * 2
def baseEnd_6451347 : Nat := 1104213959980491936297767

theorem tailTrace_6451347 : CollatzResearch.WordTrace tailWord_6451347 prefixEnd_6451347 1104213959980491936297767 := by
  unfold tailWord_6451347
  simp only [CollatzResearch.WordTrace]
  refine ⟨235299955758879096193744295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156866637172586064129162863 235299955758879096193744295)
  ·
    refine ⟨352949933638318644290616443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235299955758879096193744295 352949933638318644290616443)
    ·
      refine ⟨529424900457477966435924665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352949933638318644290616443 529424900457477966435924665)
      ·
        refine ⟨397068675343108474826943499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529424900457477966435924665 397068675343108474826943499)
        ·
          refine ⟨595603013014662712240415249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397068675343108474826943499 595603013014662712240415249)
          ·
            refine ⟨446702259760997034180311437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595603013014662712240415249 446702259760997034180311437)
            ·
              refine ⟨167513347410373887817616789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 446702259760997034180311437 167513347410373887817616789)
              ·
                refine ⟨7852188159861275991450787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167513347410373887817616789 7852188159861275991450787)
                ·
                  refine ⟨11778282239791913987176181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7852188159861275991450787 11778282239791913987176181)
                  ·
                    refine ⟨1104213959980491936297767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11778282239791913987176181 1104213959980491936297767)
                    ·
                      rfl

theorem cell23_6451347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 5].length) (baseStart_6451347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451347 prefixEnd_6451347 := by exact prefixLift 6451347
  have htrace : WordTrace (prefixWord ++ tailWord_6451347) baseStart_6451347 baseEnd_6451347 := by
    simpa [prefixWord, tailWord_6451347, baseEnd_6451347] using wordTrace_append hprefix tailTrace_6451347
  have hstable : (prefixWord ++ tailWord_6451347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451347).length < 2 ^ (prefixWord ++ tailWord_6451347).sum := by decide
  have hdescent : baseEnd_6451347 < baseStart_6451347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451387 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 5]
def baseStart_6451387 : Nat := 118140960795 + 6451387 * 2 ^ 59
def prefixEnd_6451387 : Nat := 4983230072969 + 3 ^ 40 * 6451387 * 2
def baseEnd_6451387 : Nat := 3312662419167655652393117

theorem tailTrace_6451387 : CollatzResearch.WordTrace tailWord_6451387 prefixEnd_6451387 3312662419167655652393117 := by
  unfold tailWord_6451387
  simp only [CollatzResearch.WordTrace]
  refine ⟨235301414678734183025200415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156867609785822788683466943 235301414678734183025200415)
  ·
    refine ⟨352952122018101274537800623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235301414678734183025200415 352952122018101274537800623)
    ·
      refine ⟨529428183027151911806700935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352952122018101274537800623 529428183027151911806700935)
      ·
        refine ⟨794142274540727867710051403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529428183027151911806700935 794142274540727867710051403)
        ·
          refine ⟨1191213411811091801565077105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794142274540727867710051403 1191213411811091801565077105)
          ·
            refine ⟨893410058858318851173807829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1191213411811091801565077105 893410058858318851173807829)
            ·
              refine ⟨20939298254491848074386121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 893410058858318851173807829 20939298254491848074386121)
              ·
                refine ⟨15704473690868886055789591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20939298254491848074386121 15704473690868886055789591)
                ·
                  refine ⟨23556710536303329083684387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15704473690868886055789591 23556710536303329083684387)
                  ·
                    refine ⟨35335065804454993625526581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23556710536303329083684387 35335065804454993625526581)
                    ·
                      refine ⟨3312662419167655652393117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35335065804454993625526581 3312662419167655652393117)
                      ·
                        rfl

theorem cell23_6451387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 5].length) (baseStart_6451387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451387 prefixEnd_6451387 := by exact prefixLift 6451387
  have htrace : WordTrace (prefixWord ++ tailWord_6451387) baseStart_6451387 baseEnd_6451387 := by
    simpa [prefixWord, tailWord_6451387, baseEnd_6451387] using wordTrace_append hprefix tailTrace_6451387
  have hstable : (prefixWord ++ tailWord_6451387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451387).length < 2 ^ (prefixWord ++ tailWord_6451387).sum := by decide
  have hdescent : baseEnd_6451387 < baseStart_6451387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451421 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_6451421 : Nat := 118140960795 + 6451421 * 2 ^ 59
def prefixEnd_6451421 : Nat := 4983230072969 + 3 ^ 40 * 6451421 * 2
def baseEnd_6451421 : Nat := 3312679877509908519367961

theorem tailTrace_6451421 : CollatzResearch.WordTrace tailWord_6451421 prefixEnd_6451421 3312679877509908519367961 := by
  unfold tailWord_6451421
  simp only [CollatzResearch.WordTrace]
  refine ⟨235302654760611006831938117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156868436507074004554625411 235302654760611006831938117)
  ·
    refine ⟨44119247767614563780988397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235302654760611006831938117 44119247767614563780988397)
    ·
      refine ⟨16544717912855461417870649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44119247767614563780988397 16544717912855461417870649)
      ·
        refine ⟨12408538434641596063402987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16544717912855461417870649 12408538434641596063402987)
        ·
          refine ⟨18612807651962394095104481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12408538434641596063402987 18612807651962394095104481)
          ·
            refine ⟨13959605738971795571328361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18612807651962394095104481 13959605738971795571328361)
            ·
              refine ⟨10469704304228846678496271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13959605738971795571328361 10469704304228846678496271)
              ·
                refine ⟨15704556456343270017744407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10469704304228846678496271 15704556456343270017744407)
                ·
                  refine ⟨23556834684514905026616611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15704556456343270017744407 23556834684514905026616611)
                  ·
                    refine ⟨35335252026772357539924917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23556834684514905026616611 35335252026772357539924917)
                    ·
                      refine ⟨3312679877509908519367961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35335252026772357539924917 3312679877509908519367961)
                      ·
                        rfl

theorem cell23_6451421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_6451421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451421 prefixEnd_6451421 := by exact prefixLift 6451421
  have htrace : WordTrace (prefixWord ++ tailWord_6451421) baseStart_6451421 baseEnd_6451421 := by
    simpa [prefixWord, tailWord_6451421, baseEnd_6451421] using wordTrace_append hprefix tailTrace_6451421
  have hstable : (prefixWord ++ tailWord_6451421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451421).length < 2 ^ (prefixWord ++ tailWord_6451421).sum := by decide
  have hdescent : baseEnd_6451421 < baseStart_6451421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451435 : List Nat := [1, 1, 1, 1, 2, 5, 5, 2, 1, 2, 2]
def baseStart_6451435 : Nat := 118140960795 + 6451435 * 2 ^ 59
def prefixEnd_6451435 : Nat := 4983230072969 + 3 ^ 40 * 6451435 * 2
def baseEnd_6451435 : Nat := 3312687066239071464592897

theorem tailTrace_6451435 : CollatzResearch.WordTrace tailWord_6451435 prefixEnd_6451435 3312687066239071464592897 := by
  unfold tailWord_6451435
  simp only [CollatzResearch.WordTrace]
  refine ⟨235303165382560287222947759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156868776921706858148631839 235303165382560287222947759)
  ·
    refine ⟨352954748073840430834421639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235303165382560287222947759 352954748073840430834421639)
    ·
      refine ⟨529432122110760646251632459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352954748073840430834421639 529432122110760646251632459)
      ·
        refine ⟨794148183166140969377448689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529432122110760646251632459 794148183166140969377448689)
        ·
          refine ⟨595611137374605727033086517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 794148183166140969377448689 595611137374605727033086517)
          ·
            refine ⟨55838544128869286909351861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 595611137374605727033086517 55838544128869286909351861)
            ·
              refine ⟨5234863512081495647751737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55838544128869286909351861 5234863512081495647751737)
              ·
                refine ⟨3926147634061121735813803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5234863512081495647751737 3926147634061121735813803)
                ·
                  refine ⟨5889221451091682603720705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926147634061121735813803 5889221451091682603720705)
                  ·
                    refine ⟨4416916088318761952790529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5889221451091682603720705 4416916088318761952790529)
                    ·
                      refine ⟨3312687066239071464592897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416916088318761952790529 3312687066239071464592897)
                      ·
                        rfl

theorem cell23_6451435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 1, 2, 2].length) (baseStart_6451435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451435 prefixEnd_6451435 := by exact prefixLift 6451435
  have htrace : WordTrace (prefixWord ++ tailWord_6451435) baseStart_6451435 baseEnd_6451435 := by
    simpa [prefixWord, tailWord_6451435, baseEnd_6451435] using wordTrace_append hprefix tailTrace_6451435
  have hstable : (prefixWord ++ tailWord_6451435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451435).length < 2 ^ (prefixWord ++ tailWord_6451435).sum := by decide
  have hdescent : baseEnd_6451435 < baseStart_6451435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451461 : List Nat := [1, 3, 1, 1, 2, 1, 2, 6, 1, 3, 2]
def baseStart_6451461 : Nat := 118140960795 + 6451461 * 2 ^ 59
def prefixEnd_6451461 : Nat := 4983230072969 + 3 ^ 40 * 6451461 * 2
def baseEnd_6451461 : Nat := 3312700416736088362867777

theorem tailTrace_6451461 : CollatzResearch.WordTrace tailWord_6451461 prefixEnd_6451461 3312700416736088362867777 := by
  unfold tailWord_6451461
  simp only [CollatzResearch.WordTrace]
  refine ⟨235304113680466093663394237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156869409120310729108929491 235304113680466093663394237)
  ·
    refine ⟨88239042630174785123772839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235304113680466093663394237 88239042630174785123772839)
    ·
      refine ⟨132358563945262177685659259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88239042630174785123772839 132358563945262177685659259)
      ·
        refine ⟨198537845917893266528488889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132358563945262177685659259 198537845917893266528488889)
        ·
          refine ⟨148903384438419949896366667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198537845917893266528488889 148903384438419949896366667)
          ·
            refine ⟨223355076657629924844550001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148903384438419949896366667 223355076657629924844550001)
            ·
              refine ⟨167516307493222443633412501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223355076657629924844550001 167516307493222443633412501)
              ·
                refine ⟨7852326913744802045316211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167516307493222443633412501 7852326913744802045316211)
                ·
                  refine ⟨11778490370617203067974317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7852326913744802045316211 11778490370617203067974317)
                  ·
                    refine ⟨4416933888981451150490369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11778490370617203067974317 4416933888981451150490369)
                    ·
                      refine ⟨3312700416736088362867777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416933888981451150490369 3312700416736088362867777)
                      ·
                        rfl

theorem cell23_6451461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 3, 2].length) (baseStart_6451461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451461 prefixEnd_6451461 := by exact prefixLift 6451461
  have htrace : WordTrace (prefixWord ++ tailWord_6451461) baseStart_6451461 baseEnd_6451461 := by
    simpa [prefixWord, tailWord_6451461, baseEnd_6451461] using wordTrace_append hprefix tailTrace_6451461
  have hstable : (prefixWord ++ tailWord_6451461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451461).length < 2 ^ (prefixWord ++ tailWord_6451461).sum := by decide
  have hdescent : baseEnd_6451461 < baseStart_6451461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451485 : List Nat := [1, 4, 2, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_6451485 : Nat := 118140960795 + 6451485 * 2 ^ 59
def prefixEnd_6451485 : Nat := 4983230072969 + 3 ^ 40 * 6451485 * 2
def baseEnd_6451485 : Nat := 3312712740271796268967667

theorem tailTrace_6451485 : CollatzResearch.WordTrace tailWord_6451485 prefixEnd_6451485 3312712740271796268967667 := by
  unfold tailWord_6451485
  simp only [CollatzResearch.WordTrace]
  refine ⟨235304989032379145762267909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156869992688252763841511939 235304989032379145762267909)
  ·
    refine ⟨44119685443571089830425233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235304989032379145762267909 44119685443571089830425233)
    ·
      refine ⟨33089764082678317372818925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44119685443571089830425233 33089764082678317372818925)
      ·
        refine ⟨12408661531004369014807097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33089764082678317372818925 12408661531004369014807097)
        ·
          refine ⟨9306496148253276761105323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12408661531004369014807097 9306496148253276761105323)
          ·
            refine ⟨13959744222379915141657985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9306496148253276761105323 13959744222379915141657985)
            ·
              refine ⟨10469808166784936356243489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13959744222379915141657985 10469808166784936356243489)
              ·
                refine ⟨7852356125088702267182617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10469808166784936356243489 7852356125088702267182617)
                ·
                  refine ⟨5889267093816526700386963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7852356125088702267182617 5889267093816526700386963)
                  ·
                    refine ⟨8833900640724790050580445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5889267093816526700386963 8833900640724790050580445)
                    ·
                      refine ⟨3312712740271796268967667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8833900640724790050580445 3312712740271796268967667)
                      ·
                        rfl

theorem cell23_6451485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_6451485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451485 prefixEnd_6451485 := by exact prefixLift 6451485
  have htrace : WordTrace (prefixWord ++ tailWord_6451485) baseStart_6451485 baseEnd_6451485 := by
    simpa [prefixWord, tailWord_6451485, baseEnd_6451485] using wordTrace_append hprefix tailTrace_6451485
  have hstable : (prefixWord ++ tailWord_6451485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451485).length < 2 ^ (prefixWord ++ tailWord_6451485).sum := by decide
  have hdescent : baseEnd_6451485 < baseStart_6451485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451486 : List Nat := [4, 3, 2, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_6451486 : Nat := 118140960795 + 6451486 * 2 ^ 59
def prefixEnd_6451486 : Nat := 4983230072969 + 3 ^ 40 * 6451486 * 2
def baseEnd_6451486 : Nat := 3312713253752450765055163

theorem tailTrace_6451486 : CollatzResearch.WordTrace tailWord_6451486 prefixEnd_6451486 3312713253752450765055163 := by
  unfold tailWord_6451486
  simp only [CollatzResearch.WordTrace]
  refine ⟨29413128188171940366631789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156870017003583681955369541 29413128188171940366631789)
  ·
    refine ⟨11029923070564477637486921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29413128188171940366631789 11029923070564477637486921)
    ·
      refine ⟨8272442302923358228115191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11029923070564477637486921 8272442302923358228115191)
      ·
        refine ⟨12408663454385037342172787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8272442302923358228115191 12408663454385037342172787)
        ·
          refine ⟨18612995181577556013259181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12408663454385037342172787 18612995181577556013259181)
          ·
            refine ⟨6979873193091583504972193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18612995181577556013259181 6979873193091583504972193)
            ·
              refine ⟨5234904894818687628729145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6979873193091583504972193 5234904894818687628729145)
              ·
                refine ⟨3926178671114015721546859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5234904894818687628729145 3926178671114015721546859)
                ·
                  refine ⟨5889268006671023582320289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926178671114015721546859 5889268006671023582320289)
                  ·
                    refine ⟨4416951005003267686740217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5889268006671023582320289 4416951005003267686740217)
                    ·
                      refine ⟨3312713253752450765055163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416951005003267686740217 3312713253752450765055163)
                      ·
                        rfl

theorem cell23_6451486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_6451486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451486 prefixEnd_6451486 := by exact prefixLift 6451486
  have htrace : WordTrace (prefixWord ++ tailWord_6451486) baseStart_6451486 baseEnd_6451486 := by
    simpa [prefixWord, tailWord_6451486, baseEnd_6451486] using wordTrace_append hprefix tailTrace_6451486
  have hstable : (prefixWord ++ tailWord_6451486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451486).length < 2 ^ (prefixWord ++ tailWord_6451486).sum := by decide
  have hdescent : baseEnd_6451486 < baseStart_6451486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451508 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_6451508 : Nat := 118140960795 + 6451508 * 2 ^ 59
def prefixEnd_6451508 : Nat := 4983230072969 + 3 ^ 40 * 6451508 * 2
def baseEnd_6451508 : Nat := 3312724550326849678980061

theorem tailTrace_6451508 : CollatzResearch.WordTrace tailWord_6451508 prefixEnd_6451508 3312724550326849678980061 := by
  unfold tailWord_6451508
  simp only [CollatzResearch.WordTrace]
  refine ⟨117652913955647910345177589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156870551940863880460236785 117652913955647910345177589)
  ·
    refine ⟨11029960683341991594860399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117652913955647910345177589 11029960683341991594860399)
    ·
      refine ⟨16544941025012987392290599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11029960683341991594860399 16544941025012987392290599)
      ·
        refine ⟨24817411537519481088435899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16544941025012987392290599 24817411537519481088435899)
        ·
          refine ⟨37226117306279221632653849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24817411537519481088435899 37226117306279221632653849)
          ·
            refine ⟨27919587979709416224490387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37226117306279221632653849 27919587979709416224490387)
            ·
              refine ⟨41879381969564124336735581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27919587979709416224490387 41879381969564124336735581)
              ·
                refine ⟨15704768238586546626275843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41879381969564124336735581 15704768238586546626275843)
                ·
                  refine ⟨23557152357879819939413765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15704768238586546626275843 23557152357879819939413765)
                  ·
                    refine ⟨4416966067102466238640081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23557152357879819939413765 4416966067102466238640081)
                    ·
                      refine ⟨3312724550326849678980061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4416966067102466238640081 3312724550326849678980061)
                      ·
                        rfl

theorem cell23_6451508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_6451508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451508 prefixEnd_6451508 := by exact prefixLift 6451508
  have htrace : WordTrace (prefixWord ++ tailWord_6451508) baseStart_6451508 baseEnd_6451508 := by
    simpa [prefixWord, tailWord_6451508, baseEnd_6451508] using wordTrace_append hprefix tailTrace_6451508
  have hstable : (prefixWord ++ tailWord_6451508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451508).length < 2 ^ (prefixWord ++ tailWord_6451508).sum := by decide
  have hdescent : baseEnd_6451508 < baseStart_6451508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451514 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 7]
def baseStart_6451514 : Nat := 118140960795 + 6451514 * 2 ^ 59
def prefixEnd_6451514 : Nat := 4983230072969 + 3 ^ 40 * 6451514 * 2
def baseEnd_6451514 : Nat := 368080847912308517278337

theorem tailTrace_6451514 : CollatzResearch.WordTrace tailWord_6451514 prefixEnd_6451514 368080847912308517278337 := by
  unfold tailWord_6451514
  simp only [CollatzResearch.WordTrace]
  refine ⟨58826511687318520928768399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156870697832849389143382397 58826511687318520928768399)
  ·
    refine ⟨88239767530977781393152599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58826511687318520928768399 88239767530977781393152599)
    ·
      refine ⟨132359651296466672089728899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88239767530977781393152599 132359651296466672089728899)
      ·
        refine ⟨198539476944700008134593349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132359651296466672089728899 198539476944700008134593349)
        ·
          refine ⟨37226151927131251525236253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198539476944700008134593349 37226151927131251525236253)
          ·
            refine ⟨13959806972674219321963595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37226151927131251525236253 13959806972674219321963595)
            ·
              refine ⟨20939710459011328982945393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13959806972674219321963595 20939710459011328982945393)
              ·
                refine ⟨15704782844258496737209045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20939710459011328982945393 15704782844258496737209045)
                ·
                  refine ⟨368080847912308517278337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15704782844258496737209045 368080847912308517278337)
                  ·
                    rfl

theorem cell23_6451514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_6451514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451514 prefixEnd_6451514 := by exact prefixLift 6451514
  have htrace : WordTrace (prefixWord ++ tailWord_6451514) baseStart_6451514 baseEnd_6451514 := by
    simpa [prefixWord, tailWord_6451514, baseEnd_6451514] using wordTrace_append hprefix tailTrace_6451514
  have hstable : (prefixWord ++ tailWord_6451514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451514).length < 2 ^ (prefixWord ++ tailWord_6451514).sum := by decide
  have hdescent : baseEnd_6451514 < baseStart_6451514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451548 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 7]
def baseStart_6451548 : Nat := 118140960795 + 6451548 * 2 ^ 59
def prefixEnd_6451548 : Nat := 4983230072969 + 3 ^ 40 * 6451548 * 2
def baseEnd_6451548 : Nat := 368082787728114391386653

theorem tailTrace_6451548 : CollatzResearch.WordTrace tailWord_6451548 prefixEnd_6451548 368082787728114391386653 := by
  unfold tailWord_6451548
  simp only [CollatzResearch.WordTrace]
  refine ⟨117653643415575453760905649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156871524554100605014540865 117653643415575453760905649)
  ·
    refine ⟨88240232561681590320679237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117653643415575453760905649 88240232561681590320679237)
    ·
      refine ⟨16545043605315298185127357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88240232561681590320679237 16545043605315298185127357)
      ·
        refine ⟨6204391351993236819422759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16545043605315298185127357 6204391351993236819422759)
        ·
          refine ⟨9306587027989855229134139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6204391351993236819422759 9306587027989855229134139)
          ·
            refine ⟨13959880541984782843701209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9306587027989855229134139 13959880541984782843701209)
            ·
              refine ⟨10469910406488587132775907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13959880541984782843701209 10469910406488587132775907)
              ·
                refine ⟨15704865609732880699163861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10469910406488587132775907 15704865609732880699163861)
                ·
                  refine ⟨368082787728114391386653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15704865609732880699163861 368082787728114391386653)
                  ·
                    rfl

theorem cell23_6451548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 7].length) (baseStart_6451548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451548 prefixEnd_6451548 := by exact prefixLift 6451548
  have htrace : WordTrace (prefixWord ++ tailWord_6451548) baseStart_6451548 baseEnd_6451548 := by
    simpa [prefixWord, tailWord_6451548, baseEnd_6451548] using wordTrace_append hprefix tailTrace_6451548
  have hstable : (prefixWord ++ tailWord_6451548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451548).length < 2 ^ (prefixWord ++ tailWord_6451548).sum := by decide
  have hdescent : baseEnd_6451548 < baseStart_6451548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451598 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6451598 : Nat := 118140960795 + 6451598 * 2 ^ 59
def prefixEnd_6451598 : Nat := 4983230072969 + 3 ^ 40 * 6451598 * 2
def baseEnd_6451598 : Nat := 3312770763585754326854647

theorem tailTrace_6451598 : CollatzResearch.WordTrace tailWord_6451598 prefixEnd_6451598 3312770763585754326854647 := by
  unfold tailWord_6451598
  simp only [CollatzResearch.WordTrace]
  refine ⟨29413638810121220757641431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156872740320646510707420965 29413638810121220757641431)
  ·
    refine ⟨44120458215181831136462147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29413638810121220757641431 44120458215181831136462147)
    ·
      refine ⟨66180687322772746704693221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44120458215181831136462147 66180687322772746704693221)
      ·
        refine ⟨12408878873019890007129979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66180687322772746704693221 12408878873019890007129979)
        ·
          refine ⟨18613318309529835010694969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12408878873019890007129979 18613318309529835010694969)
          ·
            refine ⟨13959988732147376258021227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18613318309529835010694969 13959988732147376258021227)
            ·
              refine ⟨20939983098221064387031841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13959988732147376258021227 20939983098221064387031841)
              ·
                refine ⟨15704987323665798290273881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20939983098221064387031841 15704987323665798290273881)
                ·
                  refine ⟨11778740492749348717705411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15704987323665798290273881 11778740492749348717705411)
                  ·
                    refine ⟨17668110739124023076558117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11778740492749348717705411 17668110739124023076558117)
                    ·
                      refine ⟨3312770763585754326854647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17668110739124023076558117 3312770763585754326854647)
                      ·
                        rfl

theorem cell23_6451598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6451598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451598 prefixEnd_6451598 := by exact prefixLift 6451598
  have htrace : WordTrace (prefixWord ++ tailWord_6451598) baseStart_6451598 baseEnd_6451598 := by
    simpa [prefixWord, tailWord_6451598, baseEnd_6451598] using wordTrace_append hprefix tailTrace_6451598
  have hstable : (prefixWord ++ tailWord_6451598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451598).length < 2 ^ (prefixWord ++ tailWord_6451598).sum := by decide
  have hdescent : baseEnd_6451598 < baseStart_6451598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451608 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 3, 4]
def baseStart_6451608 : Nat := 118140960795 + 6451608 * 2 ^ 59
def prefixEnd_6451608 : Nat := 4983230072969 + 3 ^ 40 * 6451608 * 2
def baseEnd_6451608 : Nat := 1104258632797433095909867

theorem tailTrace_6451608 : CollatzResearch.WordTrace tailWord_6451608 prefixEnd_6451608 1104258632797433095909867 := by
  unfold tailWord_6451608
  simp only [CollatzResearch.WordTrace]
  refine ⟨117654737605466768884497739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156872983473955691845996985 117654737605466768884497739)
  ·
    refine ⟨176482106408200153326746609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117654737605466768884497739 176482106408200153326746609)
    ·
      refine ⟨132361579806150114995059957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176482106408200153326746609 132361579806150114995059957)
      ·
        refine ⟨12408898106826573280786871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132361579806150114995059957 12408898106826573280786871)
        ·
          refine ⟨18613347160239859921180307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12408898106826573280786871 18613347160239859921180307)
          ·
            refine ⟨27920020740359789881770461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18613347160239859921180307 27920020740359789881770461)
            ·
              refine ⟨10470007777634921205663923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27920020740359789881770461 10470007777634921205663923)
              ·
                refine ⟨15705011666452381808495885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10470007777634921205663923 15705011666452381808495885)
                ·
                  refine ⟨5889379374919643178185957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15705011666452381808495885 5889379374919643178185957)
                  ·
                    refine ⟨1104258632797433095909867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5889379374919643178185957 1104258632797433095909867)
                    ·
                      rfl

theorem cell23_6451608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_6451608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451608 prefixEnd_6451608 := by exact prefixLift 6451608
  have htrace : WordTrace (prefixWord ++ tailWord_6451608) baseStart_6451608 baseEnd_6451608 := by
    simpa [prefixWord, tailWord_6451608, baseEnd_6451608] using wordTrace_append hprefix tailTrace_6451608
  have hstable : (prefixWord ++ tailWord_6451608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451608).length < 2 ^ (prefixWord ++ tailWord_6451608).sum := by decide
  have hdescent : baseEnd_6451608 < baseStart_6451608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451658 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 2, 3, 2]
def baseStart_6451658 : Nat := 118140960795 + 6451658 * 2 ^ 59
def prefixEnd_6451658 : Nat := 4983230072969 + 3 ^ 40 * 6451658 * 2
def baseEnd_6451658 : Nat := 3312801572425024092104371

theorem tailTrace_6451658 : CollatzResearch.WordTrace tailWord_6451658 prefixEnd_6451658 3312801572425024092104371 := by
  unfold tailWord_6451658
  simp only [CollatzResearch.WordTrace]
  refine ⟨58827824715188099077078907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156874199240501597538877085 58827824715188099077078907)
  ·
    refine ⟨88241737072782148615618361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58827824715188099077078907 88241737072782148615618361)
    ·
      refine ⟨66181302804586611461713771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88241737072782148615618361 66181302804586611461713771)
      ·
        refine ⟨99271954206879917192570657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66181302804586611461713771 99271954206879917192570657)
        ·
          refine ⟨74453965655159937894427993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99271954206879917192570657 74453965655159937894427993)
          ·
            refine ⟨55840474241369953420820995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74453965655159937894427993 55840474241369953420820995)
            ·
              refine ⟨83760711362054930131231493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55840474241369953420820995 83760711362054930131231493)
              ·
                refine ⟨15705133380385299399605905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83760711362054930131231493 15705133380385299399605905)
                ·
                  refine ⟨11778850035288974549704429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15705133380385299399605905 11778850035288974549704429)
                  ·
                    refine ⟨4417068763233365456139161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11778850035288974549704429 4417068763233365456139161)
                    ·
                      refine ⟨3312801572425024092104371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417068763233365456139161 3312801572425024092104371)
                      ·
                        rfl

theorem cell23_6451658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_6451658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451658 prefixEnd_6451658 := by exact prefixLift 6451658
  have htrace : WordTrace (prefixWord ++ tailWord_6451658) baseStart_6451658 baseEnd_6451658 := by
    simpa [prefixWord, tailWord_6451658, baseEnd_6451658] using wordTrace_append hprefix tailTrace_6451658
  have hstable : (prefixWord ++ tailWord_6451658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451658).length < 2 ^ (prefixWord ++ tailWord_6451658).sum := by decide
  have hdescent : baseEnd_6451658 < baseStart_6451658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451671 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 4, 6, 2]
def baseStart_6451671 : Nat := 118140960795 + 6451671 * 2 ^ 59
def prefixEnd_6451671 : Nat := 4983230072969 + 3 ^ 40 * 6451671 * 2
def baseEnd_6451671 : Nat := 3312808247673532541241811

theorem tailTrace_6451671 : CollatzResearch.WordTrace tailWord_6451671 prefixEnd_6451671 3312808247673532541241811 := by
  unfold tailWord_6451671
  simp only [CollatzResearch.WordTrace]
  refine ⟨235311773009705299528538867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156874515339803533019025911 235311773009705299528538867)
  ·
    refine ⟨352967659514557949292808301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235311773009705299528538867 352967659514557949292808301)
    ·
      refine ⟨132362872317959230984803113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352967659514557949292808301 132362872317959230984803113)
      ·
        refine ⟨99272154238469423238602335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132362872317959230984803113 99272154238469423238602335)
        ·
          refine ⟨148908231357704134857903503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99272154238469423238602335 148908231357704134857903503)
          ·
            refine ⟨223362347036556202286855255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148908231357704134857903503 223362347036556202286855255)
            ·
              refine ⟨335043520554834303430282883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223362347036556202286855255 335043520554834303430282883)
              ·
                refine ⟨502565280832251455145424325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335043520554834303430282883 502565280832251455145424325)
                ·
                  refine ⟨94230990156047147839767061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502565280832251455145424325 94230990156047147839767061)
                  ·
                    refine ⟨4417077663564710054989081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94230990156047147839767061 4417077663564710054989081)
                    ·
                      refine ⟨3312808247673532541241811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417077663564710054989081 3312808247673532541241811)
                      ·
                        rfl

theorem cell23_6451671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_6451671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451671 prefixEnd_6451671 := by exact prefixLift 6451671
  have htrace : WordTrace (prefixWord ++ tailWord_6451671) baseStart_6451671 baseEnd_6451671 := by
    simpa [prefixWord, tailWord_6451671, baseEnd_6451671] using wordTrace_append hprefix tailTrace_6451671
  have hstable : (prefixWord ++ tailWord_6451671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451671).length < 2 ^ (prefixWord ++ tailWord_6451671).sum := by decide
  have hdescent : baseEnd_6451671 < baseStart_6451671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451681 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 1, 6]
def baseStart_6451681 : Nat := 118140960795 + 6451681 * 2 ^ 59
def prefixEnd_6451681 : Nat := 4983230072969 + 3 ^ 40 * 6451681 * 2
def baseEnd_6451681 : Nat := 1104271127493359167372255

theorem tailTrace_6451681 : CollatzResearch.WordTrace tailWord_6451681 prefixEnd_6451681 1104271127493359167372255 := by
  unfold tailWord_6451681
  simp only [CollatzResearch.WordTrace]
  refine ⟨235312137739669071236402897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156874758493112714157601931 235312137739669071236402897)
  ·
    refine ⟨176484103304751803427302173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235312137739669071236402897 176484103304751803427302173)
    ·
      refine ⟨66181538739281926285238315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176484103304751803427302173 66181538739281926285238315)
      ·
        refine ⟨99272308108922889427857473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66181538739281926285238315 99272308108922889427857473)
        ·
          refine ⟨74454231081692167070893105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99272308108922889427857473 74454231081692167070893105)
          ·
            refine ⟨55840673311269125303169829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74454231081692167070893105 55840673311269125303169829)
            ·
              refine ⟨10470126245862960994344343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55840673311269125303169829 10470126245862960994344343)
              ·
                refine ⟨15705189368794441491516515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10470126245862960994344343 15705189368794441491516515)
                ·
                  refine ⟨23557784053191662237274773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15705189368794441491516515 23557784053191662237274773)
                  ·
                    refine ⟨1104271127493359167372255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23557784053191662237274773 1104271127493359167372255)
                    ·
                      rfl

theorem cell23_6451681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_6451681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451681 prefixEnd_6451681 := by exact prefixLift 6451681
  have htrace : WordTrace (prefixWord ++ tailWord_6451681) baseStart_6451681 baseEnd_6451681 := by
    simpa [prefixWord, tailWord_6451681, baseEnd_6451681] using wordTrace_append hprefix tailTrace_6451681
  have hstable : (prefixWord ++ tailWord_6451681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451681).length < 2 ^ (prefixWord ++ tailWord_6451681).sum := by decide
  have hdescent : baseEnd_6451681 < baseStart_6451681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451691 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 3]
def baseStart_6451691 : Nat := 118140960795 + 6451691 * 2 ^ 59
def prefixEnd_6451691 : Nat := 4983230072969 + 3 ^ 40 * 6451691 * 2
def baseEnd_6451691 : Nat := 3312818517286622462991719

theorem tailTrace_6451691 : CollatzResearch.WordTrace tailWord_6451691 prefixEnd_6451691 3312818517286622462991719 := by
  unfold tailWord_6451691
  simp only [CollatzResearch.WordTrace]
  refine ⟨235312502469632842944266927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156875001646421895296177951 235312502469632842944266927)
  ·
    refine ⟨352968753704449264416400391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235312502469632842944266927 352968753704449264416400391)
    ·
      refine ⟨529453130556673896624600587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352968753704449264416400391 529453130556673896624600587)
      ·
        refine ⟨794179695835010844936900881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529453130556673896624600587 794179695835010844936900881)
        ·
          refine ⟨595634771876258133702675661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 794179695835010844936900881 595634771876258133702675661)
          ·
            refine ⟨223363039453596800138503373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 595634771876258133702675661 223363039453596800138503373)
            ·
              refine ⟨83761139795098800051938765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223363039453596800138503373 83761139795098800051938765)
              ·
                refine ⟨31410427423162050019477037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83761139795098800051938765 31410427423162050019477037)
                ·
                  refine ⟨11778910283685768757303889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31410427423162050019477037 11778910283685768757303889)
                  ·
                    refine ⟨8834182712764326567977917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11778910283685768757303889 8834182712764326567977917)
                    ·
                      refine ⟨3312818517286622462991719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8834182712764326567977917 3312818517286622462991719)
                      ·
                        rfl

theorem cell23_6451691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 3].length) (baseStart_6451691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451691 prefixEnd_6451691 := by exact prefixLift 6451691
  have htrace : WordTrace (prefixWord ++ tailWord_6451691) baseStart_6451691 baseEnd_6451691 := by
    simpa [prefixWord, tailWord_6451691, baseEnd_6451691] using wordTrace_append hprefix tailTrace_6451691
  have hstable : (prefixWord ++ tailWord_6451691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451691).length < 2 ^ (prefixWord ++ tailWord_6451691).sum := by decide
  have hdescent : baseEnd_6451691 < baseStart_6451691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451722 : List Nat := [3, 1, 2, 2, 2, 1, 1, 6, 1, 2, 2]
def baseStart_6451722 : Nat := 118140960795 + 6451722 * 2 ^ 59
def prefixEnd_6451722 : Nat := 4983230072969 + 3 ^ 40 * 6451722 * 2
def baseEnd_6451722 : Nat := 3312834435186911841704077

theorem tailTrace_6451722 : CollatzResearch.WordTrace tailWord_6451722 prefixEnd_6451722 3312834435186911841704077 := by
  unfold tailWord_6451722
  simp only [CollatzResearch.WordTrace]
  refine ⟨58828408283130133809661355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156875755421680356825763613 58828408283130133809661355)
  ·
    refine ⟨88242612424695200714492033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58828408283130133809661355 88242612424695200714492033)
    ·
      refine ⟨66181959318521400535869025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88242612424695200714492033 66181959318521400535869025)
      ·
        refine ⟨49636469488891050401901769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66181959318521400535869025 49636469488891050401901769)
        ·
          refine ⟨37227352116668287801426327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49636469488891050401901769 37227352116668287801426327)
          ·
            refine ⟨55841028175002431702139491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37227352116668287801426327 55841028175002431702139491)
            ·
              refine ⟨83761542262503647553209237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55841028175002431702139491 83761542262503647553209237)
              ·
                refine ⟨3926322293554858479056683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83761542262503647553209237 3926322293554858479056683)
                ·
                  refine ⟨5889483440332287718585025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926322293554858479056683 5889483440332287718585025)
                  ·
                    refine ⟨4417112580249215788938769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5889483440332287718585025 4417112580249215788938769)
                    ·
                      refine ⟨3312834435186911841704077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417112580249215788938769 3312834435186911841704077)
                      ·
                        rfl

theorem cell23_6451722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_6451722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451722 prefixEnd_6451722 := by exact prefixLift 6451722
  have htrace : WordTrace (prefixWord ++ tailWord_6451722) baseStart_6451722 baseEnd_6451722 := by
    simpa [prefixWord, tailWord_6451722, baseEnd_6451722] using wordTrace_append hprefix tailTrace_6451722
  have hstable : (prefixWord ++ tailWord_6451722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451722).length < 2 ^ (prefixWord ++ tailWord_6451722).sum := by decide
  have hdescent : baseEnd_6451722 < baseStart_6451722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451725 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6451725 : Nat := 118140960795 + 6451725 * 2 ^ 59
def prefixEnd_6451725 : Nat := 4983230072969 + 3 ^ 40 * 6451725 * 2
def baseEnd_6451725 : Nat := 3312835975628875329966563

theorem tailTrace_6451725 : CollatzResearch.WordTrace tailWord_6451725 prefixEnd_6451725 3312835975628875329966563 := by
  unfold tailWord_6451725
  simp only [CollatzResearch.WordTrace]
  refine ⟨235313742551509666751004629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156875828367673111167336419 235313742551509666751004629)
  ·
    refine ⟨5515165841051007814476671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 235313742551509666751004629 5515165841051007814476671)
    ·
      refine ⟨8272748761576511721715007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5515165841051007814476671 8272748761576511721715007)
      ·
        refine ⟨12409123142364767582572511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8272748761576511721715007 12409123142364767582572511)
        ·
          refine ⟨18613684713547151373858767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12409123142364767582572511 18613684713547151373858767)
          ·
            refine ⟨27920527070320727060788151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18613684713547151373858767 27920527070320727060788151)
            ·
              refine ⟨41880790605481090591182227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27920527070320727060788151 41880790605481090591182227)
              ·
                refine ⟨62821185908221635886773341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41880790605481090591182227 62821185908221635886773341)
                ·
                  refine ⟨23557944715583113457540003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62821185908221635886773341 23557944715583113457540003)
                  ·
                    refine ⟨35336917073374670186310005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23557944715583113457540003 35336917073374670186310005)
                    ·
                      refine ⟨3312835975628875329966563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35336917073374670186310005 3312835975628875329966563)
                      ·
                        rfl

theorem cell23_6451725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6451725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451725 prefixEnd_6451725 := by exact prefixLift 6451725
  have htrace : WordTrace (prefixWord ++ tailWord_6451725) baseStart_6451725 baseEnd_6451725 := by
    simpa [prefixWord, tailWord_6451725, baseEnd_6451725] using wordTrace_append hprefix tailTrace_6451725
  have hstable : (prefixWord ++ tailWord_6451725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451725).length < 2 ^ (prefixWord ++ tailWord_6451725).sum := by decide
  have hdescent : baseEnd_6451725 < baseStart_6451725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451738 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3]
def baseStart_6451738 : Nat := 118140960795 + 6451738 * 2 ^ 59
def prefixEnd_6451738 : Nat := 4983230072969 + 3 ^ 40 * 6451738 * 2
def baseEnd_6451738 : Nat := 3312842650877383779104003

theorem tailTrace_6451738 : CollatzResearch.WordTrace tailWord_6451738 prefixEnd_6451738 3312842650877383779104003 := by
  unfold tailWord_6451738
  simp only [CollatzResearch.WordTrace]
  refine ⟨58828554175115642492806967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156876144466975046647485245 58828554175115642492806967)
  ·
    refine ⟨88242831262673463739210451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58828554175115642492806967 88242831262673463739210451)
    ·
      refine ⟨132364246894010195608815677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88242831262673463739210451 132364246894010195608815677)
      ·
        refine ⟨49636592585253823353305879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132364246894010195608815677 49636592585253823353305879)
        ·
          refine ⟨74454888877880735029958819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49636592585253823353305879 74454888877880735029958819)
          ·
            refine ⟨111682333316821102544938229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74454888877880735029958819 111682333316821102544938229)
            ·
              refine ⟨10470218748451978363587959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111682333316821102544938229 10470218748451978363587959)
              ·
                refine ⟨15705328122677967545381939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10470218748451978363587959 15705328122677967545381939)
                ·
                  refine ⟨23557992184016951318072909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15705328122677967545381939 23557992184016951318072909)
                  ·
                    refine ⟨8834247069006356744277341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23557992184016951318072909 8834247069006356744277341)
                    ·
                      refine ⟨3312842650877383779104003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8834247069006356744277341 3312842650877383779104003)
                      ·
                        rfl

theorem cell23_6451738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_6451738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451738 prefixEnd_6451738 := by exact prefixLift 6451738
  have htrace : WordTrace (prefixWord ++ tailWord_6451738) baseStart_6451738 baseEnd_6451738 := by
    simpa [prefixWord, tailWord_6451738, baseEnd_6451738] using wordTrace_append hprefix tailTrace_6451738
  have hstable : (prefixWord ++ tailWord_6451738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451738).length < 2 ^ (prefixWord ++ tailWord_6451738).sum := by decide
  have hdescent : baseEnd_6451738 < baseStart_6451738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451765 : List Nat := [1, 3, 3, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_6451765 : Nat := 118140960795 + 6451765 * 2 ^ 59
def prefixEnd_6451765 : Nat := 4983230072969 + 3 ^ 40 * 6451765 * 2
def baseEnd_6451765 : Nat := 3312856514855055173466379

theorem tailTrace_6451765 : CollatzResearch.WordTrace tailWord_6451765 prefixEnd_6451765 3312856514855055173466379 := by
  unfold tailWord_6451765
  simp only [CollatzResearch.WordTrace]
  refine ⟨235315201471364753582460749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156876800980909835721640499 235315201471364753582460749)
  ·
    refine ⟨88243200551761782593422781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235315201471364753582460749 88243200551761782593422781)
    ·
      refine ⟨33091200206910668472533543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88243200551761782593422781 33091200206910668472533543)
      ·
        refine ⟨49636800310366002708800315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33091200206910668472533543 49636800310366002708800315)
        ·
          refine ⟨74455200465549004063200473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49636800310366002708800315 74455200465549004063200473)
          ·
            refine ⟨55841400349161753047400355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74455200465549004063200473 55841400349161753047400355)
            ·
              refine ⟨83762100523742629571100533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55841400349161753047400355 83762100523742629571100533)
              ·
                refine ⟨7852696924100871522290675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83762100523742629571100533 7852696924100871522290675)
                ·
                  refine ⟨11779045386151307283436013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7852696924100871522290675 11779045386151307283436013)
                  ·
                    refine ⟨4417142019806740231288505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11779045386151307283436013 4417142019806740231288505)
                    ·
                      refine ⟨3312856514855055173466379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417142019806740231288505 3312856514855055173466379)
                      ·
                        rfl

theorem cell23_6451765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_6451765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451765 prefixEnd_6451765 := by exact prefixLift 6451765
  have htrace : WordTrace (prefixWord ++ tailWord_6451765) baseStart_6451765 baseEnd_6451765 := by
    simpa [prefixWord, tailWord_6451765, baseEnd_6451765] using wordTrace_append hprefix tailTrace_6451765
  have hstable : (prefixWord ++ tailWord_6451765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451765).length < 2 ^ (prefixWord ++ tailWord_6451765).sum := by decide
  have hdescent : baseEnd_6451765 < baseStart_6451765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451789 : List Nat := [1, 6, 1, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_6451789 : Nat := 118140960795 + 6451789 * 2 ^ 59
def prefixEnd_6451789 : Nat := 4983230072969 + 3 ^ 40 * 6451789 * 2
def baseEnd_6451789 : Nat := 3312868838390763079566269

theorem tailTrace_6451789 : CollatzResearch.WordTrace tailWord_6451789 prefixEnd_6451789 3312868838390763079566269 := by
  unfold tailWord_6451789
  simp only [CollatzResearch.WordTrace]
  refine ⟨235316076823277805681334421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156877384548851870454222947 235316076823277805681334421)
  ·
    refine ⟨11030441101091147141312551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 235316076823277805681334421 11030441101091147141312551)
    ·
      refine ⟨16545661651636720711968827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11030441101091147141312551 16545661651636720711968827)
      ·
        refine ⟨24818492477455081067953241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16545661651636720711968827 24818492477455081067953241)
        ·
          refine ⟨18613869358091310800964931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24818492477455081067953241 18613869358091310800964931)
          ·
            refine ⟨27920804037136966201447397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18613869358091310800964931 27920804037136966201447397)
            ·
              refine ⟨5235150756963181162771387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27920804037136966201447397 5235150756963181162771387)
              ·
                refine ⟨7852726135444771744157081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5235150756963181162771387 7852726135444771744157081)
                ·
                  refine ⟨5889544601583578808117811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7852726135444771744157081 5889544601583578808117811)
                  ·
                    refine ⟨8834316902375368212176717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5889544601583578808117811 8834316902375368212176717)
                    ·
                      refine ⟨3312868838390763079566269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8834316902375368212176717 3312868838390763079566269)
                      ·
                        rfl

theorem cell23_6451789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_6451789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451789 prefixEnd_6451789 := by exact prefixLift 6451789
  have htrace : WordTrace (prefixWord ++ tailWord_6451789) baseStart_6451789 baseEnd_6451789 := by
    simpa [prefixWord, tailWord_6451789, baseEnd_6451789] using wordTrace_append hprefix tailTrace_6451789
  have hstable : (prefixWord ++ tailWord_6451789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451789).length < 2 ^ (prefixWord ++ tailWord_6451789).sum := by decide
  have hdescent : baseEnd_6451789 < baseStart_6451789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451791 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 4]
def baseStart_6451791 : Nat := 118140960795 + 6451791 * 2 ^ 59
def prefixEnd_6451791 : Nat := 4983230072969 + 3 ^ 40 * 6451791 * 2
def baseEnd_6451791 : Nat := 3312869865352072071741259

theorem tailTrace_6451791 : CollatzResearch.WordTrace tailWord_6451791 prefixEnd_6451791 3312869865352072071741259 := by
  unfold tailWord_6451791
  simp only [CollatzResearch.WordTrace]
  refine ⟨235316149769270560022907227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156877433179513706681938151 235316149769270560022907227)
  ·
    refine ⟨352974224653905840034360841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235316149769270560022907227 352974224653905840034360841)
    ·
      refine ⟨264730668490429380025770631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352974224653905840034360841 264730668490429380025770631)
      ·
        refine ⟨397096002735644070038655947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264730668490429380025770631 397096002735644070038655947)
        ·
          refine ⟨595644004103466105057983921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397096002735644070038655947 595644004103466105057983921)
          ·
            refine ⟨446733003077599578793487941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595644004103466105057983921 446733003077599578793487941)
            ·
              refine ⟨83762438077049921023778989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 446733003077599578793487941 83762438077049921023778989)
              ·
                refine ⟨31410914278893720383917121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83762438077049921023778989 31410914278893720383917121)
                ·
                  refine ⟨23558185709170290287937841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31410914278893720383917121 23558185709170290287937841)
                  ·
                    refine ⟨17668639281877717715953381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23558185709170290287937841 17668639281877717715953381)
                    ·
                      refine ⟨3312869865352072071741259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17668639281877717715953381 3312869865352072071741259)
                      ·
                        rfl

theorem cell23_6451791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_6451791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451791 prefixEnd_6451791 := by exact prefixLift 6451791
  have htrace : WordTrace (prefixWord ++ tailWord_6451791) baseStart_6451791 baseEnd_6451791 := by
    simpa [prefixWord, tailWord_6451791, baseEnd_6451791] using wordTrace_append hprefix tailTrace_6451791
  have hstable : (prefixWord ++ tailWord_6451791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451791).length < 2 ^ (prefixWord ++ tailWord_6451791).sum := by decide
  have hdescent : baseEnd_6451791 < baseStart_6451791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451881 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 6]
def baseStart_6451881 : Nat := 118140960795 + 6451881 * 2 ^ 59
def prefixEnd_6451881 : Nat := 4983230072969 + 3 ^ 40 * 6451881 * 2
def baseEnd_6451881 : Nat := 3312916078610976719615845

theorem tailTrace_6451881 : CollatzResearch.WordTrace tailWord_6451881 prefixEnd_6451881 3312916078610976719615845 := by
  unfold tailWord_6451881
  simp only [CollatzResearch.WordTrace]
  refine ⟨235319432338944505393683497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156879621559296336929122331 235319432338944505393683497)
  ·
    refine ⟨176489574254208379045262623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235319432338944505393683497 176489574254208379045262623)
    ·
      refine ⟨264734361381312568567893935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176489574254208379045262623 264734361381312568567893935)
      ·
        refine ⟨397101542071968852851840903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264734361381312568567893935 397101542071968852851840903)
        ·
          refine ⟨595652313107953279277761355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397101542071968852851840903 595652313107953279277761355)
          ·
            refine ⟨893478469661929918916642033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595652313107953279277761355 893478469661929918916642033)
            ·
              refine ⟨670108852246447439187481525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893478469661929918916642033 670108852246447439187481525)
              ·
                refine ⟨62822704898104447423826393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 670108852246447439187481525 62822704898104447423826393)
                ·
                  refine ⟨47117028673578335567869795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62822704898104447423826393 47117028673578335567869795)
                  ·
                    refine ⟨70675543010367503351804693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47117028673578335567869795 70675543010367503351804693)
                    ·
                      refine ⟨3312916078610976719615845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70675543010367503351804693 3312916078610976719615845)
                      ·
                        rfl

theorem cell23_6451881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_6451881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451881 prefixEnd_6451881 := by exact prefixLift 6451881
  have htrace : WordTrace (prefixWord ++ tailWord_6451881) baseStart_6451881 baseEnd_6451881 := by
    simpa [prefixWord, tailWord_6451881, baseEnd_6451881] using wordTrace_append hprefix tailTrace_6451881
  have hstable : (prefixWord ++ tailWord_6451881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451881).length < 2 ^ (prefixWord ++ tailWord_6451881).sum := by decide
  have hdescent : baseEnd_6451881 < baseStart_6451881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451888 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 3]
def baseStart_6451888 : Nat := 118140960795 + 6451888 * 2 ^ 59
def prefixEnd_6451888 : Nat := 4983230072969 + 3 ^ 40 * 6451888 * 2
def baseEnd_6451888 : Nat := 3312919672975558192228313

theorem tailTrace_6451888 : CollatzResearch.WordTrace tailWord_6451888 prefixEnd_6451888 3312919672975558192228313 := by
  unfold tailWord_6451888
  simp only [CollatzResearch.WordTrace]
  refine ⟨117659843824959572794594159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156879791766612763726125545 117659843824959572794594159)
  ·
    refine ⟨176489765737439359191891239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117659843824959572794594159 176489765737439359191891239)
    ·
      refine ⟨264734648606159038787836859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176489765737439359191891239 264734648606159038787836859)
      ·
        refine ⟨397101972909238558181755289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264734648606159038787836859 397101972909238558181755289)
        ·
          refine ⟨297826479681928918636316467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397101972909238558181755289 297826479681928918636316467)
          ·
            refine ⟨446739719522893377954474701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297826479681928918636316467 446739719522893377954474701)
            ·
              refine ⟨167527394821085016732928013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 446739719522893377954474701 167527394821085016732928013)
              ·
                refine ⟨62822773057906881274848005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167527394821085016732928013 62822773057906881274848005)
                ·
                  refine ⟨11779269948357540239034001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62822773057906881274848005 11779269948357540239034001)
                  ·
                    refine ⟨8834452461268155179275501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11779269948357540239034001 8834452461268155179275501)
                    ·
                      refine ⟨3312919672975558192228313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8834452461268155179275501 3312919672975558192228313)
                      ·
                        rfl

theorem cell23_6451888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 3].length) (baseStart_6451888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451888 prefixEnd_6451888 := by exact prefixLift 6451888
  have htrace : WordTrace (prefixWord ++ tailWord_6451888) baseStart_6451888 baseEnd_6451888 := by
    simpa [prefixWord, tailWord_6451888, baseEnd_6451888] using wordTrace_append hprefix tailTrace_6451888
  have hstable : (prefixWord ++ tailWord_6451888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451888).length < 2 ^ (prefixWord ++ tailWord_6451888).sum := by decide
  have hdescent : baseEnd_6451888 < baseStart_6451888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451931 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 7]
def baseStart_6451931 : Nat := 118140960795 + 6451931 * 2 ^ 59
def prefixEnd_6451931 : Nat := 4983230072969 + 3 ^ 40 * 6451931 * 2
def baseEnd_6451931 : Nat := 3312941752643701523990615

theorem tailTrace_6451931 : CollatzResearch.WordTrace tailWord_6451931 prefixEnd_6451931 3312941752643701523990615 := by
  unfold tailWord_6451931
  simp only [CollatzResearch.WordTrace]
  refine ⟨235321255988763363933003647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156880837325842242622002431 235321255988763363933003647)
  ·
    refine ⟨352981883983145045899505471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235321255988763363933003647 352981883983145045899505471)
    ·
      refine ⟨529472825974717568849258207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352981883983145045899505471 529472825974717568849258207)
      ·
        refine ⟨794209238962076353273887311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529472825974717568849258207 794209238962076353273887311)
        ·
          refine ⟨1191313858443114529910830967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794209238962076353273887311 1191313858443114529910830967)
          ·
            refine ⟨1786970787664671794866246451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191313858443114529910830967 1786970787664671794866246451)
            ·
              refine ⟨2680456181497007692299369677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1786970787664671794866246451 2680456181497007692299369677)
              ·
                refine ⟨1005171068061377884612263629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2680456181497007692299369677 1005171068061377884612263629)
                ·
                  refine ⟨376939150523016706729598861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1005171068061377884612263629 376939150523016706729598861)
                  ·
                    refine ⟨141352181446131265023599573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 376939150523016706729598861 141352181446131265023599573)
                    ·
                      refine ⟨3312941752643701523990615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141352181446131265023599573 3312941752643701523990615)
                      ·
                        rfl

theorem cell23_6451931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_6451931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451931 prefixEnd_6451931 := by exact prefixLift 6451931
  have htrace : WordTrace (prefixWord ++ tailWord_6451931) baseStart_6451931 baseEnd_6451931 := by
    simpa [prefixWord, tailWord_6451931, baseEnd_6451931] using wordTrace_append hprefix tailTrace_6451931
  have hstable : (prefixWord ++ tailWord_6451931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451931).length < 2 ^ (prefixWord ++ tailWord_6451931).sum := by decide
  have hdescent : baseEnd_6451931 < baseStart_6451931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6451945 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 4, 3, 2]
def baseStart_6451945 : Nat := 118140960795 + 6451945 * 2 ^ 59
def prefixEnd_6451945 : Nat := 4983230072969 + 3 ^ 40 * 6451945 * 2
def baseEnd_6451945 : Nat := 3312948941372864469215551

theorem tailTrace_6451945 : CollatzResearch.WordTrace tailWord_6451945 prefixEnd_6451945 3312948941372864469215551 := by
  unfold tailWord_6451945
  simp only [CollatzResearch.WordTrace]
  refine ⟨235321766610712644324013289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156881177740475096216008859 235321766610712644324013289)
  ·
    refine ⟨176491324958034483243009967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235321766610712644324013289 176491324958034483243009967)
    ·
      refine ⟨264736987437051724864514951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176491324958034483243009967 264736987437051724864514951)
      ·
        refine ⟨397105481155577587296772427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264736987437051724864514951 397105481155577587296772427)
        ·
          refine ⟨595658221733366380945158641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397105481155577587296772427 595658221733366380945158641)
          ·
            refine ⟨446743666300024785708868981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595658221733366380945158641 446743666300024785708868981)
            ·
              refine ⟨41882218715627323660206467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 446743666300024785708868981 41882218715627323660206467)
              ·
                refine ⟨62823328073440985490309701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41882218715627323660206467 62823328073440985490309701)
                ·
                  refine ⟨11779374013770184779433069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62823328073440985490309701 11779374013770184779433069)
                  ·
                    refine ⟨4417265255163819292287401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11779374013770184779433069 4417265255163819292287401)
                    ·
                      refine ⟨3312948941372864469215551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417265255163819292287401 3312948941372864469215551)
                      ·
                        rfl

theorem cell23_6451945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 3, 2].length) (baseStart_6451945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6451945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6451945 prefixEnd_6451945 := by exact prefixLift 6451945
  have htrace : WordTrace (prefixWord ++ tailWord_6451945) baseStart_6451945 baseEnd_6451945 := by
    simpa [prefixWord, tailWord_6451945, baseEnd_6451945] using wordTrace_append hprefix tailTrace_6451945
  have hstable : (prefixWord ++ tailWord_6451945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6451945).length < 2 ^ (prefixWord ++ tailWord_6451945).sum := by decide
  have hdescent : baseEnd_6451945 < baseStart_6451945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6451945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452002 : List Nat := [3, 3, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_6452002 : Nat := 118140960795 + 6452002 * 2 ^ 59
def prefixEnd_6452002 : Nat := 4983230072969 + 3 ^ 40 * 6452002 * 2
def baseEnd_6452002 : Nat := 1104326069923390248734263

theorem tailTrace_6452002 : CollatzResearch.WordTrace tailWord_6452002 prefixEnd_6452002 1104326069923390248734263 := by
  unfold tailWord_6452002
  simp only [CollatzResearch.WordTrace]
  refine ⟨58830961392876535764709565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156882563714337428705892173 58830961392876535764709565)
  ·
    refine ⟨22061610522328700911766087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58830961392876535764709565 22061610522328700911766087)
    ·
      refine ⟨33092415783493051367649131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22061610522328700911766087 33092415783493051367649131)
      ·
        refine ⟨49638623675239577051473697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33092415783493051367649131 49638623675239577051473697)
        ·
          refine ⟨37228967756429682788605273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49638623675239577051473697 37228967756429682788605273)
          ·
            refine ⟨27921725817322262091453955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37228967756429682788605273 27921725817322262091453955)
            ·
              refine ⟨41882588725983393137180933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27921725817322262091453955 41882588725983393137180933)
              ·
                refine ⟨7852985386121886213221425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41882588725983393137180933 7852985386121886213221425)
                ·
                  refine ⟨5889739039591414659916069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7852985386121886213221425 5889739039591414659916069)
                  ·
                    refine ⟨1104326069923390248734263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5889739039591414659916069 1104326069923390248734263)
                    ·
                      rfl

theorem cell23_6452002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_6452002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452002 prefixEnd_6452002 := by exact prefixLift 6452002
  have htrace : WordTrace (prefixWord ++ tailWord_6452002) baseStart_6452002 baseEnd_6452002 := by
    simpa [prefixWord, tailWord_6452002, baseEnd_6452002] using wordTrace_append hprefix tailTrace_6452002
  have hstable : (prefixWord ++ tailWord_6452002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452002).length < 2 ^ (prefixWord ++ tailWord_6452002).sum := by decide
  have hdescent : baseEnd_6452002 < baseStart_6452002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452009 : List Nat := [1, 2, 1, 1, 1, 1, 1, 10, 1, 2, 2]
def baseStart_6452009 : Nat := 118140960795 + 6452009 * 2 ^ 59
def prefixEnd_6452009 : Nat := 4983230072969 + 3 ^ 40 * 6452009 * 2
def baseEnd_6452009 : Nat := 3312981804134752218815257

theorem tailTrace_6452009 : CollatzResearch.WordTrace tailWord_6452009 prefixEnd_6452009 3312981804134752218815257 := by
  unfold tailWord_6452009
  simp only [CollatzResearch.WordTrace]
  refine ⟨235324100882480783254343081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156882733921653855502895387 235324100882480783254343081)
  ·
    refine ⟨176493075661860587440757311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235324100882480783254343081 176493075661860587440757311)
    ·
      refine ⟨264739613492790881161135967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176493075661860587440757311 264739613492790881161135967)
      ·
        refine ⟨397109420239186321741703951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264739613492790881161135967 397109420239186321741703951)
        ·
          refine ⟨595664130358779482612555927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397109420239186321741703951 595664130358779482612555927)
          ·
            refine ⟨893496195538169223918833891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595664130358779482612555927 893496195538169223918833891)
            ·
              refine ⟨1340244293307253835878250837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893496195538169223918833891 1340244293307253835878250837)
              ·
                refine ⟨3926496953048595222299563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1340244293307253835878250837 3926496953048595222299563)
                ·
                  refine ⟨5889745429572892833449345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926496953048595222299563 5889745429572892833449345)
                  ·
                    refine ⟨4417309072179669625087009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5889745429572892833449345 4417309072179669625087009)
                    ·
                      refine ⟨3312981804134752218815257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417309072179669625087009 3312981804134752218815257)
                      ·
                        rfl

theorem cell23_6452009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 1, 2, 2].length) (baseStart_6452009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452009 prefixEnd_6452009 := by exact prefixLift 6452009
  have htrace : WordTrace (prefixWord ++ tailWord_6452009) baseStart_6452009 baseEnd_6452009 := by
    simpa [prefixWord, tailWord_6452009, baseEnd_6452009] using wordTrace_append hprefix tailTrace_6452009
  have hstable : (prefixWord ++ tailWord_6452009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452009).length < 2 ^ (prefixWord ++ tailWord_6452009).sum := by decide
  have hdescent : baseEnd_6452009 < baseStart_6452009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452028 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 4, 7]
def baseStart_6452028 : Nat := 118140960795 + 6452028 * 2 ^ 59
def prefixEnd_6452028 : Nat := 4983230072969 + 3 ^ 40 * 6452028 * 2
def baseEnd_6452028 : Nat := 1104330520089062548159223

theorem tailTrace_6452028 : CollatzResearch.WordTrace tailWord_6452028 prefixEnd_6452028 1104330520089062548159223 := by
  unfold tailWord_6452028
  simp only [CollatzResearch.WordTrace]
  refine ⟨117662396934705974749642369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156883195912941299666189825 117662396934705974749642369)
  ·
    refine ⟨88246797701029481062231777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117662396934705974749642369 88246797701029481062231777)
    ·
      refine ⟨66185098275772110796673833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88246797701029481062231777 66185098275772110796673833)
      ·
        refine ⟨49638823706829083097505375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66185098275772110796673833 49638823706829083097505375)
        ·
          refine ⟨74458235560243624646258063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49638823706829083097505375 74458235560243624646258063)
          ·
            refine ⟨111687353340365436969387095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74458235560243624646258063 111687353340365436969387095)
            ·
              refine ⟨167531030010548155454080643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111687353340365436969387095 167531030010548155454080643)
              ·
                refine ⟨251296545015822233181120965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167531030010548155454080643 251296545015822233181120965)
                ·
                  refine ⟨47118102190466668721460181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251296545015822233181120965 47118102190466668721460181)
                  ·
                    refine ⟨1104330520089062548159223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47118102190466668721460181 1104330520089062548159223)
                    ·
                      rfl

theorem cell23_6452028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_6452028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452028 prefixEnd_6452028 := by exact prefixLift 6452028
  have htrace : WordTrace (prefixWord ++ tailWord_6452028) baseStart_6452028 baseEnd_6452028 := by
    simpa [prefixWord, tailWord_6452028, baseEnd_6452028] using wordTrace_append hprefix tailTrace_6452028
  have hstable : (prefixWord ++ tailWord_6452028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452028).length < 2 ^ (prefixWord ++ tailWord_6452028).sum := by decide
  have hdescent : baseEnd_6452028 < baseStart_6452028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452086 : List Nat := [5, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_6452086 : Nat := 118140960795 + 6452086 * 2 ^ 59
def prefixEnd_6452086 : Nat := 4983230072969 + 3 ^ 40 * 6452086 * 2
def baseEnd_6452086 : Nat := 3313021342145148417552403

theorem tailTrace_6452086 : CollatzResearch.WordTrace tailWord_6452086 prefixEnd_6452086 3313021342145148417552403 := by
  unfold tailWord_6452086
  simp only [CollatzResearch.WordTrace]
  refine ⟨14707931831450114087806007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156884606202134550269930741 14707931831450114087806007)
  ·
    refine ⟨22061897747175171131709011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14707931831450114087806007 22061897747175171131709011)
    ·
      refine ⟨33092846620762756697563517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22061897747175171131709011 33092846620762756697563517)
      ·
        refine ⟨12409817482786033761586319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33092846620762756697563517 12409817482786033761586319)
        ·
          refine ⟨18614726224179050642379479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12409817482786033761586319 18614726224179050642379479)
          ·
            refine ⟨27922089336268575963569219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18614726224179050642379479 27922089336268575963569219)
            ·
              refine ⟨41883134004402863945353829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27922089336268575963569219 41883134004402863945353829)
              ·
                refine ⟨7853087625825536989753843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41883134004402863945353829 7853087625825536989753843)
                ·
                  refine ⟨11779631438738305484630765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7853087625825536989753843 11779631438738305484630765)
                  ·
                    refine ⟨4417361789526864556736537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11779631438738305484630765 4417361789526864556736537)
                    ·
                      refine ⟨3313021342145148417552403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417361789526864556736537 3313021342145148417552403)
                      ·
                        rfl

theorem cell23_6452086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_6452086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452086 prefixEnd_6452086 := by exact prefixLift 6452086
  have htrace : WordTrace (prefixWord ++ tailWord_6452086) baseStart_6452086 baseEnd_6452086 := by
    simpa [prefixWord, tailWord_6452086, baseEnd_6452086] using wordTrace_append hprefix tailTrace_6452086
  have hstable : (prefixWord ++ tailWord_6452086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452086).length < 2 ^ (prefixWord ++ tailWord_6452086).sum := by decide
  have hdescent : baseEnd_6452086 < baseStart_6452086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452088 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 9]
def baseStart_6452088 : Nat := 118140960795 + 6452088 * 2 ^ 59
def prefixEnd_6452088 : Nat := 4983230072969 + 3 ^ 40 * 6452088 * 2
def baseEnd_6452088 : Nat := 368113596567384156636377

theorem tailTrace_6452088 : CollatzResearch.WordTrace tailWord_6452088 prefixEnd_6452088 368113596567384156636377 := by
  unfold tailWord_6452088
  simp only [CollatzResearch.WordTrace]
  refine ⟨117663491124597289873234459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156884654832796386497645945 117663491124597289873234459)
  ·
    refine ⟨176495236686895934809851689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117663491124597289873234459 176495236686895934809851689)
    ·
      refine ⟨132371427515171951107388767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176495236686895934809851689 132371427515171951107388767)
      ·
        refine ⟨198557141272757926661083151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132371427515171951107388767 198557141272757926661083151)
        ·
          refine ⟨297835711909136889991624727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198557141272757926661083151 297835711909136889991624727)
          ·
            refine ⟨446753567863705334987437091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297835711909136889991624727 446753567863705334987437091)
            ·
              refine ⟨670130351795558002481155637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446753567863705334987437091 670130351795558002481155637)
              ·
                refine ⟨62824720480833562732608341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 670130351795558002481155637 62824720480833562732608341)
                ·
                  refine ⟨368113596567384156636377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62824720480833562732608341 368113596567384156636377)
                  ·
                    rfl

theorem cell23_6452088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 9].length) (baseStart_6452088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452088 prefixEnd_6452088 := by exact prefixLift 6452088
  have htrace : WordTrace (prefixWord ++ tailWord_6452088) baseStart_6452088 baseEnd_6452088 := by
    simpa [prefixWord, tailWord_6452088, baseEnd_6452088] using wordTrace_append hprefix tailTrace_6452088
  have hstable : (prefixWord ++ tailWord_6452088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452088).length < 2 ^ (prefixWord ++ tailWord_6452088).sum := by decide
  have hdescent : baseEnd_6452088 < baseStart_6452088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452115 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 3]
def baseStart_6452115 : Nat := 118140960795 + 6452115 * 2 ^ 59
def prefixEnd_6452115 : Nat := 4983230072969 + 3 ^ 40 * 6452115 * 2
def baseEnd_6452115 : Nat := 3313036233084128804089769

theorem tailTrace_6452115 : CollatzResearch.WordTrace tailWord_6452115 prefixEnd_6452115 3313036233084128804089769 := by
  unfold tailWord_6452115
  simp only [CollatzResearch.WordTrace]
  refine ⟨235327967020096763357701799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156885311346731175571801199 235327967020096763357701799)
  ·
    refine ⟨352991950530145145036552699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235327967020096763357701799 352991950530145145036552699)
    ·
      refine ⟨529487925795217717554829049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352991950530145145036552699 529487925795217717554829049)
      ·
        refine ⟨397115944346413288166121787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529487925795217717554829049 397115944346413288166121787)
        ·
          refine ⟨595673916519619932249182681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397115944346413288166121787 595673916519619932249182681)
          ·
            refine ⟨446755437389714949186887011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595673916519619932249182681 446755437389714949186887011)
            ·
              refine ⟨670133156084572423780330517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446755437389714949186887011 670133156084572423780330517)
              ·
                refine ⟨31412491691464332364702993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 670133156084572423780330517 31412491691464332364702993)
                ·
                  refine ⟨23559368768598249273527245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31412491691464332364702993 23559368768598249273527245)
                  ·
                    refine ⟨8834763288224343477572717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23559368768598249273527245 8834763288224343477572717)
                    ·
                      refine ⟨3313036233084128804089769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8834763288224343477572717 3313036233084128804089769)
                      ·
                        rfl

theorem cell23_6452115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 3].length) (baseStart_6452115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452115 prefixEnd_6452115 := by exact prefixLift 6452115
  have htrace : WordTrace (prefixWord ++ tailWord_6452115) baseStart_6452115 baseEnd_6452115 := by
    simpa [prefixWord, tailWord_6452115, baseEnd_6452115] using wordTrace_append hprefix tailTrace_6452115
  have hstable : (prefixWord ++ tailWord_6452115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452115).length < 2 ^ (prefixWord ++ tailWord_6452115).sum := by decide
  have hdescent : baseEnd_6452115 < baseStart_6452115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452116 : List Nat := [2, 4, 2, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_6452116 : Nat := 118140960795 + 6452116 * 2 ^ 59
def prefixEnd_6452116 : Nat := 4983230072969 + 3 ^ 40 * 6452116 * 2
def baseEnd_6452116 : Nat := 3313036746564783300177265

theorem tailTrace_6452116 : CollatzResearch.WordTrace tailWord_6452116 prefixEnd_6452116 3313036746564783300177265 := by
  unfold tailWord_6452116
  simp only [CollatzResearch.WordTrace]
  refine ⟨117664001746546570264244101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156885335662062093685658801 117664001746546570264244101)
  ·
    refine ⟨22062000327477481924545769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117664001746546570264244101 22062000327477481924545769)
    ·
      refine ⟨16546500245608111443409327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22062000327477481924545769 16546500245608111443409327)
      ·
        refine ⟨24819750368412167165113991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16546500245608111443409327 24819750368412167165113991)
        ·
          refine ⟨37229625552618250747670987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24819750368412167165113991 37229625552618250747670987)
          ·
            refine ⟨55844438328927376121506481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37229625552618250747670987 55844438328927376121506481)
            ·
              refine ⟨41883328746695532091129861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55844438328927376121506481 41883328746695532091129861)
              ·
                refine ⟨7853124140005412267086849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41883328746695532091129861 7853124140005412267086849)
                ·
                  refine ⟨5889843105004059200315137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7853124140005412267086849 5889843105004059200315137)
                  ·
                    refine ⟨4417382328753044400236353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5889843105004059200315137 4417382328753044400236353)
                    ·
                      refine ⟨3313036746564783300177265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417382328753044400236353 3313036746564783300177265)
                      ·
                        rfl

theorem cell23_6452116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_6452116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452116 prefixEnd_6452116 := by exact prefixLift 6452116
  have htrace : WordTrace (prefixWord ++ tailWord_6452116) baseStart_6452116 baseEnd_6452116 := by
    simpa [prefixWord, tailWord_6452116, baseEnd_6452116] using wordTrace_append hprefix tailTrace_6452116
  have hstable : (prefixWord ++ tailWord_6452116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452116).length < 2 ^ (prefixWord ++ tailWord_6452116).sum := by decide
  have hdescent : baseEnd_6452116 < baseStart_6452116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452150 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6452150 : Nat := 118140960795 + 6452150 * 2 ^ 59
def prefixEnd_6452150 : Nat := 4983230072969 + 3 ^ 40 * 6452150 * 2
def baseEnd_6452150 : Nat := 3313054204907036167152109

theorem tailTrace_6452150 : CollatzResearch.WordTrace tailWord_6452150 prefixEnd_6452150 3313054204907036167152109 := by
  unfold tailWord_6452150
  simp only [CollatzResearch.WordTrace]
  refine ⟨14708077723435622770951619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156886162383313309556817269 14708077723435622770951619)
  ·
    refine ⟨22062116585153434156427429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14708077723435622770951619 22062116585153434156427429)
    ·
      refine ⟨4136646859716268904330143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22062116585153434156427429 4136646859716268904330143)
      ·
        refine ⟨6204970289574403356495215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4136646859716268904330143 6204970289574403356495215)
        ·
          refine ⟨9307455434361605034742823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6204970289574403356495215 9307455434361605034742823)
          ·
            refine ⟨13961183151542407552114235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9307455434361605034742823 13961183151542407552114235)
            ·
              refine ⟨20941774727313611328171353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13961183151542407552114235 20941774727313611328171353)
              ·
                refine ⟨15706331045485208496128515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20941774727313611328171353 15706331045485208496128515)
                ·
                  refine ⟨23559496568227812744192773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15706331045485208496128515 23559496568227812744192773)
                  ·
                    refine ⟨4417405606542714889536145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23559496568227812744192773 4417405606542714889536145)
                    ·
                      refine ⟨3313054204907036167152109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417405606542714889536145 3313054204907036167152109)
                      ·
                        rfl

theorem cell23_6452150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6452150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452150 prefixEnd_6452150 := by exact prefixLift 6452150
  have htrace : WordTrace (prefixWord ++ tailWord_6452150) baseStart_6452150 baseEnd_6452150 := by
    simpa [prefixWord, tailWord_6452150, baseEnd_6452150] using wordTrace_append hprefix tailTrace_6452150
  have hstable : (prefixWord ++ tailWord_6452150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452150).length < 2 ^ (prefixWord ++ tailWord_6452150).sum := by decide
  have hdescent : baseEnd_6452150 < baseStart_6452150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452152 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 2, 5]
def baseStart_6452152 : Nat := 118140960795 + 6452152 * 2 ^ 59
def prefixEnd_6452152 : Nat := 4983230072969 + 3 ^ 40 * 6452152 * 2
def baseEnd_6452152 : Nat := 1104351743956115053109033

theorem tailTrace_6452152 : CollatzResearch.WordTrace tailWord_6452152 prefixEnd_6452152 1104351743956115053109033 := by
  unfold tailWord_6452152
  simp only [CollatzResearch.WordTrace]
  refine ⟨117664658260481359338399355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156886211013975145784532473 117664658260481359338399355)
  ·
    refine ⟨176496987390722039007599033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117664658260481359338399355 176496987390722039007599033)
    ·
      refine ⟨132372740543041529255699275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176496987390722039007599033 132372740543041529255699275)
      ·
        refine ⟨198559110814562293883548913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132372740543041529255699275 198559110814562293883548913)
        ·
          refine ⟨148919333110921720412661685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198559110814562293883548913 148919333110921720412661685)
          ·
            refine ⟨13961187479148911288687033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148919333110921720412661685 13961187479148911288687033)
            ·
              refine ⟨10470890609361683466515275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13961187479148911288687033 10470890609361683466515275)
              ·
                refine ⟨15706335914042525199772913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10470890609361683466515275 15706335914042525199772913)
                ·
                  refine ⟨11779751935531893899829685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15706335914042525199772913 11779751935531893899829685)
                  ·
                    refine ⟨1104351743956115053109033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11779751935531893899829685 1104351743956115053109033)
                    ·
                      rfl

theorem cell23_6452152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_6452152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452152 prefixEnd_6452152 := by exact prefixLift 6452152
  have htrace : WordTrace (prefixWord ++ tailWord_6452152) baseStart_6452152 baseEnd_6452152 := by
    simpa [prefixWord, tailWord_6452152, baseEnd_6452152] using wordTrace_append hprefix tailTrace_6452152
  have hstable : (prefixWord ++ tailWord_6452152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452152).length < 2 ^ (prefixWord ++ tailWord_6452152).sum := by decide
  have hdescent : baseEnd_6452152 < baseStart_6452152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452172 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 2, 1, 4]
def baseStart_6452172 : Nat := 118140960795 + 6452172 * 2 ^ 59
def prefixEnd_6452172 : Nat := 4983230072969 + 3 ^ 40 * 6452172 * 2
def baseEnd_6452172 : Nat := 3313065501481435081077007

theorem tailTrace_6452172 : CollatzResearch.WordTrace tailWord_6452172 prefixEnd_6452172 3313065501481435081077007 := by
  unfold tailWord_6452172
  simp only [CollatzResearch.WordTrace]
  refine ⟨117665022990445131046263385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156886697320593508061684513 117665022990445131046263385)
  ·
    refine ⟨88248767242833848284697539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117665022990445131046263385 88248767242833848284697539)
    ·
      refine ⟨132373150864250772427046309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88248767242833848284697539 132373150864250772427046309)
      ·
        refine ⟨24819965787047019830071183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132373150864250772427046309 24819965787047019830071183)
        ·
          refine ⟨37229948680570529745106775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24819965787047019830071183 37229948680570529745106775)
          ·
            refine ⟨55844923020855794617660163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37229948680570529745106775 55844923020855794617660163)
            ·
              refine ⟨83767384531283691926490245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55844923020855794617660163 83767384531283691926490245)
              ·
                refine ⟨15706384599615692236216921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83767384531283691926490245 15706384599615692236216921)
                ·
                  refine ⟨11779788449711769177162691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15706384599615692236216921 11779788449711769177162691)
                  ·
                    refine ⟨17669682674567653765744037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11779788449711769177162691 17669682674567653765744037)
                    ·
                      refine ⟨3313065501481435081077007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17669682674567653765744037 3313065501481435081077007)
                      ·
                        rfl

theorem cell23_6452172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_6452172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452172 prefixEnd_6452172 := by exact prefixLift 6452172
  have htrace : WordTrace (prefixWord ++ tailWord_6452172) baseStart_6452172 baseEnd_6452172 := by
    simpa [prefixWord, tailWord_6452172, baseEnd_6452172] using wordTrace_append hprefix tailTrace_6452172
  have hstable : (prefixWord ++ tailWord_6452172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452172).length < 2 ^ (prefixWord ++ tailWord_6452172).sum := by decide
  have hdescent : baseEnd_6452172 < baseStart_6452172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452189 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_6452189 : Nat := 118140960795 + 6452189 * 2 ^ 59
def prefixEnd_6452189 : Nat := 4983230072969 + 3 ^ 40 * 6452189 * 2
def baseEnd_6452189 : Nat := 3313074230652561514564429

theorem tailTrace_6452189 : CollatzResearch.WordTrace tailWord_6452189 prefixEnd_6452189 3313074230652561514564429 := by
  unfold tailWord_6452189
  simp only [CollatzResearch.WordTrace]
  refine ⟨235330666021828673995895621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156887110681219115997263747 235330666021828673995895621)
  ·
    refine ⟨44124499879092876374230429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235330666021828673995895621 44124499879092876374230429)
    ·
      refine ⟨16546687454659828640336411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44124499879092876374230429 16546687454659828640336411)
      ·
        refine ⟨24820031181989742960504617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16546687454659828640336411 24820031181989742960504617)
        ·
          refine ⟨18615023386492307220378463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24820031181989742960504617 18615023386492307220378463)
          ·
            refine ⟨27922535079738460830567695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18615023386492307220378463 27922535079738460830567695)
            ·
              refine ⟨41883802619607691245851543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27922535079738460830567695 41883802619607691245851543)
              ·
                refine ⟨62825703929411536868777315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41883802619607691245851543 62825703929411536868777315)
                ·
                  refine ⟨94238555894117305303165973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62825703929411536868777315 94238555894117305303165973)
                  ·
                    refine ⟨4417432307536748686085905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94238555894117305303165973 4417432307536748686085905)
                    ·
                      refine ⟨3313074230652561514564429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417432307536748686085905 3313074230652561514564429)
                      ·
                        rfl

theorem cell23_6452189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_6452189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452189 prefixEnd_6452189 := by exact prefixLift 6452189
  have htrace : WordTrace (prefixWord ++ tailWord_6452189) baseStart_6452189 baseEnd_6452189 := by
    simpa [prefixWord, tailWord_6452189, baseEnd_6452189] using wordTrace_append hprefix tailTrace_6452189
  have hstable : (prefixWord ++ tailWord_6452189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452189).length < 2 ^ (prefixWord ++ tailWord_6452189).sum := by decide
  have hdescent : baseEnd_6452189 < baseStart_6452189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452199 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 3, 4]
def baseStart_6452199 : Nat := 118140960795 + 6452199 * 2 ^ 59
def prefixEnd_6452199 : Nat := 4983230072969 + 3 ^ 40 * 6452199 * 2
def baseEnd_6452199 : Nat := 1104359788486368825146461

theorem tailTrace_6452199 : CollatzResearch.WordTrace tailWord_6452199 prefixEnd_6452199 1104359788486368825146461 := by
  unfold tailWord_6452199
  simp only [CollatzResearch.WordTrace]
  refine ⟨235331030751792445703759651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156887353834528297135839767 235331030751792445703759651)
  ·
    refine ⟨352996546127688668555639477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235331030751792445703759651 352996546127688668555639477)
    ·
      refine ⟨33093426199470812677091201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 352996546127688668555639477 33093426199470812677091201)
      ·
        refine ⟨24820069649603109507818401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33093426199470812677091201 24820069649603109507818401)
        ·
          refine ⟨18615052237202332130863801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24820069649603109507818401 18615052237202332130863801)
          ·
            refine ⟨13961289177901749098147851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18615052237202332130863801 13961289177901749098147851)
            ·
              refine ⟨20941933766852623647221777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13961289177901749098147851 20941933766852623647221777)
              ·
                refine ⟨15706450325139467735416333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20941933766852623647221777 15706450325139467735416333)
                ·
                  refine ⟨5889918871927300400781125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15706450325139467735416333 5889918871927300400781125)
                  ·
                    refine ⟨1104359788486368825146461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5889918871927300400781125 1104359788486368825146461)
                    ·
                      rfl

theorem cell23_6452199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_6452199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452199 prefixEnd_6452199 := by exact prefixLift 6452199
  have htrace : WordTrace (prefixWord ++ tailWord_6452199) baseStart_6452199 baseEnd_6452199 := by
    simpa [prefixWord, tailWord_6452199, baseEnd_6452199] using wordTrace_append hprefix tailTrace_6452199
  have hstable : (prefixWord ++ tailWord_6452199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452199).length < 2 ^ (prefixWord ++ tailWord_6452199).sum := by decide
  have hdescent : baseEnd_6452199 < baseStart_6452199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452206 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_6452206 : Nat := 118140960795 + 6452206 * 2 ^ 59
def prefixEnd_6452206 : Nat := 4983230072969 + 3 ^ 40 * 6452206 * 2
def baseEnd_6452206 : Nat := 3313082959823687948051851

theorem tailTrace_6452206 : CollatzResearch.WordTrace tailWord_6452206 prefixEnd_6452206 3313082959823687948051851 := by
  unfold tailWord_6452206
  simp only [CollatzResearch.WordTrace]
  refine ⟨29416410757845885737408059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156887524041844723932842981 29416410757845885737408059)
  ·
    refine ⟨44124616136768828606112089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29416410757845885737408059 44124616136768828606112089)
    ·
      refine ⟨33093462102576621454584067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44124616136768828606112089 33093462102576621454584067)
      ·
        refine ⟨49640193153864932181876101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33093462102576621454584067 49640193153864932181876101)
        ·
          refine ⟨9307536216349674784101769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49640193153864932181876101 9307536216349674784101769)
          ·
            refine ⟨6980652162262256088076327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9307536216349674784101769 6980652162262256088076327)
            ·
              refine ⟨10470978243393384132114491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6980652162262256088076327 10470978243393384132114491)
              ·
                refine ⟨15706467365090076198171737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10470978243393384132114491 15706467365090076198171737)
                ·
                  refine ⟨11779850523817557148628803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15706467365090076198171737 11779850523817557148628803)
                  ·
                    refine ⟨17669775785726335722943205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11779850523817557148628803 17669775785726335722943205)
                    ·
                      refine ⟨3313082959823687948051851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17669775785726335722943205 3313082959823687948051851)
                      ·
                        rfl

theorem cell23_6452206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_6452206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452206 prefixEnd_6452206 := by exact prefixLift 6452206
  have htrace : WordTrace (prefixWord ++ tailWord_6452206) baseStart_6452206 baseEnd_6452206 := by
    simpa [prefixWord, tailWord_6452206, baseEnd_6452206] using wordTrace_append hprefix tailTrace_6452206
  have hstable : (prefixWord ++ tailWord_6452206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452206).length < 2 ^ (prefixWord ++ tailWord_6452206).sum := by decide
  have hdescent : baseEnd_6452206 < baseStart_6452206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452209 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 2, 2, 3]
def baseStart_6452209 : Nat := 118140960795 + 6452209 * 2 ^ 59
def prefixEnd_6452209 : Nat := 4983230072969 + 3 ^ 40 * 6452209 * 2
def baseEnd_6452209 : Nat := 3313084500265651436314337

theorem tailTrace_6452209 : CollatzResearch.WordTrace tailWord_6452209 prefixEnd_6452209 3313084500265651436314337 := by
  unfold tailWord_6452209
  simp only [CollatzResearch.WordTrace]
  refine ⟨235331395481756217411623681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156887596987837478274415787 235331395481756217411623681)
  ·
    refine ⟨176498546611317163058717761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235331395481756217411623681 176498546611317163058717761)
    ·
      refine ⟨132373909958487872294038321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176498546611317163058717761 132373909958487872294038321)
      ·
        refine ⟨99280432468865904220528741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132373909958487872294038321 99280432468865904220528741)
        ·
          refine ⟨18615081087912357041349139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99280432468865904220528741 18615081087912357041349139)
          ·
            refine ⟨27922621631868535562023709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18615081087912357041349139 27922621631868535562023709)
            ·
              refine ⟨10470983111950700835758891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27922621631868535562023709 10470983111950700835758891)
              ·
                refine ⟨15706474667926051253638337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10470983111950700835758891 15706474667926051253638337)
                ·
                  refine ⟨11779856000944538440228753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15706474667926051253638337 11779856000944538440228753)
                  ·
                    refine ⟨8834892000708403830171565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11779856000944538440228753 8834892000708403830171565)
                    ·
                      refine ⟨3313084500265651436314337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8834892000708403830171565 3313084500265651436314337)
                      ·
                        rfl

theorem cell23_6452209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_6452209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452209 prefixEnd_6452209 := by exact prefixLift 6452209
  have htrace : WordTrace (prefixWord ++ tailWord_6452209) baseStart_6452209 baseEnd_6452209 := by
    simpa [prefixWord, tailWord_6452209, baseEnd_6452209] using wordTrace_append hprefix tailTrace_6452209
  have hstable : (prefixWord ++ tailWord_6452209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452209).length < 2 ^ (prefixWord ++ tailWord_6452209).sum := by decide
  have hdescent : baseEnd_6452209 < baseStart_6452209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452259 : List Nat := [1, 1, 1, 4, 3, 3, 2, 2, 1, 5]
def baseStart_6452259 : Nat := 118140960795 + 6452259 * 2 ^ 59
def prefixEnd_6452259 : Nat := 4983230072969 + 3 ^ 40 * 6452259 * 2
def baseEnd_6452259 : Nat := 1104370058099458746896369

theorem tailTrace_6452259 : CollatzResearch.WordTrace tailWord_6452259 prefixEnd_6452259 1104370058099458746896369 := by
  unfold tailWord_6452259
  simp only [CollatzResearch.WordTrace]
  refine ⟨235333219131575075950943831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156888812754383383967295887 235333219131575075950943831)
  ·
    refine ⟨352999828697362613926415747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235333219131575075950943831 352999828697362613926415747)
    ·
      refine ⟨529499743046043920889623621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352999828697362613926415747 529499743046043920889623621)
      ·
        refine ⟨99281201821133235166804429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 529499743046043920889623621 99281201821133235166804429)
        ·
          refine ⟨37230450682924963187551661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99281201821133235166804429 37230450682924963187551661)
          ·
            refine ⟨13961419006096861195331873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37230450682924963187551661 13961419006096861195331873)
            ·
              refine ⟨10471064254572645896498905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13961419006096861195331873 10471064254572645896498905)
              ·
                refine ⟨7853298190929484422374179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10471064254572645896498905 7853298190929484422374179)
                ·
                  refine ⟨11779947286394226633561269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7853298190929484422374179 11779947286394226633561269)
                  ·
                    refine ⟨1104370058099458746896369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11779947286394226633561269 1104370058099458746896369)
                    ·
                      rfl

theorem cell23_6452259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 5].length) (baseStart_6452259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452259 prefixEnd_6452259 := by exact prefixLift 6452259
  have htrace : WordTrace (prefixWord ++ tailWord_6452259) baseStart_6452259 baseEnd_6452259 := by
    simpa [prefixWord, tailWord_6452259, baseEnd_6452259] using wordTrace_append hprefix tailTrace_6452259
  have hstable : (prefixWord ++ tailWord_6452259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452259).length < 2 ^ (prefixWord ++ tailWord_6452259).sum := by decide
  have hdescent : baseEnd_6452259 < baseStart_6452259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452272 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 6, 4]
def baseStart_6452272 : Nat := 118140960795 + 6452272 * 2 ^ 59
def prefixEnd_6452272 : Nat := 4983230072969 + 3 ^ 40 * 6452272 * 2
def baseEnd_6452272 : Nat := 1104372283182294896608849

theorem tailTrace_6452272 : CollatzResearch.WordTrace tailWord_6452272 prefixEnd_6452272 1104372283182294896608849 := by
  unfold tailWord_6452272
  simp only [CollatzResearch.WordTrace]
  refine ⟨117666846640263989585583535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156889128853685319447444713 117666846640263989585583535)
  ·
    refine ⟨176500269960395984378375303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117666846640263989585583535 176500269960395984378375303)
    ·
      refine ⟨264750404940593976567562955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176500269960395984378375303 264750404940593976567562955)
      ·
        refine ⟨397125607410890964851344433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264750404940593976567562955 397125607410890964851344433)
        ·
          refine ⟨297844205558168223638508325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397125607410890964851344433 297844205558168223638508325)
          ·
            refine ⟨55845788542156541932220311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 297844205558168223638508325 55845788542156541932220311)
            ·
              refine ⟨83768682813234812898330467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55845788542156541932220311 83768682813234812898330467)
              ·
                refine ⟨125653024219852219347495701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83768682813234812898330467 125653024219852219347495701)
                ·
                  refine ⟨5889985510305572781913861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125653024219852219347495701 5889985510305572781913861)
                  ·
                    refine ⟨1104372283182294896608849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5889985510305572781913861 1104372283182294896608849)
                    ·
                      rfl

theorem cell23_6452272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 6, 4].length) (baseStart_6452272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452272 prefixEnd_6452272 := by exact prefixLift 6452272
  have htrace : WordTrace (prefixWord ++ tailWord_6452272) baseStart_6452272 baseEnd_6452272 := by
    simpa [prefixWord, tailWord_6452272, baseEnd_6452272] using wordTrace_append hprefix tailTrace_6452272
  have hstable : (prefixWord ++ tailWord_6452272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452272).length < 2 ^ (prefixWord ++ tailWord_6452272).sum := by decide
  have hdescent : baseEnd_6452272 < baseStart_6452272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452276 : List Nat := [2, 5, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_6452276 : Nat := 118140960795 + 6452276 * 2 ^ 59
def prefixEnd_6452276 : Nat := 4983230072969 + 3 ^ 40 * 6452276 * 2
def baseEnd_6452276 : Nat := 1104372967823167558058843

theorem tailTrace_6452276 : CollatzResearch.WordTrace tailWord_6452276 prefixEnd_6452276 1104372967823167558058843 := by
  unfold tailWord_6452276
  simp only [CollatzResearch.WordTrace]
  refine ⟨117666919586256743927156341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156889226115008991902875121 117666919586256743927156341)
  ·
    refine ⟨11031273711211569743170907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117666919586256743927156341 11031273711211569743170907)
    ·
      refine ⟨16546910566817354614756361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11031273711211569743170907 16546910566817354614756361)
      ·
        refine ⟨12410182925113015961067271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16546910566817354614756361 12410182925113015961067271)
        ·
          refine ⟨18615274387669523941600907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12410182925113015961067271 18615274387669523941600907)
          ·
            refine ⟨27922911581504285912401361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18615274387669523941600907 27922911581504285912401361)
            ·
              refine ⟨20942183686128214434301021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27922911581504285912401361 20942183686128214434301021)
              ·
                refine ⟨7853318882298080412862883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20942183686128214434301021 7853318882298080412862883)
                ·
                  refine ⟨11779978323447120619294325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7853318882298080412862883 11779978323447120619294325)
                  ·
                    refine ⟨1104372967823167558058843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11779978323447120619294325 1104372967823167558058843)
                    ·
                      rfl

theorem cell23_6452276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_6452276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452276 prefixEnd_6452276 := by exact prefixLift 6452276
  have htrace : WordTrace (prefixWord ++ tailWord_6452276) baseStart_6452276 baseEnd_6452276 := by
    simpa [prefixWord, tailWord_6452276, baseEnd_6452276] using wordTrace_append hprefix tailTrace_6452276
  have hstable : (prefixWord ++ tailWord_6452276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452276).length < 2 ^ (prefixWord ++ tailWord_6452276).sum := by decide
  have hdescent : baseEnd_6452276 < baseStart_6452276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452282 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5]
def baseStart_6452282 : Nat := 118140960795 + 6452282 * 2 ^ 59
def prefixEnd_6452282 : Nat := 4983230072969 + 3 ^ 40 * 6452282 * 2
def baseEnd_6452282 : Nat := 3313121984353429650701501

theorem tailTrace_6452282 : CollatzResearch.WordTrace tailWord_6452282 prefixEnd_6452282 3313121984353429650701501 := by
  unfold tailWord_6452282
  simp only [CollatzResearch.WordTrace]
  refine ⟨58833514502622937719757775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156889372006994500586020733 58833514502622937719757775)
  ·
    refine ⟨88250271753934406579636663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58833514502622937719757775 88250271753934406579636663)
    ·
      refine ⟨132375407630901609869454995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88250271753934406579636663 132375407630901609869454995)
      ·
        refine ⟨198563111446352414804182493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132375407630901609869454995 198563111446352414804182493)
        ·
          refine ⟨74461166792382155551568435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198563111446352414804182493 74461166792382155551568435)
          ·
            refine ⟨111691750188573233327352653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74461166792382155551568435 111691750188573233327352653)
            ·
              refine ⟨41884406320714962497757245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111691750188573233327352653 41884406320714962497757245)
              ·
                refine ⟨15706652370268110936658967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41884406320714962497757245 15706652370268110936658967)
                ·
                  refine ⟨23559978555402166404988451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15706652370268110936658967 23559978555402166404988451)
                  ·
                    refine ⟨35339967833103249607482677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23559978555402166404988451 35339967833103249607482677)
                    ·
                      refine ⟨3313121984353429650701501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35339967833103249607482677 3313121984353429650701501)
                      ·
                        rfl

theorem cell23_6452282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_6452282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452282 prefixEnd_6452282 := by exact prefixLift 6452282
  have htrace : WordTrace (prefixWord ++ tailWord_6452282) baseStart_6452282 baseEnd_6452282 := by
    simpa [prefixWord, tailWord_6452282, baseEnd_6452282] using wordTrace_append hprefix tailTrace_6452282
  have hstable : (prefixWord ++ tailWord_6452282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452282).length < 2 ^ (prefixWord ++ tailWord_6452282).sum := by decide
  have hdescent : baseEnd_6452282 < baseStart_6452282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452302 : List Nat := [4, 1, 1, 1, 1, 3, 4, 8]
def baseStart_6452302 : Nat := 118140960795 + 6452302 * 2 ^ 59
def prefixEnd_6452302 : Nat := 4983230072969 + 3 ^ 40 * 6452302 * 2
def baseEnd_6452302 : Nat := 122708601998759984164867

theorem tailTrace_6452302 : CollatzResearch.WordTrace tailWord_6452302 prefixEnd_6452302 122708601998759984164867 := by
  unfold tailWord_6452302
  simp only [CollatzResearch.WordTrace]
  refine ⟨29416848433802411786844895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156889858313612862863172773 29416848433802411786844895)
  ·
    refine ⟨44125272650703617680267343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29416848433802411786844895 44125272650703617680267343)
    ·
      refine ⟨66187908976055426520401015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44125272650703617680267343 66187908976055426520401015)
      ·
        refine ⟨99281863464083139780601523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66187908976055426520401015 99281863464083139780601523)
        ·
          refine ⟨148922795196124709670902285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99281863464083139780601523 148922795196124709670902285)
          ·
            refine ⟨55846048198546766126588357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148922795196124709670902285 55846048198546766126588357)
            ·
              refine ⟨10471134037227518648735317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55846048198546766126588357 10471134037227518648735317)
              ·
                refine ⟨122708601998759984164867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10471134037227518648735317 122708601998759984164867)
                ·
                  rfl

theorem cell23_6452302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_6452302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452302 prefixEnd_6452302 := by exact prefixLift 6452302
  have htrace : WordTrace (prefixWord ++ tailWord_6452302) baseStart_6452302 baseEnd_6452302 := by
    simpa [prefixWord, tailWord_6452302, baseEnd_6452302] using wordTrace_append hprefix tailTrace_6452302
  have hstable : (prefixWord ++ tailWord_6452302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452302).length < 2 ^ (prefixWord ++ tailWord_6452302).sum := by decide
  have hdescent : baseEnd_6452302 < baseStart_6452302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452306 : List Nat := [3, 2, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_6452306 : Nat := 118140960795 + 6452306 * 2 ^ 59
def prefixEnd_6452306 : Nat := 4983230072969 + 3 ^ 40 * 6452306 * 2
def baseEnd_6452306 : Nat := 1104378102629712518933797

theorem tailTrace_6452306 : CollatzResearch.WordTrace tailWord_6452306 prefixEnd_6452306 1104378102629712518933797 := by
  unfold tailWord_6452306
  simp only [CollatzResearch.WordTrace]
  refine ⟨58833733340601200744476193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156889955574936535318603181 58833733340601200744476193)
  ·
    refine ⟨44125300005450900558357145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58833733340601200744476193 44125300005450900558357145)
    ·
      refine ⟨33093975004088175418767859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44125300005450900558357145 33093975004088175418767859)
      ·
        refine ⟨49640962506132263128151789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33093975004088175418767859 49640962506132263128151789)
        ·
          refine ⟨18615360939799598673056921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49640962506132263128151789 18615360939799598673056921)
          ·
            refine ⟨13961520704849699004792691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18615360939799598673056921 13961520704849699004792691)
            ·
              refine ⟨20942281057274548507189037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13961520704849699004792691 20942281057274548507189037)
              ·
                refine ⟨7853355396477955690195889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20942281057274548507189037 7853355396477955690195889)
                ·
                  refine ⟨5890016547358466767646917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7853355396477955690195889 5890016547358466767646917)
                  ·
                    refine ⟨1104378102629712518933797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5890016547358466767646917 1104378102629712518933797)
                    ·
                      rfl

theorem cell23_6452306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_6452306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452306 prefixEnd_6452306 := by exact prefixLift 6452306
  have htrace : WordTrace (prefixWord ++ tailWord_6452306) baseStart_6452306 baseEnd_6452306 := by
    simpa [prefixWord, tailWord_6452306, baseEnd_6452306] using wordTrace_append hprefix tailTrace_6452306
  have hstable : (prefixWord ++ tailWord_6452306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452306).length < 2 ^ (prefixWord ++ tailWord_6452306).sum := by decide
  have hdescent : baseEnd_6452306 < baseStart_6452306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452310 : List Nat := [5, 2, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_6452310 : Nat := 118140960795 + 6452310 * 2 ^ 59
def prefixEnd_6452310 : Nat := 4983230072969 + 3 ^ 40 * 6452310 * 2
def baseEnd_6452310 : Nat := 1104378787270585180383791

theorem tailTrace_6452310 : CollatzResearch.WordTrace tailWord_6452310 prefixEnd_6452310 1104378787270585180383791 := by
  unfold tailWord_6452310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14708442453399394478815649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156890052836260207774033589 14708442453399394478815649)
  ·
    refine ⟨11031331840049545859111737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14708442453399394478815649 11031331840049545859111737)
    ·
      refine ⟨8273498880037159394333803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11031331840049545859111737 8273498880037159394333803)
      ·
        refine ⟨12410248320055739091500705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8273498880037159394333803 12410248320055739091500705)
        ·
          refine ⟨9307686240041804318625529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12410248320055739091500705 9307686240041804318625529)
          ·
            refine ⟨6980764680031353238969147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9307686240041804318625529 6980764680031353238969147)
            ·
              refine ⟨10471147020047029858453721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6980764680031353238969147 10471147020047029858453721)
              ·
                refine ⟨7853360265035272393840291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10471147020047029858453721 7853360265035272393840291)
                ·
                  refine ⟨11780040397552908590760437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7853360265035272393840291 11780040397552908590760437)
                  ·
                    refine ⟨1104378787270585180383791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11780040397552908590760437 1104378787270585180383791)
                    ·
                      rfl

theorem cell23_6452310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_6452310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452310 prefixEnd_6452310 := by exact prefixLift 6452310
  have htrace : WordTrace (prefixWord ++ tailWord_6452310) baseStart_6452310 baseEnd_6452310 := by
    simpa [prefixWord, tailWord_6452310, baseEnd_6452310] using wordTrace_append hprefix tailTrace_6452310
  have hstable : (prefixWord ++ tailWord_6452310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452310).length < 2 ^ (prefixWord ++ tailWord_6452310).sum := by decide
  have hdescent : baseEnd_6452310 < baseStart_6452310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452329 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 1, 3, 3]
def baseStart_6452329 : Nat := 118140960795 + 6452329 * 2 ^ 59
def prefixEnd_6452329 : Nat := 4983230072969 + 3 ^ 40 * 6452329 * 2
def baseEnd_6452329 : Nat := 3313146117944190966813785

theorem tailTrace_6452329 : CollatzResearch.WordTrace tailWord_6452329 prefixEnd_6452329 3313146117944190966813785 := by
  unfold tailWord_6452329
  simp only [CollatzResearch.WordTrace]
  refine ⟨235335772241321477905992041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156890514827547651937328027 235335772241321477905992041)
  ·
    refine ⟨176501829180991108429494031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235335772241321477905992041 176501829180991108429494031)
    ·
      refine ⟨264752743771486662644241047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176501829180991108429494031 264752743771486662644241047)
      ·
        refine ⟨397129115657229993966361571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264752743771486662644241047 397129115657229993966361571)
        ·
          refine ⟨595693673485844990949542357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397129115657229993966361571 595693673485844990949542357)
          ·
            refine ⟨13961570472324491975379899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 595693673485844990949542357 13961570472324491975379899)
            ·
              refine ⟨20942355708486737963069849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13961570472324491975379899 20942355708486737963069849)
              ·
                refine ⟨15706766781365053472302387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20942355708486737963069849 15706766781365053472302387)
                ·
                  refine ⟨23560150172047580208453581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15706766781365053472302387 23560150172047580208453581)
                  ·
                    refine ⟨8835056314517842578170093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23560150172047580208453581 8835056314517842578170093)
                    ·
                      refine ⟨3313146117944190966813785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8835056314517842578170093 3313146117944190966813785)
                      ·
                        rfl

theorem cell23_6452329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 3, 3].length) (baseStart_6452329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452329 prefixEnd_6452329 := by exact prefixLift 6452329
  have htrace : WordTrace (prefixWord ++ tailWord_6452329) baseStart_6452329 baseEnd_6452329 := by
    simpa [prefixWord, tailWord_6452329, baseEnd_6452329] using wordTrace_append hprefix tailTrace_6452329
  have hstable : (prefixWord ++ tailWord_6452329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452329).length < 2 ^ (prefixWord ++ tailWord_6452329).sum := by decide
  have hdescent : baseEnd_6452329 < baseStart_6452329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452333 : List Nat := [1, 5, 1, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_6452333 : Nat := 118140960795 + 6452333 * 2 ^ 59
def prefixEnd_6452333 : Nat := 4983230072969 + 3 ^ 40 * 6452333 * 2
def baseEnd_6452333 : Nat := 3313148171866808951163767

theorem tailTrace_6452333 : CollatzResearch.WordTrace tailWord_6452333 prefixEnd_6452333 3313148171866808951163767 := by
  unfold tailWord_6452333
  simp only [CollatzResearch.WordTrace]
  refine ⟨235335918133306986589137653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156890612088871324392758435 235335918133306986589137653)
  ·
    refine ⟨22062742324997529992731655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235335918133306986589137653 22062742324997529992731655)
    ·
      refine ⟨33094113487496294989097483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22062742324997529992731655 33094113487496294989097483)
      ·
        refine ⟨49641170231244442483646225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33094113487496294989097483 49641170231244442483646225)
        ·
          refine ⟨37230877673433331862734669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49641170231244442483646225 37230877673433331862734669)
          ·
            refine ⟨13961579127537499448525501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37230877673433331862734669 13961579127537499448525501)
            ·
              refine ⟨5235592172826562293197063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13961579127537499448525501 5235592172826562293197063)
              ·
                refine ⟨7853388259239843439795595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5235592172826562293197063 7853388259239843439795595)
                ·
                  refine ⟨11780082388859765159693393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7853388259239843439795595 11780082388859765159693393)
                  ·
                    refine ⟨8835061791644823869770045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11780082388859765159693393 8835061791644823869770045)
                    ·
                      refine ⟨3313148171866808951163767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8835061791644823869770045 3313148171866808951163767)
                      ·
                        rfl

theorem cell23_6452333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_6452333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452333 prefixEnd_6452333 := by exact prefixLift 6452333
  have htrace : WordTrace (prefixWord ++ tailWord_6452333) baseStart_6452333 baseEnd_6452333 := by
    simpa [prefixWord, tailWord_6452333, baseEnd_6452333] using wordTrace_append hprefix tailTrace_6452333
  have hstable : (prefixWord ++ tailWord_6452333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452333).length < 2 ^ (prefixWord ++ tailWord_6452333).sum := by decide
  have hdescent : baseEnd_6452333 < baseStart_6452333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452352 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 4]
def baseStart_6452352 : Nat := 118140960795 + 6452352 * 2 ^ 59
def prefixEnd_6452352 : Nat := 4983230072969 + 3 ^ 40 * 6452352 * 2
def baseEnd_6452352 : Nat := 3313157927999244376826179

theorem tailTrace_6452352 : CollatzResearch.WordTrace tailWord_6452352 prefixEnd_6452352 3313157927999244376826179 := by
  unfold tailWord_6452352
  simp only [CollatzResearch.WordTrace]
  refine ⟨117668305560119076417039655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156891074080158768556052873 117668305560119076417039655)
  ·
    refine ⟨176502458340178614625559483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117668305560119076417039655 176502458340178614625559483)
    ·
      refine ⟨264753687510267921938339225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176502458340178614625559483 264753687510267921938339225)
      ·
        refine ⟨198565265632700941453754419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264753687510267921938339225 198565265632700941453754419)
        ·
          refine ⟨297847898449051412180631629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198565265632700941453754419 297847898449051412180631629)
          ·
            refine ⟨111692961918394279567736861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297847898449051412180631629 111692961918394279567736861)
            ·
              refine ⟨41884860719397854837901323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111692961918394279567736861 41884860719397854837901323)
              ·
                refine ⟨62827291079096782256851985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41884860719397854837901323 62827291079096782256851985)
                ·
                  refine ⟨47120468309322586692638989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62827291079096782256851985 47120468309322586692638989)
                  ·
                    refine ⟨17670175615995970009739621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47120468309322586692638989 17670175615995970009739621)
                    ·
                      refine ⟨3313157927999244376826179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17670175615995970009739621 3313157927999244376826179)
                      ·
                        rfl

theorem cell23_6452352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_6452352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452352 prefixEnd_6452352 := by exact prefixLift 6452352
  have htrace : WordTrace (prefixWord ++ tailWord_6452352) baseStart_6452352 baseEnd_6452352 := by
    simpa [prefixWord, tailWord_6452352, baseEnd_6452352] using wordTrace_append hprefix tailTrace_6452352
  have hstable : (prefixWord ++ tailWord_6452352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452352).length < 2 ^ (prefixWord ++ tailWord_6452352).sum := by decide
  have hdescent : baseEnd_6452352 < baseStart_6452352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452356 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_6452356 : Nat := 118140960795 + 6452356 * 2 ^ 59
def prefixEnd_6452356 : Nat := 4983230072969 + 3 ^ 40 * 6452356 * 2
def baseEnd_6452356 : Nat := 3313159981921862361176161

theorem tailTrace_6452356 : CollatzResearch.WordTrace tailWord_6452356 prefixEnd_6452356 3313159981921862361176161 := by
  unfold tailWord_6452356
  simp only [CollatzResearch.WordTrace]
  refine ⟨117668378506111830758612461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156891171341482441011483281 117668378506111830758612461)
  ·
    refine ⟨44125641939791936534479673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117668378506111830758612461 44125641939791936534479673)
    ·
      refine ⟨33094231454843952400859755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44125641939791936534479673 33094231454843952400859755)
      ·
        refine ⟨49641347182265928601289633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33094231454843952400859755 49641347182265928601289633)
        ·
          refine ⟨37231010386699446450967225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49641347182265928601289633 37231010386699446450967225)
          ·
            refine ⟨27923257790024584838225419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37231010386699446450967225 27923257790024584838225419)
            ·
              refine ⟨41884886685036877257338129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27923257790024584838225419 41884886685036877257338129)
              ·
                refine ⟨31413665013777657943003597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41884886685036877257338129 31413665013777657943003597)
                ·
                  refine ⟨11780124380166621728626349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31413665013777657943003597 11780124380166621728626349)
                  ·
                    refine ⟨4417546642562483148234881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11780124380166621728626349 4417546642562483148234881)
                    ·
                      refine ⟨3313159981921862361176161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417546642562483148234881 3313159981921862361176161)
                      ·
                        rfl

theorem cell23_6452356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_6452356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452356 prefixEnd_6452356 := by exact prefixLift 6452356
  have htrace : WordTrace (prefixWord ++ tailWord_6452356) baseStart_6452356 baseEnd_6452356 := by
    simpa [prefixWord, tailWord_6452356, baseEnd_6452356] using wordTrace_append hprefix tailTrace_6452356
  have hstable : (prefixWord ++ tailWord_6452356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452356).length < 2 ^ (prefixWord ++ tailWord_6452356).sum := by decide
  have hdescent : baseEnd_6452356 < baseStart_6452356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452397 : List Nat := [1, 5, 2, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_6452397 : Nat := 118140960795 + 6452397 * 2 ^ 59
def prefixEnd_6452397 : Nat := 4983230072969 + 3 ^ 40 * 6452397 * 2
def baseEnd_6452397 : Nat := 3313181034628696700763473

theorem tailTrace_6452397 : CollatzResearch.WordTrace tailWord_6452397 prefixEnd_6452397 3313181034628696700763473 := by
  unfold tailWord_6452397
  simp only [CollatzResearch.WordTrace]
  refine ⟨235338252405075125519467445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156892168270050083679644963 235338252405075125519467445)
  ·
    refine ⟨22062961162975793017450073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235338252405075125519467445 22062961162975793017450073)
    ·
      refine ⟨16547220872231844763087555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22062961162975793017450073 16547220872231844763087555)
      ·
        refine ⟨24820831308347767144631333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16547220872231844763087555 24820831308347767144631333)
        ·
          refine ⟨4653905870315206339618375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24820831308347767144631333 4653905870315206339618375)
          ·
            refine ⟨6980858805472809509427563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4653905870315206339618375 6980858805472809509427563)
            ·
              refine ⟨10471288208209214264141345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6980858805472809509427563 10471288208209214264141345)
              ·
                refine ⟨7853466156156910698106009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10471288208209214264141345 7853466156156910698106009)
                ·
                  refine ⟨5890099617117683023579507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7853466156156910698106009 5890099617117683023579507)
                  ·
                    refine ⟨8835149425676524535369261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5890099617117683023579507 8835149425676524535369261)
                    ·
                      refine ⟨3313181034628696700763473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8835149425676524535369261 3313181034628696700763473)
                      ·
                        rfl

theorem cell23_6452397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_6452397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452397 prefixEnd_6452397 := by exact prefixLift 6452397
  have htrace : WordTrace (prefixWord ++ tailWord_6452397) baseStart_6452397 baseEnd_6452397 := by
    simpa [prefixWord, tailWord_6452397, baseEnd_6452397] using wordTrace_append hprefix tailTrace_6452397
  have hstable : (prefixWord ++ tailWord_6452397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452397).length < 2 ^ (prefixWord ++ tailWord_6452397).sum := by decide
  have hdescent : baseEnd_6452397 < baseStart_6452397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452403 : List Nat := [1, 1, 1, 2, 3, 2, 5, 2, 2, 2, 2]
def baseStart_6452403 : Nat := 118140960795 + 6452403 * 2 ^ 59
def prefixEnd_6452403 : Nat := 4983230072969 + 3 ^ 40 * 6452403 * 2
def baseEnd_6452403 : Nat := 3313184115512623677288445

theorem tailTrace_6452403 : CollatzResearch.WordTrace tailWord_6452403 prefixEnd_6452403 3313184115512623677288445 := by
  unfold tailWord_6452403
  simp only [CollatzResearch.WordTrace]
  refine ⟨235338471243053388544185863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156892314162035592362790575 235338471243053388544185863)
  ·
    refine ⟨353007706864580082816278795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235338471243053388544185863 353007706864580082816278795)
    ·
      refine ⟨529511560296870124224418193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353007706864580082816278795 529511560296870124224418193)
      ·
        refine ⟨397133670222652593168313645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529511560296870124224418193 397133670222652593168313645)
        ·
          refine ⟨148925126333494722438117617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397133670222652593168313645 148925126333494722438117617)
          ·
            refine ⟨111693844750121041828588213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148925126333494722438117617 111693844750121041828588213)
            ·
              refine ⟨10471297945323847671430145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111693844750121041828588213 10471297945323847671430145)
              ·
                refine ⟨7853473458992885753572609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10471297945323847671430145 7853473458992885753572609)
                ·
                  refine ⟨5890105094244664315179457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7853473458992885753572609 5890105094244664315179457)
                  ·
                    refine ⟨4417578820683498236384593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5890105094244664315179457 4417578820683498236384593)
                    ·
                      refine ⟨3313184115512623677288445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417578820683498236384593 3313184115512623677288445)
                      ·
                        rfl

theorem cell23_6452403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 2, 2].length) (baseStart_6452403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452403 prefixEnd_6452403 := by exact prefixLift 6452403
  have htrace : WordTrace (prefixWord ++ tailWord_6452403) baseStart_6452403 baseEnd_6452403 := by
    simpa [prefixWord, tailWord_6452403, baseEnd_6452403] using wordTrace_append hprefix tailTrace_6452403
  have hstable : (prefixWord ++ tailWord_6452403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452403).length < 2 ^ (prefixWord ++ tailWord_6452403).sum := by decide
  have hdescent : baseEnd_6452403 < baseStart_6452403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452409 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 7]
def baseStart_6452409 : Nat := 118140960795 + 6452409 * 2 ^ 59
def prefixEnd_6452409 : Nat := 4983230072969 + 3 ^ 40 * 6452409 * 2
def baseEnd_6452409 : Nat := 368131910710727850423713

theorem tailTrace_6452409 : CollatzResearch.WordTrace tailWord_6452409 prefixEnd_6452409 368131910710727850423713 := by
  unfold tailWord_6452409
  simp only [CollatzResearch.WordTrace]
  refine ⟨235338690081031651568904281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156892460054021101045936187 235338690081031651568904281)
  ·
    refine ⟨176504017560773738676678211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235338690081031651568904281 176504017560773738676678211)
    ·
      refine ⟨264756026341160608015017317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176504017560773738676678211 264756026341160608015017317)
      ·
        refine ⟨49641754938967614002815747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264756026341160608015017317 49641754938967614002815747)
        ·
          refine ⟨74462632408451421004223621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49641754938967614002815747 74462632408451421004223621)
          ·
            refine ⟨13961743576584641438291929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74462632408451421004223621 13961743576584641438291929)
            ·
              refine ⟨10471307682438481078718947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13961743576584641438291929 10471307682438481078718947)
              ·
                refine ⟨15706961523657721618078421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10471307682438481078718947 15706961523657721618078421)
                ·
                  refine ⟨368131910710727850423713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15706961523657721618078421 368131910710727850423713)
                  ·
                    rfl

theorem cell23_6452409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 7].length) (baseStart_6452409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452409 prefixEnd_6452409 := by exact prefixLift 6452409
  have htrace : WordTrace (prefixWord ++ tailWord_6452409) baseStart_6452409 baseEnd_6452409 := by
    simpa [prefixWord, tailWord_6452409, baseEnd_6452409] using wordTrace_append hprefix tailTrace_6452409
  have hstable : (prefixWord ++ tailWord_6452409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452409).length < 2 ^ (prefixWord ++ tailWord_6452409).sum := by decide
  have hdescent : baseEnd_6452409 < baseStart_6452409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452420 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_6452420 : Nat := 118140960795 + 6452420 * 2 ^ 59
def prefixEnd_6452420 : Nat := 4983230072969 + 3 ^ 40 * 6452420 * 2
def baseEnd_6452420 : Nat := 3313192844683750110775867

theorem tailTrace_6452420 : CollatzResearch.WordTrace tailWord_6452420 prefixEnd_6452420 3313192844683750110775867 := by
  unfold tailWord_6452420
  simp only [CollatzResearch.WordTrace]
  refine ⟨117669545641995900223777357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156892727522661200298369809 117669545641995900223777357)
  ·
    refine ⟨44126079615748462583916509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117669545641995900223777357 44126079615748462583916509)
    ·
      refine ⟨16547279855905673468968691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44126079615748462583916509 16547279855905673468968691)
      ·
        refine ⟨24820919783858510203453037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16547279855905673468968691 24820919783858510203453037)
        ·
          refine ⟨9307844918946941326294889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24820919783858510203453037 9307844918946941326294889)
          ·
            refine ⟨6980883689210205994721167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9307844918946941326294889 6980883689210205994721167)
            ·
              refine ⟨10471325533815308992081751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6980883689210205994721167 10471325533815308992081751)
              ·
                refine ⟨15706988300722963488122627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10471325533815308992081751 15706988300722963488122627)
                ·
                  refine ⟨23560482451084445232183941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15706988300722963488122627 23560482451084445232183941)
                  ·
                    refine ⟨4417590459578333481034489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23560482451084445232183941 4417590459578333481034489)
                    ·
                      refine ⟨3313192844683750110775867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417590459578333481034489 3313192844683750110775867)
                      ·
                        rfl

theorem cell23_6452420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_6452420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452420 prefixEnd_6452420 := by exact prefixLift 6452420
  have htrace : WordTrace (prefixWord ++ tailWord_6452420) baseStart_6452420 baseEnd_6452420 := by
    simpa [prefixWord, tailWord_6452420, baseEnd_6452420] using wordTrace_append hprefix tailTrace_6452420
  have hstable : (prefixWord ++ tailWord_6452420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452420).length < 2 ^ (prefixWord ++ tailWord_6452420).sum := by decide
  have hdescent : baseEnd_6452420 < baseStart_6452420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452459 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 4]
def baseStart_6452459 : Nat := 118140960795 + 6452459 * 2 ^ 59
def prefixEnd_6452459 : Nat := 4983230072969 + 3 ^ 40 * 6452459 * 2
def baseEnd_6452459 : Nat := 3313212870429275458188187

theorem tailTrace_6452459 : CollatzResearch.WordTrace tailWord_6452459 prefixEnd_6452459 3313212870429275458188187 := by
  unfold tailWord_6452459
  simp only [CollatzResearch.WordTrace]
  refine ⟨235340513730850510108224431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156893675820567006738816287 235340513730850510108224431)
  ·
    refine ⟨353010770596275765162336647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235340513730850510108224431 353010770596275765162336647)
    ·
      refine ⟨529516155894413647743504971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353010770596275765162336647 529516155894413647743504971)
      ·
        refine ⟨794274233841620471615257457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529516155894413647743504971 794274233841620471615257457)
        ·
          refine ⟨595705675381215353711443093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 794274233841620471615257457 595705675381215353711443093)
          ·
            refine ⟨27923703533494469705223895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 595705675381215353711443093 27923703533494469705223895)
            ·
              refine ⟨41885555300241704557835843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27923703533494469705223895 41885555300241704557835843)
              ·
                refine ⟨62828332950362556836753765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41885555300241704557835843 62828332950362556836753765)
                ·
                  refine ⟨11780312428192979406891331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62828332950362556836753765 11780312428192979406891331)
                  ·
                    refine ⟨17670468642289469110336997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11780312428192979406891331 17670468642289469110336997)
                    ·
                      refine ⟨3313212870429275458188187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17670468642289469110336997 3313212870429275458188187)
                      ·
                        rfl

theorem cell23_6452459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 4].length) (baseStart_6452459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452459 prefixEnd_6452459 := by exact prefixLift 6452459
  have htrace : WordTrace (prefixWord ++ tailWord_6452459) baseStart_6452459 baseEnd_6452459 := by
    simpa [prefixWord, tailWord_6452459, baseEnd_6452459] using wordTrace_append hprefix tailTrace_6452459
  have hstable : (prefixWord ++ tailWord_6452459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452459).length < 2 ^ (prefixWord ++ tailWord_6452459).sum := by decide
  have hdescent : baseEnd_6452459 < baseStart_6452459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452466 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_6452466 : Nat := 118140960795 + 6452466 * 2 ^ 59
def prefixEnd_6452466 : Nat := 4983230072969 + 3 ^ 40 * 6452466 * 2
def baseEnd_6452466 : Nat := 3313216464793856930800655

theorem tailTrace_6452466 : CollatzResearch.WordTrace tailWord_6452466 prefixEnd_6452466 3313216464793856930800655 := by
  unfold tailWord_6452466
  simp only [CollatzResearch.WordTrace]
  refine ⟨58835192260456287575932313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156893846027883433535819501 58835192260456287575932313)
  ·
    refine ⟨44126394195342215681949235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58835192260456287575932313 44126394195342215681949235)
    ·
      refine ⟨66189591293013323522923853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44126394195342215681949235 66189591293013323522923853)
      ·
        refine ⟨24821096734879996321096445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66189591293013323522923853 24821096734879996321096445)
        ·
          refine ⟨9307911275579998620411167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24821096734879996321096445 9307911275579998620411167)
          ·
            refine ⟨13961866913369997930616751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9307911275579998620411167 13961866913369997930616751)
            ·
              refine ⟨20942800370054996895925127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13961866913369997930616751 20942800370054996895925127)
              ·
                refine ⟨31414200555082495343887691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20942800370054996895925127 31414200555082495343887691)
                ·
                  refine ⟨47121300832623743015831537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31414200555082495343887691 47121300832623743015831537)
                  ·
                    refine ⟨35340975624467807261873653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47121300832623743015831537 35340975624467807261873653)
                    ·
                      refine ⟨3313216464793856930800655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35340975624467807261873653 3313216464793856930800655)
                      ·
                        rfl

theorem cell23_6452466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_6452466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452466 prefixEnd_6452466 := by exact prefixLift 6452466
  have htrace : WordTrace (prefixWord ++ tailWord_6452466) baseStart_6452466 baseEnd_6452466 := by
    simpa [prefixWord, tailWord_6452466, baseEnd_6452466] using wordTrace_append hprefix tailTrace_6452466
  have hstable : (prefixWord ++ tailWord_6452466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452466).length < 2 ^ (prefixWord ++ tailWord_6452466).sum := by decide
  have hdescent : baseEnd_6452466 < baseStart_6452466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452503 : List Nat := [1, 1, 3, 4, 1, 1, 2, 5, 1, 4]
def baseStart_6452503 : Nat := 118140960795 + 6452503 * 2 ^ 59
def prefixEnd_6452503 : Nat := 4983230072969 + 3 ^ 40 * 6452503 * 2
def baseEnd_6452503 : Nat := 1104411821192691095345995

theorem tailTrace_6452503 : CollatzResearch.WordTrace tailWord_6452503 prefixEnd_6452503 1104411821192691095345995 := by
  unfold tailWord_6452503
  simp only [CollatzResearch.WordTrace]
  refine ⟨235342118542691105622826163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156894745695127403748550775 235342118542691105622826163)
  ·
    refine ⟨353013177814036658434239245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235342118542691105622826163 353013177814036658434239245)
    ·
      refine ⟨132379941680263746912839717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353013177814036658434239245 132379941680263746912839717)
      ·
        refine ⟨24821239065049452546157447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132379941680263746912839717 24821239065049452546157447)
        ·
          refine ⟨37231858597574178819236171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24821239065049452546157447 37231858597574178819236171)
          ·
            refine ⟨55847787896361268228854257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37231858597574178819236171 55847787896361268228854257)
            ·
              refine ⟨41885840922270951171640693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55847787896361268228854257 41885840922270951171640693)
              ·
                refine ⟨3926797586462901672341315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41885840922270951171640693 3926797586462901672341315)
                ·
                  refine ⟨5890196379694352508511973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926797586462901672341315 5890196379694352508511973)
                  ·
                    refine ⟨1104411821192691095345995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5890196379694352508511973 1104411821192691095345995)
                    ·
                      rfl

theorem cell23_6452503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_6452503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452503 prefixEnd_6452503 := by exact prefixLift 6452503
  have htrace : WordTrace (prefixWord ++ tailWord_6452503) baseStart_6452503 baseEnd_6452503 := by
    simpa [prefixWord, tailWord_6452503, baseEnd_6452503] using wordTrace_append hprefix tailTrace_6452503
  have hstable : (prefixWord ++ tailWord_6452503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452503).length < 2 ^ (prefixWord ++ tailWord_6452503).sum := by decide
  have hdescent : baseEnd_6452503 < baseStart_6452503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452516 : List Nat := [2, 3, 1, 3, 1, 1, 4, 2, 6]
def baseStart_6452516 : Nat := 118140960795 + 6452516 * 2 ^ 59
def prefixEnd_6452516 : Nat := 4983230072969 + 3 ^ 40 * 6452516 * 2
def baseEnd_6452516 : Nat := 368138015425175748352825

theorem tailTrace_6452516 : CollatzResearch.WordTrace tailWord_6452516 prefixEnd_6452516 368138015425175748352825 := by
  unfold tailWord_6452516
  simp only [CollatzResearch.WordTrace]
  refine ⟨117671296345822004421524701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156895061794429339228699601 117671296345822004421524701)
  ·
    refine ⟨44126736129683251658071763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117671296345822004421524701 44126736129683251658071763)
    ·
      refine ⟨66190104194524877487107645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44126736129683251658071763 66190104194524877487107645)
      ·
        refine ⟨24821289072946829057665367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66190104194524877487107645 24821289072946829057665367)
        ·
          refine ⟨37231933609420243586498051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24821289072946829057665367 37231933609420243586498051)
          ·
            refine ⟨55847900414130365379747077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37231933609420243586498051 55847900414130365379747077)
            ·
              refine ⟨10471481327649443508702577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55847900414130365379747077 10471481327649443508702577)
              ·
                refine ⟨7853610995737082631526933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10471481327649443508702577 7853610995737082631526933)
                ·
                  refine ⟨368138015425175748352825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7853610995737082631526933 368138015425175748352825)
                  ·
                    rfl

theorem cell23_6452516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_6452516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452516 prefixEnd_6452516 := by exact prefixLift 6452516
  have htrace : WordTrace (prefixWord ++ tailWord_6452516) baseStart_6452516 baseEnd_6452516 := by
    simpa [prefixWord, tailWord_6452516, baseEnd_6452516] using wordTrace_append hprefix tailTrace_6452516
  have hstable : (prefixWord ++ tailWord_6452516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452516).length < 2 ^ (prefixWord ++ tailWord_6452516).sum := by decide
  have hdescent : baseEnd_6452516 < baseStart_6452516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452520 : List Nat := [2, 1, 5, 1, 2, 2, 1, 4, 1, 4]
def baseStart_6452520 : Nat := 118140960795 + 6452520 * 2 ^ 59
def prefixEnd_6452520 : Nat := 4983230072969 + 3 ^ 40 * 6452520 * 2
def baseEnd_6452520 : Nat := 1104414730916399906508469

theorem tailTrace_6452520 : CollatzResearch.WordTrace tailWord_6452520 prefixEnd_6452520 1104414730916399906508469 := by
  unfold tailWord_6452520
  simp only [CollatzResearch.WordTrace]
  refine ⟨117671369291814758763097507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156895159055753011684130009 117671369291814758763097507)
  ·
    refine ⟨176507053937722138144646261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117671369291814758763097507 176507053937722138144646261)
    ·
      refine ⟨16547536306661450451060587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176507053937722138144646261 16547536306661450451060587)
      ·
        refine ⟨24821304459992175676590881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16547536306661450451060587 24821304459992175676590881)
        ·
          refine ⟨18615978344994131757443161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24821304459992175676590881 18615978344994131757443161)
          ·
            refine ⟨13961983758745598818082371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18615978344994131757443161 13961983758745598818082371)
            ·
              refine ⟨20942975638118398227123557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13961983758745598818082371 20942975638118398227123557)
              ·
                refine ⟨3926807932147199667585667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20942975638118398227123557 3926807932147199667585667)
                ·
                  refine ⟨5890211898220799501378501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926807932147199667585667 5890211898220799501378501)
                  ·
                    refine ⟨1104414730916399906508469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5890211898220799501378501 1104414730916399906508469)
                    ·
                      rfl

theorem cell23_6452520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_6452520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452520 prefixEnd_6452520 := by exact prefixLift 6452520
  have htrace : WordTrace (prefixWord ++ tailWord_6452520) baseStart_6452520 baseEnd_6452520 := by
    simpa [prefixWord, tailWord_6452520, baseEnd_6452520] using wordTrace_append hprefix tailTrace_6452520
  have hstable : (prefixWord ++ tailWord_6452520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452520).length < 2 ^ (prefixWord ++ tailWord_6452520).sum := by decide
  have hdescent : baseEnd_6452520 < baseStart_6452520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452536 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 1, 5, 2]
def baseStart_6452536 : Nat := 118140960795 + 6452536 * 2 ^ 59
def prefixEnd_6452536 : Nat := 4983230072969 + 3 ^ 40 * 6452536 * 2
def baseEnd_6452536 : Nat := 3313252408439671656925333

theorem tailTrace_6452536 : CollatzResearch.WordTrace tailWord_6452536 prefixEnd_6452536 3313252408439671656925333 := by
  unfold tailWord_6452536
  simp only [CollatzResearch.WordTrace]
  refine ⟨117671661075785776129388731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156895548101047701505851641 117671661075785776129388731)
  ·
    refine ⟨176507491613678664194083097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117671661075785776129388731 176507491613678664194083097)
    ·
      refine ⟨132380618710258998145562323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176507491613678664194083097 132380618710258998145562323)
      ·
        refine ⟨198570928065388497218343485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132380618710258998145562323 198570928065388497218343485)
        ·
          refine ⟨74464098024520686456878807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198570928065388497218343485 74464098024520686456878807)
          ·
            refine ⟨111696147036781029685318211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74464098024520686456878807 111696147036781029685318211)
            ·
              refine ⟨167544220555171544527977317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111696147036781029685318211 167544220555171544527977317)
              ·
                refine ⟨31414541354094664598995747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167544220555171544527977317 31414541354094664598995747)
                ·
                  refine ⟨47121812031141996898493621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31414541354094664598995747 47121812031141996898493621)
                  ·
                    refine ⟨4417669877919562209233777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47121812031141996898493621 4417669877919562209233777)
                    ·
                      refine ⟨3313252408439671656925333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417669877919562209233777 3313252408439671656925333)
                      ·
                        rfl

theorem cell23_6452536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 5, 2].length) (baseStart_6452536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452536 prefixEnd_6452536 := by exact prefixLift 6452536
  have htrace : WordTrace (prefixWord ++ tailWord_6452536) baseStart_6452536 baseEnd_6452536 := by
    simpa [prefixWord, tailWord_6452536, baseEnd_6452536] using wordTrace_append hprefix tailTrace_6452536
  have hstable : (prefixWord ++ tailWord_6452536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452536).length < 2 ^ (prefixWord ++ tailWord_6452536).sum := by decide
  have hdescent : baseEnd_6452536 < baseStart_6452536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452543 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 3, 1, 3]
def baseStart_6452543 : Nat := 118140960795 + 6452543 * 2 ^ 59
def prefixEnd_6452543 : Nat := 4983230072969 + 3 ^ 40 * 6452543 * 2
def baseEnd_6452543 : Nat := 3313256002804253129537801

theorem tailTrace_6452543 : CollatzResearch.WordTrace tailWord_6452543 prefixEnd_6452543 3313256002804253129537801 := by
  unfold tailWord_6452543
  simp only [CollatzResearch.WordTrace]
  refine ⟨235343577462546192454282283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156895718308364128302854855 235343577462546192454282283)
  ·
    refine ⟨353015366193819288681423425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235343577462546192454282283 353015366193819288681423425)
    ·
      refine ⟨264761524645364466511067569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353015366193819288681423425 264761524645364466511067569)
      ·
        refine ⟨198571143484023349883300677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264761524645364466511067569 198571143484023349883300677)
        ·
          refine ⟨37232089403254378103118877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198571143484023349883300677 37232089403254378103118877)
          ·
            refine ⟨13962033526220391788669579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37232089403254378103118877 13962033526220391788669579)
            ·
              refine ⟨20943050289330587683004369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13962033526220391788669579 20943050289330587683004369)
              ·
                refine ⟨15707287716997940762253277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20943050289330587683004369 15707287716997940762253277)
                ·
                  refine ⟨5890232893874227785844979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15707287716997940762253277 5890232893874227785844979)
                  ·
                    refine ⟨8835349340811341678767469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5890232893874227785844979 8835349340811341678767469)
                    ·
                      refine ⟨3313256002804253129537801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8835349340811341678767469 3313256002804253129537801)
                      ·
                        rfl

theorem cell23_6452543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_6452543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452543 prefixEnd_6452543 := by exact prefixLift 6452543
  have htrace : WordTrace (prefixWord ++ tailWord_6452543) baseStart_6452543 baseEnd_6452543 := by
    simpa [prefixWord, tailWord_6452543, baseEnd_6452543] using wordTrace_append hprefix tailTrace_6452543
  have hstable : (prefixWord ++ tailWord_6452543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452543).length < 2 ^ (prefixWord ++ tailWord_6452543).sum := by decide
  have hdescent : baseEnd_6452543 < baseStart_6452543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452553 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 2, 3, 2]
def baseStart_6452553 : Nat := 118140960795 + 6452553 * 2 ^ 59
def prefixEnd_6452553 : Nat := 4983230072969 + 3 ^ 40 * 6452553 * 2
def baseEnd_6452553 : Nat := 3313261137610798090412755

theorem tailTrace_6452553 : CollatzResearch.WordTrace tailWord_6452553 prefixEnd_6452553 3313261137610798090412755 := by
  unfold tailWord_6452553
  simp only [CollatzResearch.WordTrace]
  refine ⟨235343942192509964162146313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156895961461673309441430875 235343942192509964162146313)
  ·
    refine ⟨176507956644382473121609735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235343942192509964162146313 176507956644382473121609735)
    ·
      refine ⟨264761934966573709682414603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176507956644382473121609735 264761934966573709682414603)
      ·
        refine ⟨397142902449860564523621905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264761934966573709682414603 397142902449860564523621905)
        ·
          refine ⟨297857176837395423392716429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397142902449860564523621905 297857176837395423392716429)
          ·
            refine ⟨111696441314023283772268661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297857176837395423392716429 111696441314023283772268661)
            ·
              refine ⟨10471541373189682853650187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111696441314023283772268661 10471541373189682853650187)
              ·
                refine ⟨15707312059784524280475281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10471541373189682853650187 15707312059784524280475281)
                ·
                  refine ⟨11780484044838393210356461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15707312059784524280475281 11780484044838393210356461)
                  ·
                    refine ⟨4417681516814397453883673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11780484044838393210356461 4417681516814397453883673)
                    ·
                      refine ⟨3313261137610798090412755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417681516814397453883673 3313261137610798090412755)
                      ·
                        rfl

theorem cell23_6452553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 3, 2].length) (baseStart_6452553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452553 prefixEnd_6452553 := by exact prefixLift 6452553
  have htrace : WordTrace (prefixWord ++ tailWord_6452553) baseStart_6452553 baseEnd_6452553 := by
    simpa [prefixWord, tailWord_6452553, baseEnd_6452553] using wordTrace_append hprefix tailTrace_6452553
  have hstable : (prefixWord ++ tailWord_6452553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452553).length < 2 ^ (prefixWord ++ tailWord_6452553).sum := by decide
  have hdescent : baseEnd_6452553 < baseStart_6452553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452560 : List Nat := [2, 1, 1, 1, 1, 5, 4, 3, 1, 1, 3]
def baseStart_6452560 : Nat := 118140960795 + 6452560 * 2 ^ 59
def prefixEnd_6452560 : Nat := 4983230072969 + 3 ^ 40 * 6452560 * 2
def baseEnd_6452560 : Nat := 3313264731975379563025223

theorem tailTrace_6452560 : CollatzResearch.WordTrace tailWord_6452560 prefixEnd_6452560 3313264731975379563025223 := by
  unfold tailWord_6452560
  simp only [CollatzResearch.WordTrace]
  refine ⟨117672098751742302178825567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156896131668989736238434089 117672098751742302178825567)
  ·
    refine ⟨176508148127613453268238351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117672098751742302178825567 176508148127613453268238351)
    ·
      refine ⟨264762222191420179902357527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176508148127613453268238351 264762222191420179902357527)
      ·
        refine ⟨397143333287130269853536291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264762222191420179902357527 397143333287130269853536291)
        ·
          refine ⟨595714999930695404780304437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397143333287130269853536291 595714999930695404780304437)
          ·
            refine ⟨55848281243502694198153541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 595714999930695404780304437 55848281243502694198153541)
            ·
              refine ⟨10471552733156755162153789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55848281243502694198153541 10471552733156755162153789)
              ·
                refine ⟨3926832274933783185807671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10471552733156755162153789 3926832274933783185807671)
                ·
                  refine ⟨5890248412400674778711507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926832274933783185807671 5890248412400674778711507)
                  ·
                    refine ⟨8835372618601012168067261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5890248412400674778711507 8835372618601012168067261)
                    ·
                      refine ⟨3313264731975379563025223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8835372618601012168067261 3313264731975379563025223)
                      ·
                        rfl

theorem cell23_6452560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 1, 1, 3].length) (baseStart_6452560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452560 prefixEnd_6452560 := by exact prefixLift 6452560
  have htrace : WordTrace (prefixWord ++ tailWord_6452560) baseStart_6452560 baseEnd_6452560 := by
    simpa [prefixWord, tailWord_6452560, baseEnd_6452560] using wordTrace_append hprefix tailTrace_6452560
  have hstable : (prefixWord ++ tailWord_6452560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452560).length < 2 ^ (prefixWord ++ tailWord_6452560).sum := by decide
  have hdescent : baseEnd_6452560 < baseStart_6452560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452603 : List Nat := [1, 1, 1, 1, 1, 6, 4, 2, 1, 2, 3]
def baseStart_6452603 : Nat := 118140960795 + 6452603 * 2 ^ 59
def prefixEnd_6452603 : Nat := 4983230072969 + 3 ^ 40 * 6452603 * 2
def baseEnd_6452603 : Nat := 3313286811643522894787525

theorem tailTrace_6452603 : CollatzResearch.WordTrace tailWord_6452603 prefixEnd_6452603 3313286811643522894787525 := by
  unfold tailWord_6452603
  simp only [CollatzResearch.WordTrace]
  refine ⟨235345765842328822701466463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156897177228219215134310975 235345765842328822701466463)
  ·
    refine ⟨353018648763493234052199695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235345765842328822701466463 353018648763493234052199695)
    ·
      refine ⟨529527973145239851078299543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353018648763493234052199695 529527973145239851078299543)
      ·
        refine ⟨794291959717859776617449315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529527973145239851078299543 794291959717859776617449315)
        ·
          refine ⟨1191437939576789664926173973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794291959717859776617449315 1191437939576789664926173973)
          ·
            refine ⟨55848653417662015543414405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1191437939576789664926173973 55848653417662015543414405)
            ·
              refine ⟨10471622515811627914390201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55848653417662015543414405 10471622515811627914390201)
              ·
                refine ⟨7853716886858720935792651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10471622515811627914390201 7853716886858720935792651)
                ·
                  refine ⟨11780575330288081403688977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7853716886858720935792651 11780575330288081403688977)
                  ·
                    refine ⟨8835431497716061052766733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11780575330288081403688977 8835431497716061052766733)
                    ·
                      refine ⟨3313286811643522894787525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8835431497716061052766733 3313286811643522894787525)
                      ·
                        rfl

theorem cell23_6452603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 2, 3].length) (baseStart_6452603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452603 prefixEnd_6452603 := by exact prefixLift 6452603
  have htrace : WordTrace (prefixWord ++ tailWord_6452603) baseStart_6452603 baseEnd_6452603 := by
    simpa [prefixWord, tailWord_6452603, baseEnd_6452603] using wordTrace_append hprefix tailTrace_6452603
  have hstable : (prefixWord ++ tailWord_6452603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452603).length < 2 ^ (prefixWord ++ tailWord_6452603).sum := by decide
  have hdescent : baseEnd_6452603 < baseStart_6452603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452610 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_6452610 : Nat := 118140960795 + 6452610 * 2 ^ 59
def prefixEnd_6452610 : Nat := 4983230072969 + 3 ^ 40 * 6452610 * 2
def baseEnd_6452610 : Nat := 1104430135336034789133331

theorem tailTrace_6452610 : CollatzResearch.WordTrace tailWord_6452610 prefixEnd_6452610 1104430135336034789133331 := by
  unfold tailWord_6452610
  simp only [CollatzResearch.WordTrace]
  refine ⟨58836505288325865724242821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156897347435535641931314189 58836505288325865724242821)
  ·
    refine ⟨11031844741561099823295529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58836505288325865724242821 11031844741561099823295529)
    ·
      refine ⟨8273883556170824867471647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11031844741561099823295529 8273883556170824867471647)
      ·
        refine ⟨12410825334256237301207471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8273883556170824867471647 12410825334256237301207471)
        ·
          refine ⟨18616238001384355951811207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12410825334256237301207471 18616238001384355951811207)
          ·
            refine ⟨27924357002076533927716811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18616238001384355951811207 27924357002076533927716811)
            ·
              refine ⟨41886535503114800891575217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27924357002076533927716811 41886535503114800891575217)
              ·
                refine ⟨31414901627336100668681413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41886535503114800891575217 31414901627336100668681413)
                ·
                  refine ⟨5890294055125518875377765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31414901627336100668681413 5890294055125518875377765)
                  ·
                    refine ⟨1104430135336034789133331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5890294055125518875377765 1104430135336034789133331)
                    ·
                      rfl

theorem cell23_6452610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_6452610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452610 prefixEnd_6452610 := by exact prefixLift 6452610
  have htrace : WordTrace (prefixWord ++ tailWord_6452610) baseStart_6452610 baseEnd_6452610 := by
    simpa [prefixWord, tailWord_6452610, baseEnd_6452610] using wordTrace_append hprefix tailTrace_6452610
  have hstable : (prefixWord ++ tailWord_6452610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452610).length < 2 ^ (prefixWord ++ tailWord_6452610).sum := by decide
  have hdescent : baseEnd_6452610 < baseStart_6452610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452633 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 4, 1, 3]
def baseStart_6452633 : Nat := 118140960795 + 6452633 * 2 ^ 59
def prefixEnd_6452633 : Nat := 4983230072969 + 3 ^ 40 * 6452633 * 2
def baseEnd_6452633 : Nat := 3313302216063157777412387

theorem tailTrace_6452633 : CollatzResearch.WordTrace tailWord_6452633 prefixEnd_6452633 3313302216063157777412387 := by
  unfold tailWord_6452633
  simp only [CollatzResearch.WordTrace]
  refine ⟨235346860032220137825058553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156897906688146758550039035 235346860032220137825058553)
  ·
    refine ⟨176510145024165103368793915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235346860032220137825058553 176510145024165103368793915)
    ·
      refine ⟨264765217536247655053190873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176510145024165103368793915 264765217536247655053190873)
      ·
        refine ⟨198573913152185741289893155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264765217536247655053190873 198573913152185741289893155)
        ·
          refine ⟨297860869728278611934839733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198573913152185741289893155 297860869728278611934839733)
          ·
            refine ⟨27924456537026119868891225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 297860869728278611934839733 27924456537026119868891225)
            ·
              refine ⟨20943342402769589901668419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27924456537026119868891225 20943342402769589901668419)
              ·
                refine ⟨31415013604154384852502629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20943342402769589901668419 31415013604154384852502629)
                ·
                  refine ⟨5890315050778947159844243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31415013604154384852502629 5890315050778947159844243)
                  ·
                    refine ⟨8835472576168420739766365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5890315050778947159844243 8835472576168420739766365)
                    ·
                      refine ⟨3313302216063157777412387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8835472576168420739766365 3313302216063157777412387)
                      ·
                        rfl

theorem cell23_6452633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_6452633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452633 prefixEnd_6452633 := by exact prefixLift 6452633
  have htrace : WordTrace (prefixWord ++ tailWord_6452633) baseStart_6452633 baseEnd_6452633 := by
    simpa [prefixWord, tailWord_6452633, baseEnd_6452633] using wordTrace_append hprefix tailTrace_6452633
  have hstable : (prefixWord ++ tailWord_6452633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452633).length < 2 ^ (prefixWord ++ tailWord_6452633).sum := by decide
  have hdescent : baseEnd_6452633 < baseStart_6452633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452634 : List Nat := [3, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2]
def baseStart_6452634 : Nat := 118140960795 + 6452634 * 2 ^ 59
def prefixEnd_6452634 : Nat := 4983230072969 + 3 ^ 40 * 6452634 * 2
def baseEnd_6452634 : Nat := 3313302729543812273499883

theorem tailTrace_6452634 : CollatzResearch.WordTrace tailWord_6452634 prefixEnd_6452634 3313302729543812273499883 := by
  unfold tailWord_6452634
  simp only [CollatzResearch.WordTrace]
  refine ⟨58836724126304128748961239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156897931003477676663896637 58836724126304128748961239)
  ·
    refine ⟨88255086189456193123441859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58836724126304128748961239 88255086189456193123441859)
    ·
      refine ⟨132382629284184289685162789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88255086189456193123441859 132382629284184289685162789)
      ·
        refine ⟨24821742990784554315968023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132382629284184289685162789 24821742990784554315968023)
        ·
          refine ⟨37232614486176831473952035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24821742990784554315968023 37232614486176831473952035)
          ·
            refine ⟨55848921729265247210928053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37232614486176831473952035 55848921729265247210928053)
            ·
              refine ⟨5235836412118616926024505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55848921729265247210928053 5235836412118616926024505)
              ·
                refine ⟨3926877309088962694518379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5235836412118616926024505 3926877309088962694518379)
                ·
                  refine ⟨5890315963633444041777569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926877309088962694518379 5890315963633444041777569)
                  ·
                    refine ⟨4417736972725083031333177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5890315963633444041777569 4417736972725083031333177)
                    ·
                      refine ⟨3313302729543812273499883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417736972725083031333177 3313302729543812273499883)
                      ·
                        rfl

theorem cell23_6452634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_6452634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452634 prefixEnd_6452634 := by exact prefixLift 6452634
  have htrace : WordTrace (prefixWord ++ tailWord_6452634) baseStart_6452634 baseEnd_6452634 := by
    simpa [prefixWord, tailWord_6452634, baseEnd_6452634] using wordTrace_append hprefix tailTrace_6452634
  have hstable : (prefixWord ++ tailWord_6452634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452634).length < 2 ^ (prefixWord ++ tailWord_6452634).sum := by decide
  have hdescent : baseEnd_6452634 < baseStart_6452634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452643 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 3, 3, 2]
def baseStart_6452643 : Nat := 118140960795 + 6452643 * 2 ^ 59
def prefixEnd_6452643 : Nat := 4983230072969 + 3 ^ 40 * 6452643 * 2
def baseEnd_6452643 : Nat := 3313307350869702738287341

theorem tailTrace_6452643 : CollatzResearch.WordTrace tailWord_6452643 prefixEnd_6452643 3313307350869702738287341 := by
  unfold tailWord_6452643
  simp only [CollatzResearch.WordTrace]
  refine ⟨235347224762183909532922583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156898149841455939688615055 235347224762183909532922583)
  ·
    refine ⟨353020837143275864299383875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235347224762183909532922583 353020837143275864299383875)
    ·
      refine ⟨529531255714913796449075813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353020837143275864299383875 529531255714913796449075813)
      ·
        refine ⟨99287110446546336834201715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 529531255714913796449075813 99287110446546336834201715)
        ·
          refine ⟨148930665669819505251302573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99287110446546336834201715 148930665669819505251302573)
          ·
            refine ⟨55848999626182314469238465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148930665669819505251302573 55848999626182314469238465)
            ·
              refine ⟨41886749719636735851928849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55848999626182314469238465 41886749719636735851928849)
              ·
                refine ⟨31415062289727551888946637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41886749719636735851928849 31415062289727551888946637)
                ·
                  refine ⟨11780648358647831958354989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31415062289727551888946637 11780648358647831958354989)
                  ·
                    refine ⟨4417743134492936984383121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11780648358647831958354989 4417743134492936984383121)
                    ·
                      refine ⟨3313307350869702738287341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417743134492936984383121 3313307350869702738287341)
                      ·
                        rfl

theorem cell23_6452643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_6452643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452643 prefixEnd_6452643 := by exact prefixLift 6452643
  have htrace : WordTrace (prefixWord ++ tailWord_6452643) baseStart_6452643 baseEnd_6452643 := by
    simpa [prefixWord, tailWord_6452643, baseEnd_6452643] using wordTrace_append hprefix tailTrace_6452643
  have hstable : (prefixWord ++ tailWord_6452643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452643).length < 2 ^ (prefixWord ++ tailWord_6452643).sum := by decide
  have hdescent : baseEnd_6452643 < baseStart_6452643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452707 : List Nat := [1, 1, 1, 6, 2, 1, 2, 3, 2, 2, 2]
def baseStart_6452707 : Nat := 118140960795 + 6452707 * 2 ^ 59
def prefixEnd_6452707 : Nat := 4983230072969 + 3 ^ 40 * 6452707 * 2
def baseEnd_6452707 : Nat := 3313340213631590487887047

theorem tailTrace_6452707 : CollatzResearch.WordTrace tailWord_6452707 prefixEnd_6452707 3313340213631590487887047 := by
  unfold tailWord_6452707
  simp only [CollatzResearch.WordTrace]
  refine ⟨235349559033952048463252375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156899706022634698975501583 235349559033952048463252375)
  ·
    refine ⟨353024338550928072694878563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235349559033952048463252375 353024338550928072694878563)
    ·
      refine ⟨529536507826392109042317845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353024338550928072694878563 529536507826392109042317845)
      ·
        refine ⟨24822023804362130111358649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 529536507826392109042317845 24822023804362130111358649)
        ·
          refine ⟨18616517853271597583518987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24822023804362130111358649 18616517853271597583518987)
          ·
            refine ⟨27924776779907396375278481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18616517853271597583518987 27924776779907396375278481)
            ·
              refine ⟨20943582584930547281458861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27924776779907396375278481 20943582584930547281458861)
              ·
                refine ⟨7853843469348955230547073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20943582584930547281458861 7853843469348955230547073)
                ·
                  refine ⟨5890382602011716422910305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7853843469348955230547073 5890382602011716422910305)
                  ·
                    refine ⟨4417786951508787317182729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5890382602011716422910305 4417786951508787317182729)
                    ·
                      refine ⟨3313340213631590487887047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417786951508787317182729 3313340213631590487887047)
                      ·
                        rfl

theorem cell23_6452707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_6452707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452707 prefixEnd_6452707 := by exact prefixLift 6452707
  have htrace : WordTrace (prefixWord ++ tailWord_6452707) baseStart_6452707 baseEnd_6452707 := by
    simpa [prefixWord, tailWord_6452707, baseEnd_6452707] using wordTrace_append hprefix tailTrace_6452707
  have hstable : (prefixWord ++ tailWord_6452707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452707).length < 2 ^ (prefixWord ++ tailWord_6452707).sum := by decide
  have hdescent : baseEnd_6452707 < baseStart_6452707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452807 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 3, 4]
def baseStart_6452807 : Nat := 118140960795 + 6452807 * 2 ^ 59
def prefixEnd_6452807 : Nat := 4983230072969 + 3 ^ 40 * 6452807 * 2
def baseEnd_6452807 : Nat := 1104463853899013365545529

theorem tailTrace_6452807 : CollatzResearch.WordTrace tailWord_6452807 prefixEnd_6452807 1104463853899013365545529 := by
  unfold tailWord_6452807
  simp only [CollatzResearch.WordTrace]
  refine ⟨235353206333589765541892675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156902137555726510361261783 235353206333589765541892675)
  ·
    refine ⟨353029809500384648312839013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235353206333589765541892675 353029809500384648312839013)
    ·
      refine ⟨66193089281322121558657315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353029809500384648312839013 66193089281322121558657315)
      ·
        refine ⟨99289633921983182337985973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66193089281322121558657315 99289633921983182337985973)
        ·
          refine ⟨9308403180185923344186185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99289633921983182337985973 9308403180185923344186185)
          ·
            refine ⟨6981302385139442508139639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9308403180185923344186185 6981302385139442508139639)
            ·
              refine ⟨10471953577709163762209459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6981302385139442508139639 10471953577709163762209459)
              ·
                refine ⟨15707930366563745643314189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10471953577709163762209459 15707930366563745643314189)
                ·
                  refine ⟨5890473887461404616242821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15707930366563745643314189 5890473887461404616242821)
                  ·
                    refine ⟨1104463853899013365545529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5890473887461404616242821 1104463853899013365545529)
                    ·
                      rfl

theorem cell23_6452807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_6452807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452807 prefixEnd_6452807 := by exact prefixLift 6452807
  have htrace : WordTrace (prefixWord ++ tailWord_6452807) baseStart_6452807 baseEnd_6452807 := by
    simpa [prefixWord, tailWord_6452807, baseEnd_6452807] using wordTrace_append hprefix tailTrace_6452807
  have hstable : (prefixWord ++ tailWord_6452807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452807).length < 2 ^ (prefixWord ++ tailWord_6452807).sum := by decide
  have hdescent : baseEnd_6452807 < baseStart_6452807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452833 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 3, 5]
def baseStart_6452833 : Nat := 118140960795 + 6452833 * 2 ^ 59
def prefixEnd_6452833 : Nat := 4983230072969 + 3 ^ 40 * 6452833 * 2
def baseEnd_6452833 : Nat := 1104468304064685664970489

theorem tailTrace_6452833 : CollatzResearch.WordTrace tailWord_6452833 prefixEnd_6452833 1104468304064685664970489 := by
  unfold tailWord_6452833
  simp only [CollatzResearch.WordTrace]
  refine ⟨235354154631495571982339153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156902769754330381321559435 235354154631495571982339153)
  ·
    refine ⟨176515615973621678986754365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235354154631495571982339153 176515615973621678986754365)
    ·
      refine ⟨66193355990108129620032887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176515615973621678986754365 66193355990108129620032887)
      ·
        refine ⟨99290033985162194430049331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66193355990108129620032887 99290033985162194430049331)
        ·
          refine ⟨148935050977743291645073997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99290033985162194430049331 148935050977743291645073997)
          ·
            refine ⟨55850644116653734366902749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148935050977743291645073997 55850644116653734366902749)
            ·
              refine ⟨20943991543745150387588531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55850644116653734366902749 20943991543745150387588531)
              ·
                refine ⟨31415987315617725581382797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20943991543745150387588531 31415987315617725581382797)
                ·
                  refine ⟨11780995243356647093018549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31415987315617725581382797 11780995243356647093018549)
                  ·
                    refine ⟨1104468304064685664970489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11780995243356647093018549 1104468304064685664970489)
                    ·
                      rfl

theorem cell23_6452833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_6452833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452833 prefixEnd_6452833 := by exact prefixLift 6452833
  have htrace : WordTrace (prefixWord ++ tailWord_6452833) baseStart_6452833 baseEnd_6452833 := by
    simpa [prefixWord, tailWord_6452833, baseEnd_6452833] using wordTrace_append hprefix tailTrace_6452833
  have hstable : (prefixWord ++ tailWord_6452833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452833).length < 2 ^ (prefixWord ++ tailWord_6452833).sum := by decide
  have hdescent : baseEnd_6452833 < baseStart_6452833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452847 : List Nat := [1, 1, 2, 1, 3, 2, 1, 7, 1, 1, 3]
def baseStart_6452847 : Nat := 118140960795 + 6452847 * 2 ^ 59
def prefixEnd_6452847 : Nat := 4983230072969 + 3 ^ 40 * 6452847 * 2
def baseEnd_6452847 : Nat := 3313412100923219940136403

theorem tailTrace_6452847 : CollatzResearch.WordTrace tailWord_6452847 prefixEnd_6452847 3313412100923219940136403 := by
  unfold tailWord_6452847
  simp only [CollatzResearch.WordTrace]
  refine ⟨235354665253444852373348795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156903110168963234915565863 235354665253444852373348795)
  ·
    refine ⟨353031997880167278560023193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235354665253444852373348795 353031997880167278560023193)
    ·
      refine ⟨264773998410125458920017395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353031997880167278560023193 264773998410125458920017395)
      ·
        refine ⟨397160997615188188380026093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264773998410125458920017395 397160997615188188380026093)
        ·
          refine ⟨148935374105695570642509785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397160997615188188380026093 148935374105695570642509785)
          ·
            refine ⟨111701530579271677981882339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148935374105695570642509785 111701530579271677981882339)
            ·
              refine ⟨167552295868907516972823509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111701530579271677981882339 167552295868907516972823509)
              ·
                refine ⟨3927006934427519929050551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 167552295868907516972823509 3927006934427519929050551)
                ·
                  refine ⟨5890510401641279893575827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3927006934427519929050551 5890510401641279893575827)
                  ·
                    refine ⟨8835765602461919840363741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5890510401641279893575827 8835765602461919840363741)
                    ·
                      refine ⟨3313412100923219940136403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8835765602461919840363741 3313412100923219940136403)
                      ·
                        rfl

theorem cell23_6452847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 1, 1, 3].length) (baseStart_6452847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452847 prefixEnd_6452847 := by exact prefixLift 6452847
  have htrace : WordTrace (prefixWord ++ tailWord_6452847) baseStart_6452847 baseEnd_6452847 := by
    simpa [prefixWord, tailWord_6452847, baseEnd_6452847] using wordTrace_append hprefix tailTrace_6452847
  have hstable : (prefixWord ++ tailWord_6452847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452847).length < 2 ^ (prefixWord ++ tailWord_6452847).sum := by decide
  have hdescent : baseEnd_6452847 < baseStart_6452847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452863 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 8, 4]
def baseStart_6452863 : Nat := 118140960795 + 6452863 * 2 ^ 59
def prefixEnd_6452863 : Nat := 4983230072969 + 3 ^ 40 * 6452863 * 2
def baseEnd_6452863 : Nat := 1104473438871230625845443

theorem tailTrace_6452863 : CollatzResearch.WordTrace tailWord_6452863 prefixEnd_6452863 1104473438871230625845443 := by
  unfold tailWord_6452863
  simp only [CollatzResearch.WordTrace]
  refine ⟨235355248821386887105931243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156903499214257924737287495 235355248821386887105931243)
  ·
    refine ⟨353032873232080330658896865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235355248821386887105931243 353032873232080330658896865)
    ·
      refine ⟨264774654924060247994172649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353032873232080330658896865 264774654924060247994172649)
      ·
        refine ⟨198580991193045185995629487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264774654924060247994172649 198580991193045185995629487)
        ·
          refine ⟨297871486789567778993444231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198580991193045185995629487 297871486789567778993444231)
          ·
            refine ⟨446807230184351668490166347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297871486789567778993444231 446807230184351668490166347)
            ·
              refine ⟨670210845276527502735249521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446807230184351668490166347 670210845276527502735249521)
              ·
                refine ⟨502658133957395627051437141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670210845276527502735249521 502658133957395627051437141)
                ·
                  refine ⟨5890525007313230004509029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 502658133957395627051437141 5890525007313230004509029)
                  ·
                    refine ⟨1104473438871230625845443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5890525007313230004509029 1104473438871230625845443)
                    ·
                      rfl

theorem cell23_6452863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 4].length) (baseStart_6452863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452863 prefixEnd_6452863 := by exact prefixLift 6452863
  have htrace : WordTrace (prefixWord ++ tailWord_6452863) baseStart_6452863 baseEnd_6452863 := by
    simpa [prefixWord, tailWord_6452863, baseEnd_6452863] using wordTrace_append hprefix tailTrace_6452863
  have hstable : (prefixWord ++ tailWord_6452863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452863).length < 2 ^ (prefixWord ++ tailWord_6452863).sum := by decide
  have hdescent : baseEnd_6452863 < baseStart_6452863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452873 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 1, 1, 5]
def baseStart_6452873 : Nat := 118140960795 + 6452873 * 2 ^ 59
def prefixEnd_6452873 : Nat := 4983230072969 + 3 ^ 40 * 6452873 * 2
def baseEnd_6452873 : Nat := 3313425451420236838411283

theorem tailTrace_6452873 : CollatzResearch.WordTrace tailWord_6452873 prefixEnd_6452873 3313425451420236838411283 := by
  unfold tailWord_6452873
  simp only [CollatzResearch.WordTrace]
  refine ⟨235355613551350658813795273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156903742367567105875863515 235355613551350658813795273)
  ·
    refine ⟨176516710163512994110346455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235355613551350658813795273 176516710163512994110346455)
    ·
      refine ⟨264775065245269491165519683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176516710163512994110346455 264775065245269491165519683)
      ·
        refine ⟨397162597867904236748279525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264775065245269491165519683 397162597867904236748279525)
        ·
          refine ⟨74467987100232044390302411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397162597867904236748279525 74467987100232044390302411)
          ·
            refine ⟨111701980650348066585453617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74467987100232044390302411 111701980650348066585453617)
            ·
              refine ⟨83776485487761049939090213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111701980650348066585453617 83776485487761049939090213)
              ·
                refine ⟨15708091028955196863579415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83776485487761049939090213 15708091028955196863579415)
                ·
                  refine ⟨23562136543432795295369123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15708091028955196863579415 23562136543432795295369123)
                  ·
                    refine ⟨35343204815149192943053685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23562136543432795295369123 35343204815149192943053685)
                    ·
                      refine ⟨3313425451420236838411283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35343204815149192943053685 3313425451420236838411283)
                      ·
                        rfl

theorem cell23_6452873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_6452873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452873 prefixEnd_6452873 := by exact prefixLift 6452873
  have htrace : WordTrace (prefixWord ++ tailWord_6452873) baseStart_6452873 baseEnd_6452873 := by
    simpa [prefixWord, tailWord_6452873, baseEnd_6452873] using wordTrace_append hprefix tailTrace_6452873
  have hstable : (prefixWord ++ tailWord_6452873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452873).length < 2 ^ (prefixWord ++ tailWord_6452873).sum := by decide
  have hdescent : baseEnd_6452873 < baseStart_6452873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452887 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 5, 2, 2]
def baseStart_6452887 : Nat := 118140960795 + 6452887 * 2 ^ 59
def prefixEnd_6452887 : Nat := 4983230072969 + 3 ^ 40 * 6452887 * 2
def baseEnd_6452887 : Nat := 3313432640149399783636219

theorem tailTrace_6452887 : CollatzResearch.WordTrace tailWord_6452887 prefixEnd_6452887 3313432640149399783636219 := by
  unfold tailWord_6452887
  simp only [CollatzResearch.WordTrace]
  refine ⟨235356124173299939204804915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156904082782199959469869943 235356124173299939204804915)
  ·
    refine ⟨353034186259949908807207373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235356124173299939204804915 353034186259949908807207373)
    ·
      refine ⟨132387819847481215802702765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353034186259949908807207373 132387819847481215802702765)
      ·
        refine ⟨49645432442805455926013537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132387819847481215802702765 49645432442805455926013537)
        ·
          refine ⟨37234074332104091944510153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49645432442805455926013537 37234074332104091944510153)
          ·
            refine ⟨27925555749078068958382615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37234074332104091944510153 27925555749078068958382615)
            ·
              refine ⟨41888333623617103437573923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27925555749078068958382615 41888333623617103437573923)
              ·
                refine ⟨62832500435425655156360885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41888333623617103437573923 62832500435425655156360885)
                ·
                  refine ⟨5890546915821155170908833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62832500435425655156360885 5890546915821155170908833)
                  ·
                    refine ⟨4417910186865866378181625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5890546915821155170908833 4417910186865866378181625)
                    ·
                      refine ⟨3313432640149399783636219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417910186865866378181625 3313432640149399783636219)
                      ·
                        rfl

theorem cell23_6452887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_6452887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452887 prefixEnd_6452887 := by exact prefixLift 6452887
  have htrace : WordTrace (prefixWord ++ tailWord_6452887) baseStart_6452887 baseEnd_6452887 := by
    simpa [prefixWord, tailWord_6452887, baseEnd_6452887] using wordTrace_append hprefix tailTrace_6452887
  have hstable : (prefixWord ++ tailWord_6452887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452887).length < 2 ^ (prefixWord ++ tailWord_6452887).sum := by decide
  have hdescent : baseEnd_6452887 < baseStart_6452887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452898 : List Nat := [3, 3, 1, 4, 1, 1, 2, 3, 1, 1, 3]
def baseStart_6452898 : Nat := 118140960795 + 6452898 * 2 ^ 59
def prefixEnd_6452898 : Nat := 4983230072969 + 3 ^ 40 * 6452898 * 2
def baseEnd_6452898 : Nat := 3313438288436599240598669

theorem tailTrace_6452898 : CollatzResearch.WordTrace tailWord_6452898 prefixEnd_6452898 3313438288436599240598669 := by
  unfold tailWord_6452898
  simp only [CollatzResearch.WordTrace]
  refine ⟨58839131344065022020863837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156904350250840058722303565 58839131344065022020863837)
  ·
    refine ⟨22064674254024383257823939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58839131344065022020863837 22064674254024383257823939)
    ·
      refine ⟨33097011381036574886735909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22064674254024383257823939 33097011381036574886735909)
      ·
        refine ⟨6205689633944357791262983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33097011381036574886735909 6205689633944357791262983)
        ·
          refine ⟨9308534450916536686894475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6205689633944357791262983 9308534450916536686894475)
          ·
            refine ⟨13962801676374805030341713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9308534450916536686894475 13962801676374805030341713)
            ·
              refine ⟨10472101257281103772756285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13962801676374805030341713 10472101257281103772756285)
              ·
                refine ⟨3927037971480413914783607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10472101257281103772756285 3927037971480413914783607)
                ·
                  refine ⟨5890556957220620872175411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3927037971480413914783607 5890556957220620872175411)
                  ·
                    refine ⟨8835835435830931308263117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5890556957220620872175411 8835835435830931308263117)
                    ·
                      refine ⟨3313438288436599240598669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8835835435830931308263117 3313438288436599240598669)
                      ·
                        rfl

theorem cell23_6452898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_6452898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452898 prefixEnd_6452898 := by exact prefixLift 6452898
  have htrace : WordTrace (prefixWord ++ tailWord_6452898) baseStart_6452898 baseEnd_6452898 := by
    simpa [prefixWord, tailWord_6452898, baseEnd_6452898] using wordTrace_append hprefix tailTrace_6452898
  have hstable : (prefixWord ++ tailWord_6452898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452898).length < 2 ^ (prefixWord ++ tailWord_6452898).sum := by decide
  have hdescent : baseEnd_6452898 < baseStart_6452898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452900 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_6452900 : Nat := 118140960795 + 6452900 * 2 ^ 59
def prefixEnd_6452900 : Nat := 4983230072969 + 3 ^ 40 * 6452900 * 2
def baseEnd_6452900 : Nat := 3313439315397908232773659

theorem tailTrace_6452900 : CollatzResearch.WordTrace tailWord_6452900 prefixEnd_6452900 3313439315397908232773659 := by
  unfold tailWord_6452900
  simp only [CollatzResearch.WordTrace]
  refine ⟨117678299161126421212514077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156904398881501894950018769 117678299161126421212514077)
  ·
    refine ⟨44129362185422407954692779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117678299161126421212514077 44129362185422407954692779)
    ·
      refine ⟨66194043278133611932039169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44129362185422407954692779 66194043278133611932039169)
      ·
        refine ⟨49645532458600208949029377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66194043278133611932039169 49645532458600208949029377)
        ·
          refine ⟨37234149343950156711772033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49645532458600208949029377 37234149343950156711772033)
          ·
            refine ⟨27925612007962617533829025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37234149343950156711772033 27925612007962617533829025)
            ·
              refine ⟨20944209005971963150371769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27925612007962617533829025 20944209005971963150371769)
              ·
                refine ⟨15708156754478972362778827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20944209005971963150371769 15708156754478972362778827)
                ·
                  refine ⟨23562235131718458544168241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15708156754478972362778827 23562235131718458544168241)
                  ·
                    refine ⟨17671676348788843908126181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23562235131718458544168241 17671676348788843908126181)
                    ·
                      refine ⟨3313439315397908232773659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17671676348788843908126181 3313439315397908232773659)
                      ·
                        rfl

theorem cell23_6452900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_6452900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452900 prefixEnd_6452900 := by exact prefixLift 6452900
  have htrace : WordTrace (prefixWord ++ tailWord_6452900) baseStart_6452900 baseEnd_6452900 := by
    simpa [prefixWord, tailWord_6452900, baseEnd_6452900] using wordTrace_append hprefix tailTrace_6452900
  have hstable : (prefixWord ++ tailWord_6452900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452900).length < 2 ^ (prefixWord ++ tailWord_6452900).sum := by decide
  have hdescent : baseEnd_6452900 < baseStart_6452900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452934 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6452934 : Nat := 118140960795 + 6452934 * 2 ^ 59
def prefixEnd_6452934 : Nat := 4983230072969 + 3 ^ 40 * 6452934 * 2
def baseEnd_6452934 : Nat := 3313456773740161099748503

theorem tailTrace_6452934 : CollatzResearch.WordTrace tailWord_6452934 prefixEnd_6452934 3313456773740161099748503 := by
  unfold tailWord_6452934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7354932450129052069742683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156905225602753110821177237 7354932450129052069742683)
  ·
    refine ⟨11032398675193578104614025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7354932450129052069742683 11032398675193578104614025)
    ·
      refine ⟨8274299006395183578460519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11032398675193578104614025 8274299006395183578460519)
      ·
        refine ⟨12411448509592775367690779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8274299006395183578460519 12411448509592775367690779)
        ·
          refine ⟨18617172764389163051536169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12411448509592775367690779 18617172764389163051536169)
          ·
            refine ⟨13962879573291872288652127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18617172764389163051536169 13962879573291872288652127)
            ·
              refine ⟨20944319359937808432978191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13962879573291872288652127 20944319359937808432978191)
              ·
                refine ⟨31416479039906712649467287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20944319359937808432978191 31416479039906712649467287)
                ·
                  refine ⟨47124718559860068974200931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31416479039906712649467287 47124718559860068974200931)
                  ·
                    refine ⟨70687077839790103461301397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47124718559860068974200931 70687077839790103461301397)
                    ·
                      refine ⟨3313456773740161099748503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70687077839790103461301397 3313456773740161099748503)
                      ·
                        rfl

theorem cell23_6452934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6452934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452934 prefixEnd_6452934 := by exact prefixLift 6452934
  have htrace : WordTrace (prefixWord ++ tailWord_6452934) baseStart_6452934 baseEnd_6452934 := by
    simpa [prefixWord, tailWord_6452934, baseEnd_6452934] using wordTrace_append hprefix tailTrace_6452934
  have hstable : (prefixWord ++ tailWord_6452934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452934).length < 2 ^ (prefixWord ++ tailWord_6452934).sum := by decide
  have hdescent : baseEnd_6452934 < baseStart_6452934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452941 : List Nat := [1, 6, 2, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_6452941 : Nat := 118140960795 + 6452941 * 2 ^ 59
def prefixEnd_6452941 : Nat := 4983230072969 + 3 ^ 40 * 6452941 * 2
def baseEnd_6452941 : Nat := 3313460368104742572360971

theorem tailTrace_6452941 : CollatzResearch.WordTrace tailWord_6452941 prefixEnd_6452941 3313460368104742572360971 := by
  unfold tailWord_6452941
  simp only [CollatzResearch.WordTrace]
  refine ⟨235358093715104306427270677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156905395810069537618180451 235358093715104306427270677)
  ·
    refine ⟨11032410642895514363778313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 235358093715104306427270677 11032410642895514363778313)
    ·
      refine ⟨8274307982171635772833735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11032410642895514363778313 8274307982171635772833735)
      ·
        refine ⟨12411461973257453659250603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8274307982171635772833735 12411461973257453659250603)
        ·
          refine ⟨18617192959886180488875905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12411461973257453659250603 18617192959886180488875905)
          ·
            refine ⟨13962894719914635366656929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18617192959886180488875905 13962894719914635366656929)
            ·
              refine ⟨10472171039935976524992697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13962894719914635366656929 10472171039935976524992697)
              ·
                refine ⟨7854128279951982393744523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10472171039935976524992697 7854128279951982393744523)
                ·
                  refine ⟨11781192419927973590616785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7854128279951982393744523 11781192419927973590616785)
                  ·
                    refine ⟨8835894314945980192962589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11781192419927973590616785 8835894314945980192962589)
                    ·
                      refine ⟨3313460368104742572360971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8835894314945980192962589 3313460368104742572360971)
                      ·
                        rfl

theorem cell23_6452941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_6452941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452941 prefixEnd_6452941 := by exact prefixLift 6452941
  have htrace : WordTrace (prefixWord ++ tailWord_6452941) baseStart_6452941 baseEnd_6452941 := by
    simpa [prefixWord, tailWord_6452941, baseEnd_6452941] using wordTrace_append hprefix tailTrace_6452941
  have hstable : (prefixWord ++ tailWord_6452941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452941).length < 2 ^ (prefixWord ++ tailWord_6452941).sum := by decide
  have hdescent : baseEnd_6452941 < baseStart_6452941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452943 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 4]
def baseStart_6452943 : Nat := 118140960795 + 6452943 * 2 ^ 59
def prefixEnd_6452943 : Nat := 4983230072969 + 3 ^ 40 * 6452943 * 2
def baseEnd_6452943 : Nat := 3313461395066051564535961

theorem tailTrace_6452943 : CollatzResearch.WordTrace tailWord_6452943 prefixEnd_6452943 3313461395066051564535961 := by
  unfold tailWord_6452943
  simp only [CollatzResearch.WordTrace]
  refine ⟨235358166661097060768843483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156905444440731373845895655 235358166661097060768843483)
  ·
    refine ⟨353037249991645591153265225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235358166661097060768843483 353037249991645591153265225)
    ·
      refine ⟨264777937493734193364948919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353037249991645591153265225 264777937493734193364948919)
      ·
        refine ⟨397166906240601290047423379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264777937493734193364948919 397166906240601290047423379)
        ·
          refine ⟨595750359360901935071135069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397166906240601290047423379 595750359360901935071135069)
          ·
            refine ⟨223406384760338225651675651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 595750359360901935071135069 223406384760338225651675651)
            ·
              refine ⟨335109577140507338477513477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223406384760338225651675651 335109577140507338477513477)
              ·
                refine ⟨62833045713845125964533777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335109577140507338477513477 62833045713845125964533777)
                ·
                  refine ⟨47124784285383844473400333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62833045713845125964533777 47124784285383844473400333)
                  ·
                    refine ⟨17671794107018941677525125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47124784285383844473400333 17671794107018941677525125)
                    ·
                      refine ⟨3313461395066051564535961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17671794107018941677525125 3313461395066051564535961)
                      ·
                        rfl

theorem cell23_6452943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_6452943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452943 prefixEnd_6452943 := by exact prefixLift 6452943
  have htrace : WordTrace (prefixWord ++ tailWord_6452943) baseStart_6452943 baseEnd_6452943 := by
    simpa [prefixWord, tailWord_6452943, baseEnd_6452943] using wordTrace_append hprefix tailTrace_6452943
  have hstable : (prefixWord ++ tailWord_6452943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452943).length < 2 ^ (prefixWord ++ tailWord_6452943).sum := by decide
  have hdescent : baseEnd_6452943 < baseStart_6452943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6452994 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_6452994 : Nat := 118140960795 + 6452994 * 2 ^ 59
def prefixEnd_6452994 : Nat := 4983230072969 + 3 ^ 40 * 6452994 * 2
def baseEnd_6452994 : Nat := 3313487582579430864998227

theorem tailTrace_6452994 : CollatzResearch.WordTrace tailWord_6452994 prefixEnd_6452994 3313487582579430864998227 := by
  unfold tailWord_6452994
  simp only [CollatzResearch.WordTrace]
  refine ⟨58840006695978074119737509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156906684522608197652633357 58840006695978074119737509)
  ·
    refine ⟨11032501255495888897450783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58840006695978074119737509 11032501255495888897450783)
    ·
      refine ⟨16548751883243833346176175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11032501255495888897450783 16548751883243833346176175)
      ·
        refine ⟨24823127824865750019264263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16548751883243833346176175 24823127824865750019264263)
        ·
          refine ⟨37234691737298625028896395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24823127824865750019264263 37234691737298625028896395)
          ·
            refine ⟨55852037605947937543344593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37234691737298625028896395 55852037605947937543344593)
            ·
              refine ⟨41889028204460953157508445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55852037605947937543344593 41889028204460953157508445)
              ·
                refine ⟨15708385576672857434065667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41889028204460953157508445 15708385576672857434065667)
                ·
                  refine ⟨23562578365009286151098501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15708385576672857434065667 23562578365009286151098501)
                  ·
                    refine ⟨4417983443439241153330969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23562578365009286151098501 4417983443439241153330969)
                    ·
                      refine ⟨3313487582579430864998227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4417983443439241153330969 3313487582579430864998227)
                      ·
                        rfl

theorem cell23_6452994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_6452994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6452994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6452994 prefixEnd_6452994 := by exact prefixLift 6452994
  have htrace : WordTrace (prefixWord ++ tailWord_6452994) baseStart_6452994 baseEnd_6452994 := by
    simpa [prefixWord, tailWord_6452994, baseEnd_6452994] using wordTrace_append hprefix tailTrace_6452994
  have hstable : (prefixWord ++ tailWord_6452994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6452994).length < 2 ^ (prefixWord ++ tailWord_6452994).sum := by decide
  have hdescent : baseEnd_6452994 < baseStart_6452994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6452994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453033 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 8]
def baseStart_6453033 : Nat := 118140960795 + 6453033 * 2 ^ 59
def prefixEnd_6453033 : Nat := 4983230072969 + 3 ^ 40 * 6453033 * 2
def baseEnd_6453033 : Nat := 3313507608324956212410547

theorem tailTrace_6453033 : CollatzResearch.WordTrace tailWord_6453033 prefixEnd_6453033 3313507608324956212410547 := by
  unfold tailWord_6453033
  simp only [CollatzResearch.WordTrace]
  refine ⟨235361449230771006139619753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156907632820514004093079835 235361449230771006139619753)
  ·
    refine ⟨176521086923078254604714815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235361449230771006139619753 176521086923078254604714815)
    ·
      refine ⟨264781630384617381907072223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176521086923078254604714815 264781630384617381907072223)
      ·
        refine ⟨397172445576926072860608335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264781630384617381907072223 397172445576926072860608335)
        ·
          refine ⟨595758668365389109290912503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397172445576926072860608335 595758668365389109290912503)
          ·
            refine ⟨893638002548083663936368755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595758668365389109290912503 893638002548083663936368755)
            ·
              refine ⟨1340457003822125495904553133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893638002548083663936368755 1340457003822125495904553133)
              ·
                refine ⟨502671376433297060964207425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1340457003822125495904553133 502671376433297060964207425)
                ·
                  refine ⟨377003532324972795723155569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502671376433297060964207425 377003532324972795723155569)
                  ·
                    refine ⟨282752649243729596792366677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 377003532324972795723155569 282752649243729596792366677)
                    ·
                      refine ⟨3313507608324956212410547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 282752649243729596792366677 3313507608324956212410547)
                      ·
                        rfl

theorem cell23_6453033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_6453033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453033 prefixEnd_6453033 := by exact prefixLift 6453033
  have htrace : WordTrace (prefixWord ++ tailWord_6453033) baseStart_6453033 baseEnd_6453033 := by
    simpa [prefixWord, tailWord_6453033, baseEnd_6453033] using wordTrace_append hprefix tailTrace_6453033
  have hstable : (prefixWord ++ tailWord_6453033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453033).length < 2 ^ (prefixWord ++ tailWord_6453033).sum := by decide
  have hdescent : baseEnd_6453033 < baseStart_6453033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453044 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_6453044 : Nat := 118140960795 + 6453044 * 2 ^ 59
def prefixEnd_6453044 : Nat := 4983230072969 + 3 ^ 40 * 6453044 * 2
def baseEnd_6453044 : Nat := 3313513256612155669372997

theorem tailTrace_6453044 : CollatzResearch.WordTrace tailWord_6453044 prefixEnd_6453044 3313513256612155669372997 := by
  unfold tailWord_6453044
  simp only [CollatzResearch.WordTrace]
  refine ⟨117680925216865577509135093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156907900289154103345513457 117680925216865577509135093)
  ·
    refine ⟨11032586739081147891481415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117680925216865577509135093 11032586739081147891481415)
    ·
      refine ⟨16548880108621721837222123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11032586739081147891481415 16548880108621721837222123)
      ·
        refine ⟨24823320162932582755833185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16548880108621721837222123 24823320162932582755833185)
        ·
          refine ⟨18617490122199437066874889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24823320162932582755833185 18617490122199437066874889)
          ·
            refine ⟨13963117591649577800156167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18617490122199437066874889 13963117591649577800156167)
            ·
              refine ⟨20944676387474366700234251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13963117591649577800156167 20944676387474366700234251)
              ·
                refine ⟨31417014581211550050351377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20944676387474366700234251 31417014581211550050351377)
                ·
                  refine ⟨23562760935908662537763533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31417014581211550050351377 23562760935908662537763533)
                  ·
                    refine ⟨8836035350965748451661325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23562760935908662537763533 8836035350965748451661325)
                    ·
                      refine ⟨3313513256612155669372997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8836035350965748451661325 3313513256612155669372997)
                      ·
                        rfl

theorem cell23_6453044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_6453044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453044 prefixEnd_6453044 := by exact prefixLift 6453044
  have htrace : WordTrace (prefixWord ++ tailWord_6453044) baseStart_6453044 baseEnd_6453044 := by
    simpa [prefixWord, tailWord_6453044, baseEnd_6453044] using wordTrace_append hprefix tailTrace_6453044
  have hstable : (prefixWord ++ tailWord_6453044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453044).length < 2 ^ (prefixWord ++ tailWord_6453044).sum := by decide
  have hdescent : baseEnd_6453044 < baseStart_6453044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453128 : List Nat := [2, 1, 3, 3, 3, 2, 1, 3, 1, 4]
def baseStart_6453128 : Nat := 118140960795 + 6453128 * 2 ^ 59
def prefixEnd_6453128 : Nat := 4983230072969 + 3 ^ 40 * 6453128 * 2
def baseEnd_6453128 : Nat := 1104518796329044446907537

theorem tailTrace_6453128 : CollatzResearch.WordTrace tailWord_6453128 prefixEnd_6453128 1104518796329044446907537 := by
  unfold tailWord_6453128
  simp only [CollatzResearch.WordTrace]
  refine ⟨117682457082713418682164019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156909942776951224909552025 117682457082713418682164019)
  ·
    refine ⟨176523685624070128023246029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117682457082713418682164019 176523685624070128023246029)
    ·
      refine ⟨66196382109026298008717261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176523685624070128023246029 66196382109026298008717261)
      ·
        refine ⟨24823643290884861753268973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66196382109026298008717261 24823643290884861753268973)
        ·
          refine ⟨9308866234081823157475865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24823643290884861753268973 9308866234081823157475865)
          ·
            refine ⟨6981649675561367368106899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9308866234081823157475865 6981649675561367368106899)
            ·
              refine ⟨10472474513342051052160349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6981649675561367368106899 10472474513342051052160349)
              ·
                refine ⟨3927177942503269144560131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10472474513342051052160349 3927177942503269144560131)
                ·
                  refine ⟨5890766913754903716840197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3927177942503269144560131 5890766913754903716840197)
                  ·
                    refine ⟨1104518796329044446907537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5890766913754903716840197 1104518796329044446907537)
                    ·
                      rfl

theorem cell23_6453128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_6453128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453128 prefixEnd_6453128 := by exact prefixLift 6453128
  have htrace : WordTrace (prefixWord ++ tailWord_6453128) baseStart_6453128 baseEnd_6453128 := by
    simpa [prefixWord, tailWord_6453128, baseEnd_6453128] using wordTrace_append hprefix tailTrace_6453128
  have hstable : (prefixWord ++ tailWord_6453128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453128).length < 2 ^ (prefixWord ++ tailWord_6453128).sum := by decide
  have hdescent : baseEnd_6453128 < baseStart_6453128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453137 : List Nat := [1, 2, 2, 1, 1, 1, 6, 3, 1, 5]
def baseStart_6453137 : Nat := 118140960795 + 6453137 * 2 ^ 59
def prefixEnd_6453137 : Nat := 4983230072969 + 3 ^ 40 * 6453137 * 2
def baseEnd_6453137 : Nat := 1104520336771007935170023

theorem tailTrace_6453137 : CollatzResearch.WordTrace tailWord_6453137 prefixEnd_6453137 1104520336771007935170023 := by
  unfold tailWord_6453137
  simp only [CollatzResearch.WordTrace]
  refine ⟨235365242422394231901405665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156910161614929487934270443 235365242422394231901405665)
  ·
    refine ⟨176523931816795673926054249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235365242422394231901405665 176523931816795673926054249)
    ·
      refine ⟨132392948862596755444540687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176523931816795673926054249 132392948862596755444540687)
      ·
        refine ⟨198589423293895133166811031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132392948862596755444540687 198589423293895133166811031)
        ·
          refine ⟨297884134940842699750216547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198589423293895133166811031 297884134940842699750216547)
          ·
            refine ⟨446826202411264049625324821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297884134940842699750216547 446826202411264049625324821)
            ·
              refine ⟨20944978238028002326187101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 446826202411264049625324821 20944978238028002326187101)
              ·
                refine ⟨7854366839260500872320163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20944978238028002326187101 7854366839260500872320163)
                ·
                  refine ⟨11781550258890751308480245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7854366839260500872320163 11781550258890751308480245)
                  ·
                    refine ⟨1104520336771007935170023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11781550258890751308480245 1104520336771007935170023)
                    ·
                      rfl

theorem cell23_6453137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_6453137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453137 prefixEnd_6453137 := by exact prefixLift 6453137
  have htrace : WordTrace (prefixWord ++ tailWord_6453137) baseStart_6453137 baseEnd_6453137 := by
    simpa [prefixWord, tailWord_6453137, baseEnd_6453137] using wordTrace_append hprefix tailTrace_6453137
  have hstable : (prefixWord ++ tailWord_6453137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453137).length < 2 ^ (prefixWord ++ tailWord_6453137).sum := by decide
  have hdescent : baseEnd_6453137 < baseStart_6453137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453194 : List Nat := [3, 1, 2, 1, 2, 1, 2, 5, 1, 2, 3]
def baseStart_6453194 : Nat := 118140960795 + 6453194 * 2 ^ 59
def prefixEnd_6453194 : Nat := 4983230072969 + 3 ^ 40 * 6453194 * 2
def baseEnd_6453194 : Nat := 3313590278710330082497307

theorem tailTrace_6453194 : CollatzResearch.WordTrace tailWord_6453194 prefixEnd_6453194 3313590278710330082497307 := by
  unfold tailWord_6453194
  simp only [CollatzResearch.WordTrace]
  refine ⟨58841830345796932659057659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156911547588791820424153757 58841830345796932659057659)
  ·
    refine ⟨88262745518695398988586489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58841830345796932659057659 88262745518695398988586489)
    ·
      refine ⟨66197059139021549241439867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88262745518695398988586489 66197059139021549241439867)
      ·
        refine ⟨99295588708532323862159801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66197059139021549241439867 99295588708532323862159801)
        ·
          refine ⟨74471691531399242896619851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99295588708532323862159801 74471691531399242896619851)
          ·
            refine ⟨111707537297098864344929777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74471691531399242896619851 111707537297098864344929777)
            ·
              refine ⟨83780652972824148258697333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111707537297098864344929777 83780652972824148258697333)
              ·
                refine ⟨7854436216202263899252875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83780652972824148258697333 7854436216202263899252875)
                ·
                  refine ⟨11781654324303395848879313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7854436216202263899252875 11781654324303395848879313)
                  ·
                    refine ⟨8836240743227546886659485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11781654324303395848879313 8836240743227546886659485)
                    ·
                      refine ⟨3313590278710330082497307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8836240743227546886659485 3313590278710330082497307)
                      ·
                        rfl

theorem cell23_6453194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_6453194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453194 prefixEnd_6453194 := by exact prefixLift 6453194
  have htrace : WordTrace (prefixWord ++ tailWord_6453194) baseStart_6453194 baseEnd_6453194 := by
    simpa [prefixWord, tailWord_6453194, baseEnd_6453194] using wordTrace_append hprefix tailTrace_6453194
  have hstable : (prefixWord ++ tailWord_6453194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453194).length < 2 ^ (prefixWord ++ tailWord_6453194).sum := by decide
  have hdescent : baseEnd_6453194 < baseStart_6453194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453202 : List Nat := [3, 2, 2, 3, 2, 2, 2, 2, 1, 1, 3]
def baseStart_6453202 : Nat := 118140960795 + 6453202 * 2 ^ 59
def prefixEnd_6453202 : Nat := 4983230072969 + 3 ^ 40 * 6453202 * 2
def baseEnd_6453202 : Nat := 3313594386555566051197271

theorem tailTrace_6453202 : CollatzResearch.WordTrace tailWord_6453202 prefixEnd_6453202 3313594386555566051197271 := by
  unfold tailWord_6453202
  simp only [CollatzResearch.WordTrace]
  refine ⟨58841903291789687000630465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156911742111439165335014573 58841903291789687000630465)
  ·
    refine ⟨44131427468842265250472849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58841903291789687000630465 44131427468842265250472849)
    ·
      refine ⟨33098570601631698937854637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44131427468842265250472849 33098570601631698937854637)
      ·
        refine ⟨12411963975611887101695489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33098570601631698937854637 12411963975611887101695489)
        ·
          refine ⟨9308972981708915326271617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12411963975611887101695489 9308972981708915326271617)
          ·
            refine ⟨6981729736281686494703713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9308972981708915326271617 6981729736281686494703713)
            ·
              refine ⟨5236297302211264871027785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6981729736281686494703713 5236297302211264871027785)
              ·
                refine ⟨3927222976658448653270839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5236297302211264871027785 3927222976658448653270839)
                ·
                  refine ⟨5890834464987672979906259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3927222976658448653270839 5890834464987672979906259)
                  ·
                    refine ⟨8836251697481509469859389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5890834464987672979906259 8836251697481509469859389)
                    ·
                      refine ⟨3313594386555566051197271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8836251697481509469859389 3313594386555566051197271)
                      ·
                        rfl

theorem cell23_6453202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_6453202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453202 prefixEnd_6453202 := by exact prefixLift 6453202
  have htrace : WordTrace (prefixWord ++ tailWord_6453202) baseStart_6453202 baseEnd_6453202 := by
    simpa [prefixWord, tailWord_6453202, baseEnd_6453202] using wordTrace_append hprefix tailTrace_6453202
  have hstable : (prefixWord ++ tailWord_6453202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453202).length < 2 ^ (prefixWord ++ tailWord_6453202).sum := by decide
  have hdescent : baseEnd_6453202 < baseStart_6453202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453207 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 3]
def baseStart_6453207 : Nat := 118140960795 + 6453207 * 2 ^ 59
def prefixEnd_6453207 : Nat := 4983230072969 + 3 ^ 40 * 6453207 * 2
def baseEnd_6453207 : Nat := 3313596953958838531634747

theorem tailTrace_6453207 : CollatzResearch.WordTrace tailWord_6453207 prefixEnd_6453207 3313596953958838531634747 := by
  unfold tailWord_6453207
  simp only [CollatzResearch.WordTrace]
  refine ⟨235367795532140633856453875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156911863688093755904302583 235367795532140633856453875)
  ·
    refine ⟨353051693298210950784680813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235367795532140633856453875 353051693298210950784680813)
    ·
      refine ⟨132394384986829106544255305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353051693298210950784680813 132394384986829106544255305)
      ·
        refine ⟨99295788740121829908191479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132394384986829106544255305 99295788740121829908191479)
        ·
          refine ⟨148943683110182744862287219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99295788740121829908191479 148943683110182744862287219)
          ·
            refine ⟨223415524665274117293430829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148943683110182744862287219 223415524665274117293430829)
            ·
              refine ⟨83780821749477793985036561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223415524665274117293430829 83780821749477793985036561)
              ·
                refine ⟨62835616312108345488777421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83780821749477793985036561 62835616312108345488777421)
                ·
                  refine ⟨23563356117040629558291533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62835616312108345488777421 23563356117040629558291533)
                  ·
                    refine ⟨8836258543890236084359325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23563356117040629558291533 8836258543890236084359325)
                    ·
                      refine ⟨3313596953958838531634747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8836258543890236084359325 3313596953958838531634747)
                      ·
                        rfl

theorem cell23_6453207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_6453207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453207 prefixEnd_6453207 := by exact prefixLift 6453207
  have htrace : WordTrace (prefixWord ++ tailWord_6453207) baseStart_6453207 baseEnd_6453207 := by
    simpa [prefixWord, tailWord_6453207, baseEnd_6453207] using wordTrace_append hprefix tailTrace_6453207
  have hstable : (prefixWord ++ tailWord_6453207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453207).length < 2 ^ (prefixWord ++ tailWord_6453207).sum := by decide
  have hdescent : baseEnd_6453207 < baseStart_6453207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453208 : List Nat := [2, 1, 2, 2, 2, 2, 3, 4, 1, 2, 2]
def baseStart_6453208 : Nat := 118140960795 + 6453208 * 2 ^ 59
def prefixEnd_6453208 : Nat := 4983230072969 + 3 ^ 40 * 6453208 * 2
def baseEnd_6453208 : Nat := 3313597467439493027722243

theorem tailTrace_6453208 : CollatzResearch.WordTrace tailWord_6453208 prefixEnd_6453208 3313597467439493027722243 := by
  unfold tailWord_6453208
  simp only [CollatzResearch.WordTrace]
  refine ⟨117683916002568505513620139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156911888003424674018160185 117683916002568505513620139)
  ·
    refine ⟨176525874003852758270430209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117683916002568505513620139 176525874003852758270430209)
    ·
      refine ⟨132394405502889568702822657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176525874003852758270430209 132394405502889568702822657)
      ·
        refine ⟨99295804127167176527116993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132394405502889568702822657 99295804127167176527116993)
        ·
          refine ⟨74471853095375382395337745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99295804127167176527116993 74471853095375382395337745)
          ·
            refine ⟨55853889821531536796503309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74471853095375382395337745 55853889821531536796503309)
            ·
              refine ⟨20945208683074326298688741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55853889821531536796503309 20945208683074326298688741)
              ·
                refine ⟨3927226628076436181004139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20945208683074326298688741 3927226628076436181004139)
                ·
                  refine ⟨5890839942114654271506209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3927226628076436181004139 5890839942114654271506209)
                  ·
                    refine ⟨4418129956585990703629657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5890839942114654271506209 4418129956585990703629657)
                    ·
                      refine ⟨3313597467439493027722243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4418129956585990703629657 3313597467439493027722243)
                      ·
                        rfl

theorem cell23_6453208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_6453208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453208 prefixEnd_6453208 := by exact prefixLift 6453208
  have htrace : WordTrace (prefixWord ++ tailWord_6453208) baseStart_6453208 baseEnd_6453208 := by
    simpa [prefixWord, tailWord_6453208, baseEnd_6453208] using wordTrace_append hprefix tailTrace_6453208
  have hstable : (prefixWord ++ tailWord_6453208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453208).length < 2 ^ (prefixWord ++ tailWord_6453208).sum := by decide
  have hdescent : baseEnd_6453208 < baseStart_6453208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453224 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_6453224 : Nat := 118140960795 + 6453224 * 2 ^ 59
def prefixEnd_6453224 : Nat := 4983230072969 + 3 ^ 40 * 6453224 * 2
def baseEnd_6453224 : Nat := 3313605683129964965122169

theorem tailTrace_6453224 : CollatzResearch.WordTrace tailWord_6453224 prefixEnd_6453224 3313605683129964965122169 := by
  unfold tailWord_6453224
  simp only [CollatzResearch.WordTrace]
  refine ⟨117684207786539522879911363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156912277048719363839881817 117684207786539522879911363)
  ·
    refine ⟨176526311679809284319867045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117684207786539522879911363 176526311679809284319867045)
    ·
      refine ⟨33098683439964240809975071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176526311679809284319867045 33098683439964240809975071)
      ·
        refine ⟨49648025159946361214962607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33098683439964240809975071 49648025159946361214962607)
        ·
          refine ⟨74472037739919541822443911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49648025159946361214962607 74472037739919541822443911)
          ·
            refine ⟨111708056609879312733665867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74472037739919541822443911 111708056609879312733665867)
            ·
              refine ⟨167562084914818969100498801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111708056609879312733665867 167562084914818969100498801)
              ·
                refine ⟨125671563686114226825374101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167562084914818969100498801 125671563686114226825374101)
                ·
                  refine ⟨5890854547786604382439411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125671563686114226825374101 5890854547786604382439411)
                  ·
                    refine ⟨8836281821679906573659117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5890854547786604382439411 8836281821679906573659117)
                    ·
                      refine ⟨3313605683129964965122169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8836281821679906573659117 3313605683129964965122169)
                      ·
                        rfl

theorem cell23_6453224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_6453224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453224 prefixEnd_6453224 := by exact prefixLift 6453224
  have htrace : WordTrace (prefixWord ++ tailWord_6453224) baseStart_6453224 baseEnd_6453224 := by
    simpa [prefixWord, tailWord_6453224, baseEnd_6453224] using wordTrace_append hprefix tailTrace_6453224
  have hstable : (prefixWord ++ tailWord_6453224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453224).length < 2 ^ (prefixWord ++ tailWord_6453224).sum := by decide
  have hdescent : baseEnd_6453224 < baseStart_6453224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453267 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 3]
def baseStart_6453267 : Nat := 118140960795 + 6453267 * 2 ^ 59
def prefixEnd_6453267 : Nat := 4983230072969 + 3 ^ 40 * 6453267 * 2
def baseEnd_6453267 : Nat := 3313627762798108296884471

theorem tailTrace_6453267 : CollatzResearch.WordTrace tailWord_6453267 prefixEnd_6453267 3313627762798108296884471 := by
  unfold tailWord_6453267
  simp only [CollatzResearch.WordTrace]
  refine ⟨235369983911923264103638055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156913322607948842735758703 235369983911923264103638055)
  ·
    refine ⟨353054975867884896155457083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235369983911923264103638055 353054975867884896155457083)
    ·
      refine ⟨529582463801827344233185625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353054975867884896155457083 529582463801827344233185625)
      ·
        refine ⟨397186847851370508174889219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529582463801827344233185625 397186847851370508174889219)
        ·
          refine ⟨595780271777055762262333829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397186847851370508174889219 595780271777055762262333829)
          ·
            refine ⟨111708800958197955424187593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 595780271777055762262333829 111708800958197955424187593)
            ·
              refine ⟨83781600718648466568140695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111708800958197955424187593 83781600718648466568140695)
              ·
                refine ⟨125672401077972699852211043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83781600718648466568140695 125672401077972699852211043)
                ·
                  refine ⟨188508601616959049778316565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125672401077972699852211043 188508601616959049778316565)
                  ·
                    refine ⟨8836340700794955458358589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 188508601616959049778316565 8836340700794955458358589)
                    ·
                      refine ⟨3313627762798108296884471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8836340700794955458358589 3313627762798108296884471)
                      ·
                        rfl

theorem cell23_6453267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 3].length) (baseStart_6453267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453267 prefixEnd_6453267 := by exact prefixLift 6453267
  have htrace : WordTrace (prefixWord ++ tailWord_6453267) baseStart_6453267 baseEnd_6453267 := by
    simpa [prefixWord, tailWord_6453267, baseEnd_6453267] using wordTrace_append hprefix tailTrace_6453267
  have hstable : (prefixWord ++ tailWord_6453267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453267).length < 2 ^ (prefixWord ++ tailWord_6453267).sum := by decide
  have hdescent : baseEnd_6453267 < baseStart_6453267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453321 : List Nat := [1, 2, 1, 1, 2, 2, 7, 2, 5]
def baseStart_6453321 : Nat := 118140960795 + 6453321 * 2 ^ 59
def prefixEnd_6453321 : Nat := 4983230072969 + 3 ^ 40 * 6453321 * 2
def baseEnd_6453321 : Nat := 368183943417050120623247

theorem tailTrace_6453321 : CollatzResearch.WordTrace tailWord_6453321 prefixEnd_6453321 368183943417050120623247 := by
  unfold tailWord_6453321
  simp only [CollatzResearch.WordTrace]
  refine ⟨235371953453727631326103817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156914635635818420884069211 235371953453727631326103817)
  ·
    refine ⟨176528965090295723494577863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235371953453727631326103817 176528965090295723494577863)
    ·
      refine ⟨264793447635443585241866795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176528965090295723494577863 264793447635443585241866795)
      ·
        refine ⟨397190171453165377862800193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264793447635443585241866795 397190171453165377862800193)
        ·
          refine ⟨297892628589874033397100145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397190171453165377862800193 297892628589874033397100145)
          ·
            refine ⟨223419471442405525047825109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297892628589874033397100145 223419471442405525047825109)
            ·
              refine ⟨5236393861931379493308401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 223419471442405525047825109 5236393861931379493308401)
              ·
                refine ⟨3927295396448534619981301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5236393861931379493308401 3927295396448534619981301)
                ·
                  refine ⟨368183943417050120623247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3927295396448534619981301 368183943417050120623247)
                  ·
                    rfl

theorem cell23_6453321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 5].length) (baseStart_6453321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453321 prefixEnd_6453321 := by exact prefixLift 6453321
  have htrace : WordTrace (prefixWord ++ tailWord_6453321) baseStart_6453321 baseEnd_6453321 := by
    simpa [prefixWord, tailWord_6453321, baseEnd_6453321] using wordTrace_append hprefix tailTrace_6453321
  have hstable : (prefixWord ++ tailWord_6453321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453321).length < 2 ^ (prefixWord ++ tailWord_6453321).sum := by decide
  have hdescent : baseEnd_6453321 < baseStart_6453321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453327 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 5]
def baseStart_6453327 : Nat := 118140960795 + 6453327 * 2 ^ 59
def prefixEnd_6453327 : Nat := 4983230072969 + 3 ^ 40 * 6453327 * 2
def baseEnd_6453327 : Nat := 3313658571637378062134195

theorem tailTrace_6453327 : CollatzResearch.WordTrace tailWord_6453327 prefixEnd_6453327 3313658571637378062134195 := by
  unfold tailWord_6453327
  simp only [CollatzResearch.WordTrace]
  refine ⟨235372172291705894350822235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156914781527803929567214823 235372172291705894350822235)
  ·
    refine ⟨353058258437558841526233353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235372172291705894350822235 353058258437558841526233353)
    ·
      refine ⟨264793693828169131144675015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353058258437558841526233353 264793693828169131144675015)
      ·
        refine ⟨397190540742253696717012523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264793693828169131144675015 397190540742253696717012523)
        ·
          refine ⟨595785811113380545075518785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397190540742253696717012523 595785811113380545075518785)
          ·
            refine ⟨446839358335035408806639089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595785811113380545075518785 446839358335035408806639089)
            ·
              refine ⟨335129518751276556604979317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446839358335035408806639089 335129518751276556604979317)
              ·
                refine ⟨31418392382932177181716811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 335129518751276556604979317 31418392382932177181716811)
                ·
                  refine ⟨47127588574398265772575217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31418392382932177181716811 47127588574398265772575217)
                  ·
                    refine ⟨35345691430798699329431413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47127588574398265772575217 35345691430798699329431413)
                    ·
                      refine ⟨3313658571637378062134195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35345691430798699329431413 3313658571637378062134195)
                      ·
                        rfl

theorem cell23_6453327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_6453327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453327 prefixEnd_6453327 := by exact prefixLift 6453327
  have htrace : WordTrace (prefixWord ++ tailWord_6453327) baseStart_6453327 baseEnd_6453327 := by
    simpa [prefixWord, tailWord_6453327, baseEnd_6453327] using wordTrace_append hprefix tailTrace_6453327
  have hstable : (prefixWord ++ tailWord_6453327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453327).length < 2 ^ (prefixWord ++ tailWord_6453327).sum := by decide
  have hdescent : baseEnd_6453327 < baseStart_6453327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453347 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 2, 8]
def baseStart_6453347 : Nat := 118140960795 + 6453347 * 2 ^ 59
def prefixEnd_6453347 : Nat := 4983230072969 + 3 ^ 40 * 6453347 * 2
def baseEnd_6453347 : Nat := 1104556280416822661294701

theorem tailTrace_6453347 : CollatzResearch.WordTrace tailWord_6453347 prefixEnd_6453347 1104556280416822661294701 := by
  unfold tailWord_6453347
  simp only [CollatzResearch.WordTrace]
  refine ⟨235372901751633437766550295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156915267834422291844366863 235372901751633437766550295)
  ·
    refine ⟨353059352627450156649825443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235372901751633437766550295 353059352627450156649825443)
    ·
      refine ⟨529589028941175234974738165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353059352627450156649825443 529589028941175234974738165)
      ·
        refine ⟨49648971463235178278881703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 529589028941175234974738165 49648971463235178278881703)
        ·
          refine ⟨74473457194852767418322555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49648971463235178278881703 74473457194852767418322555)
          ·
            refine ⟨111710185792279151127483833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74473457194852767418322555 111710185792279151127483833)
            ·
              refine ⟨83782639344209363345612875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111710185792279151127483833 83782639344209363345612875)
              ·
                refine ⟨125673959016314045018419313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83782639344209363345612875 125673959016314045018419313)
                ·
                  refine ⟨94255469262235533763814485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125673959016314045018419313 94255469262235533763814485)
                  ·
                    refine ⟨1104556280416822661294701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94255469262235533763814485 1104556280416822661294701)
                    ·
                      rfl

theorem cell23_6453347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 8].length) (baseStart_6453347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453347 prefixEnd_6453347 := by exact prefixLift 6453347
  have htrace : WordTrace (prefixWord ++ tailWord_6453347) baseStart_6453347 baseEnd_6453347 := by
    simpa [prefixWord, tailWord_6453347, baseEnd_6453347] using wordTrace_append hprefix tailTrace_6453347
  have hstable : (prefixWord ++ tailWord_6453347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453347).length < 2 ^ (prefixWord ++ tailWord_6453347).sum := by decide
  have hdescent : baseEnd_6453347 < baseStart_6453347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453408 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 3]
def baseStart_6453408 : Nat := 118140960795 + 6453408 * 2 ^ 59
def prefixEnd_6453408 : Nat := 4983230072969 + 3 ^ 40 * 6453408 * 2
def baseEnd_6453408 : Nat := 3313700163570392245221323

theorem tailTrace_6453408 : CollatzResearch.WordTrace tailWord_6453408 prefixEnd_6453408 3313700163570392245221323 := by
  unfold tailWord_6453408
  simp only [CollatzResearch.WordTrace]
  refine ⟨117687563302206222592260439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156916751069608296789680585 117687563302206222592260439)
  ·
    refine ⟨176531344953309333888390659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117687563302206222592260439 176531344953309333888390659)
    ·
      refine ⟨264797017429964000832585989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176531344953309333888390659 264797017429964000832585989)
      ·
        refine ⟨49649440768118250156109873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264797017429964000832585989 49649440768118250156109873)
        ·
          refine ⟨37237080576088687617082405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49649440768118250156109873 37237080576088687617082405)
          ·
            refine ⟨6981952608016628928202951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37237080576088687617082405 6981952608016628928202951)
            ·
              refine ⟨10472928912024943392304427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6981952608016628928202951 10472928912024943392304427)
              ·
                refine ⟨15709393368037415088456641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10472928912024943392304427 15709393368037415088456641)
                ·
                  refine ⟨11782045026028061316342481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15709393368037415088456641 11782045026028061316342481)
                  ·
                    refine ⟨8836533769521045987256861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11782045026028061316342481 8836533769521045987256861)
                    ·
                      refine ⟨3313700163570392245221323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8836533769521045987256861 3313700163570392245221323)
                      ·
                        rfl

theorem cell23_6453408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_6453408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453408 prefixEnd_6453408 := by exact prefixLift 6453408
  have htrace : WordTrace (prefixWord ++ tailWord_6453408) baseStart_6453408 baseEnd_6453408 := by
    simpa [prefixWord, tailWord_6453408, baseEnd_6453408] using wordTrace_append hprefix tailTrace_6453408
  have hstable : (prefixWord ++ tailWord_6453408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453408).length < 2 ^ (prefixWord ++ tailWord_6453408).sum := by decide
  have hdescent : baseEnd_6453408 < baseStart_6453408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
