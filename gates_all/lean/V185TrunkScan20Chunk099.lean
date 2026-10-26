import V185TrunkScan20Chunk098

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_601404 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_601404 : Nat := 118140960795 + 601404 * 2 ^ 59
def prefixEnd_601404 : Nat := 4983230072969 + 3 ^ 40 * 601404 * 2
def baseEnd_601404 : Nat := 274497172921484655808177

theorem tailTrace_601404 : CollatzResearch.WordTrace tailWord_601404 prefixEnd_601404 274497172921484655808177 := by
  unfold tailWord_601404
  simp only [CollatzResearch.WordTrace]
  refine ⟨10967502956611747235509633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14623337275482329647346177 10967502956611747235509633)
  ·
    refine ⟨8225627217458810426632225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10967502956611747235509633 8225627217458810426632225)
    ·
      refine ⟨6169220413094107819974169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8225627217458810426632225 6169220413094107819974169)
      ·
        refine ⟨4626915309820580864980627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6169220413094107819974169 4626915309820580864980627)
        ·
          refine ⟨6940372964730871297470941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4626915309820580864980627 6940372964730871297470941)
          ·
            refine ⟨2602639861774076736551603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6940372964730871297470941 2602639861774076736551603)
            ·
              refine ⟨3903959792661115104827405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2602639861774076736551603 3903959792661115104827405)
              ·
                refine ⟨1463984922247918164310277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3903959792661115104827405 1463984922247918164310277)
                ·
                  refine ⟨274497172921484655808177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1463984922247918164310277 274497172921484655808177)
                  ·
                    rfl

theorem cell20_601404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_601404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601404 prefixEnd_601404 := by exact prefixLift 601404
  have htrace : WordTrace (prefixWord ++ tailWord_601404) baseStart_601404 baseEnd_601404 := by
    simpa [prefixWord, tailWord_601404, baseEnd_601404] using wordTrace_append hprefix tailTrace_601404
  have hstable : (prefixWord ++ tailWord_601404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601404).length < 2 ^ (prefixWord ++ tailWord_601404).sum := by decide
  have hdescent : baseEnd_601404 < baseStart_601404 := by decide
  rcases family_descends (prefixWord ++ tailWord_601404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601430 : List Nat := [5, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_601430 : Nat := 118140960795 + 601430 * 2 ^ 59
def prefixEnd_601430 : Nat := 4983230072969 + 3 ^ 40 * 601430 * 2
def baseEnd_601430 : Nat := 274509040029944120941405

theorem tailTrace_601430 : CollatzResearch.WordTrace tailWord_601430 prefixEnd_601430 274509040029944120941405 := by
  unfold tailWord_601430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1370997138195581306966609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14623969474086200607643829 1370997138195581306966609)
  ·
    refine ⟨1028247853646685980224957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1370997138195581306966609 1028247853646685980224957)
    ·
      refine ⟨385592945117507242584359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1028247853646685980224957 385592945117507242584359)
      ·
        refine ⟨578389417676260863876539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385592945117507242584359 578389417676260863876539)
        ·
          refine ⟨867584126514391295814809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578389417676260863876539 867584126514391295814809)
          ·
            refine ⟨650688094885793471861107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 867584126514391295814809 650688094885793471861107)
            ·
              refine ⟨976032142328690207791661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650688094885793471861107 976032142328690207791661)
              ·
                refine ⟨366012053373258827921873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 976032142328690207791661 366012053373258827921873)
                ·
                  refine ⟨274509040029944120941405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366012053373258827921873 274509040029944120941405)
                  ·
                    rfl

theorem cell20_601430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_601430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601430 prefixEnd_601430 := by exact prefixLift 601430
  have htrace : WordTrace (prefixWord ++ tailWord_601430) baseStart_601430 baseEnd_601430 := by
    simpa [prefixWord, tailWord_601430, baseEnd_601430] using wordTrace_append hprefix tailTrace_601430
  have hstable : (prefixWord ++ tailWord_601430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601430).length < 2 ^ (prefixWord ++ tailWord_601430).sum := by decide
  have hdescent : baseEnd_601430 < baseStart_601430 := by decide
  rcases family_descends (prefixWord ++ tailWord_601430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601456 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_601456 : Nat := 118140960795 + 601456 * 2 ^ 59
def prefixEnd_601456 : Nat := 4983230072969 + 3 ^ 40 * 601456 * 2
def baseEnd_601456 : Nat := 274520907138403586074631

theorem tailTrace_601456 : CollatzResearch.WordTrace tailWord_601456 prefixEnd_601456 274520907138403586074631 := by
  unfold tailWord_601456
  simp only [CollatzResearch.WordTrace]
  refine ⟨10968451254517553675956111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14624601672690071567941481 10968451254517553675956111)
  ·
    refine ⟨16452676881776330513934167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10968451254517553675956111 16452676881776330513934167)
    ·
      refine ⟨24679015322664495770901251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16452676881776330513934167 24679015322664495770901251)
      ·
        refine ⟨37018522983996743656351877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24679015322664495770901251 37018522983996743656351877)
        ·
          refine ⟨6940973059499389435565977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37018522983996743656351877 6940973059499389435565977)
          ·
            refine ⟨5205729794624542076674483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6940973059499389435565977 5205729794624542076674483)
            ·
              refine ⟨7808594691936813115011725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5205729794624542076674483 7808594691936813115011725)
              ·
                refine ⟨2928223009476304918129397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7808594691936813115011725 2928223009476304918129397)
                ·
                  refine ⟨274520907138403586074631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2928223009476304918129397 274520907138403586074631)
                  ·
                    rfl

theorem cell20_601456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_601456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601456 prefixEnd_601456 := by exact prefixLift 601456
  have htrace : WordTrace (prefixWord ++ tailWord_601456) baseStart_601456 baseEnd_601456 := by
    simpa [prefixWord, tailWord_601456, baseEnd_601456] using wordTrace_append hprefix tailTrace_601456
  have hstable : (prefixWord ++ tailWord_601456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601456).length < 2 ^ (prefixWord ++ tailWord_601456).sum := by decide
  have hdescent : baseEnd_601456 < baseStart_601456 := by decide
  rcases family_descends (prefixWord ++ tailWord_601456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601539 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 6]
def baseStart_601539 : Nat := 118140960795 + 601539 * 2 ^ 59
def prefixEnd_601539 : Nat := 4983230072969 + 3 ^ 40 * 601539 * 2
def baseEnd_601539 : Nat := 274558790600024186307625

theorem tailTrace_601539 : CollatzResearch.WordTrace tailWord_601539 prefixEnd_601539 274558790600024186307625 := by
  unfold tailWord_601539
  simp only [CollatzResearch.WordTrace]
  refine ⟨21939929767734412527183671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14626619845156275018122447 21939929767734412527183671)
  ·
    refine ⟨32909894651601618790775507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21939929767734412527183671 32909894651601618790775507)
    ·
      refine ⟨49364841977402428186163261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32909894651601618790775507 49364841977402428186163261)
      ·
        refine ⟨18511815741525910569811223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49364841977402428186163261 18511815741525910569811223)
        ·
          refine ⟨27767723612288865854716835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18511815741525910569811223 27767723612288865854716835)
          ·
            refine ⟨41651585418433298782075253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27767723612288865854716835 41651585418433298782075253)
            ·
              refine ⟨3904836132978121760819555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41651585418433298782075253 3904836132978121760819555)
              ·
                refine ⟨5857254199467182641229333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3904836132978121760819555 5857254199467182641229333)
                ·
                  refine ⟨274558790600024186307625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5857254199467182641229333 274558790600024186307625)
                  ·
                    rfl

theorem cell20_601539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_601539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601539 prefixEnd_601539 := by exact prefixLift 601539
  have htrace : WordTrace (prefixWord ++ tailWord_601539) baseStart_601539 baseEnd_601539 := by
    simpa [prefixWord, tailWord_601539, baseEnd_601539] using wordTrace_append hprefix tailTrace_601539
  have hstable : (prefixWord ++ tailWord_601539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601539).length < 2 ^ (prefixWord ++ tailWord_601539).sum := by decide
  have hdescent : baseEnd_601539 < baseStart_601539 := by decide
  rcases family_descends (prefixWord ++ tailWord_601539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601573 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 4]
def baseStart_601573 : Nat := 118140960795 + 601573 * 2 ^ 59
def prefixEnd_601573 : Nat := 4983230072969 + 3 ^ 40 * 601573 * 2
def baseEnd_601573 : Nat := 274574309126471179174153

theorem tailTrace_601573 : CollatzResearch.WordTrace tailWord_601573 prefixEnd_601573 274574309126471179174153 := by
  unfold tailWord_601573
  simp only [CollatzResearch.WordTrace]
  refine ⟨21941169849611236333921373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14627446566407490889280915 21941169849611236333921373)
  ·
    refine ⟨8227938693604213625220515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21941169849611236333921373 8227938693604213625220515)
    ·
      refine ⟨12341908040406320437830773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8227938693604213625220515 12341908040406320437830773)
      ·
        refine ⟨1157053878788092541046635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12341908040406320437830773 1157053878788092541046635)
        ·
          refine ⟨1735580818182138811569953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1157053878788092541046635 1735580818182138811569953)
          ·
            refine ⟨1301685613636604108677465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1735580818182138811569953 1301685613636604108677465)
            ·
              refine ⟨976264210227453081508099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301685613636604108677465 976264210227453081508099)
              ·
                refine ⟨1464396315341179622262149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976264210227453081508099 1464396315341179622262149)
                ·
                  refine ⟨274574309126471179174153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1464396315341179622262149 274574309126471179174153)
                  ·
                    rfl

theorem cell20_601573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_601573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601573 prefixEnd_601573 := by exact prefixLift 601573
  have htrace : WordTrace (prefixWord ++ tailWord_601573) baseStart_601573 baseEnd_601573 := by
    simpa [prefixWord, tailWord_601573, baseEnd_601573] using wordTrace_append hprefix tailTrace_601573
  have hstable : (prefixWord ++ tailWord_601573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601573).length < 2 ^ (prefixWord ++ tailWord_601573).sum := by decide
  have hdescent : baseEnd_601573 < baseStart_601573 := by decide
  rcases family_descends (prefixWord ++ tailWord_601573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601608 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_601608 : Nat := 118140960795 + 601608 * 2 ^ 59
def prefixEnd_601608 : Nat := 4983230072969 + 3 ^ 40 * 601608 * 2
def baseEnd_601608 : Nat := 274590284080166613007343

theorem tailTrace_601608 : CollatzResearch.WordTrace tailWord_601608 prefixEnd_601608 274590284080166613007343 := by
  unfold tailWord_601608
  simp only [CollatzResearch.WordTrace]
  refine ⟨10971223202242218655722739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14628297602989624874296985 10971223202242218655722739)
  ·
    refine ⟨16456834803363327983584109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10971223202242218655722739 16456834803363327983584109)
    ·
      refine ⟨6171313051261247993844041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16456834803363327983584109 6171313051261247993844041)
      ·
        refine ⟨4628484788445935995383031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6171313051261247993844041 4628484788445935995383031)
        ·
          refine ⟨6942727182668903993074547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4628484788445935995383031 6942727182668903993074547)
          ·
            refine ⟨10414090774003355989611821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6942727182668903993074547 10414090774003355989611821)
            ·
              refine ⟨3905284040251258496104433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10414090774003355989611821 3905284040251258496104433)
              ·
                refine ⟨2928963030188443872078325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3905284040251258496104433 2928963030188443872078325)
                ·
                  refine ⟨274590284080166613007343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2928963030188443872078325 274590284080166613007343)
                  ·
                    rfl

theorem cell20_601608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_601608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601608 prefixEnd_601608 := by exact prefixLift 601608
  have htrace : WordTrace (prefixWord ++ tailWord_601608) baseStart_601608 baseEnd_601608 := by
    simpa [prefixWord, tailWord_601608, baseEnd_601608] using wordTrace_append hprefix tailTrace_601608
  have hstable : (prefixWord ++ tailWord_601608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601608).length < 2 ^ (prefixWord ++ tailWord_601608).sum := by decide
  have hdescent : baseEnd_601608 < baseStart_601608 := by decide
  rcases family_descends (prefixWord ++ tailWord_601608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601628 : List Nat := [2, 2, 3, 1, 2, 1, 5, 2, 2]
def baseStart_601628 : Nat := 118140960795 + 601628 * 2 ^ 59
def prefixEnd_601628 : Nat := 4983230072969 + 3 ^ 40 * 601628 * 2
def baseEnd_601628 : Nat := 274599412625135432340595

theorem tailTrace_601628 : CollatzResearch.WordTrace tailWord_601628 prefixEnd_601628 274599412625135432340595 := by
  unfold tailWord_601628
  simp only [CollatzResearch.WordTrace]
  refine ⟨10971587932205990363586769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14628783909607987151449025 10971587932205990363586769)
  ·
    refine ⟨8228690949154492772690077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10971587932205990363586769 8228690949154492772690077)
    ·
      refine ⟨3085759105932934789758779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8228690949154492772690077 3085759105932934789758779)
      ·
        refine ⟨4628638658899402184638169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3085759105932934789758779 4628638658899402184638169)
        ·
          refine ⟨3471478994174551638478627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4628638658899402184638169 3471478994174551638478627)
          ·
            refine ⟨5207218491261827457717941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3471478994174551638478627 5207218491261827457717941)
            ·
              refine ⟨488176733555796324161057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5207218491261827457717941 488176733555796324161057)
              ·
                refine ⟨366132550166847243120793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 488176733555796324161057 366132550166847243120793)
                ·
                  refine ⟨274599412625135432340595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366132550166847243120793 274599412625135432340595)
                  ·
                    rfl

theorem cell20_601628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_601628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601628 prefixEnd_601628 := by exact prefixLift 601628
  have htrace : WordTrace (prefixWord ++ tailWord_601628) baseStart_601628 baseEnd_601628 := by
    simpa [prefixWord, tailWord_601628, baseEnd_601628] using wordTrace_append hprefix tailTrace_601628
  have hstable : (prefixWord ++ tailWord_601628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601628).length < 2 ^ (prefixWord ++ tailWord_601628).sum := by decide
  have hdescent : baseEnd_601628 < baseStart_601628 := by decide
  rcases family_descends (prefixWord ++ tailWord_601628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601677 : List Nat := [1, 6, 1, 1, 11]
def baseStart_601677 : Nat := 118140960795 + 601677 * 2 ^ 59
def prefixEnd_601677 : Nat := 4983230072969 + 3 ^ 40 * 601677 * 2
def baseEnd_601677 : Nat := 3390392315559370860581

theorem tailTrace_601677 : CollatzResearch.WordTrace tailWord_601677 prefixEnd_601677 3390392315559370860581 := by
  unfold tailWord_601677
  simp only [CollatzResearch.WordTrace]
  refine ⟨21944963041234462095707285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14629975360822974730471523 21944963041234462095707285)
  ·
    refine ⟨1028670142557865410736279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21944963041234462095707285 1028670142557865410736279)
    ·
      refine ⟨1543005213836798116104419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1028670142557865410736279 1543005213836798116104419)
      ·
        refine ⟨2314507820755197174156629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1543005213836798116104419 2314507820755197174156629)
        ·
          refine ⟨3390392315559370860581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2314507820755197174156629 3390392315559370860581)
          ·
            rfl

theorem cell20_601677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 11].length) (baseStart_601677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601677 prefixEnd_601677 := by exact prefixLift 601677
  have htrace : WordTrace (prefixWord ++ tailWord_601677) baseStart_601677 baseEnd_601677 := by
    simpa [prefixWord, tailWord_601677, baseEnd_601677] using wordTrace_append hprefix tailTrace_601677
  have hstable : (prefixWord ++ tailWord_601677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601677).length < 2 ^ (prefixWord ++ tailWord_601677).sum := by decide
  have hdescent : baseEnd_601677 < baseStart_601677 := by decide
  rcases family_descends (prefixWord ++ tailWord_601677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601687 : List Nat := [1, 1, 3, 2, 2, 4, 1, 4, 2]
def baseStart_601687 : Nat := 118140960795 + 601687 * 2 ^ 59
def prefixEnd_601687 : Nat := 4983230072969 + 3 ^ 40 * 601687 * 2
def baseEnd_601687 : Nat := 274626341832793449373687

theorem tailTrace_601687 : CollatzResearch.WordTrace tailWord_601687 prefixEnd_601687 274626341832793449373687 := by
  unfold tailWord_601687
  simp only [CollatzResearch.WordTrace]
  refine ⟨21945327771198233803571315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14630218514132155869047543 21945327771198233803571315)
  ·
    refine ⟨32917991656797350705356973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21945327771198233803571315 32917991656797350705356973)
    ·
      refine ⟨12344246871299006514508865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32917991656797350705356973 12344246871299006514508865)
      ·
        refine ⟨9258185153474254885881649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12344246871299006514508865 9258185153474254885881649)
        ·
          refine ⟨6943638865105691164411237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9258185153474254885881649 6943638865105691164411237)
          ·
            refine ⟨1301932287207317093327107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6943638865105691164411237 1301932287207317093327107)
            ·
              refine ⟨1952898430810975639990661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301932287207317093327107 1952898430810975639990661)
              ·
                refine ⟨366168455777057932498249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1952898430810975639990661 366168455777057932498249)
                ·
                  refine ⟨274626341832793449373687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366168455777057932498249 274626341832793449373687)
                  ·
                    rfl

theorem cell20_601687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 2].length) (baseStart_601687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601687 prefixEnd_601687 := by exact prefixLift 601687
  have htrace : WordTrace (prefixWord ++ tailWord_601687) baseStart_601687 baseEnd_601687 := by
    simpa [prefixWord, tailWord_601687, baseEnd_601687] using wordTrace_append hprefix tailTrace_601687
  have hstable : (prefixWord ++ tailWord_601687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601687).length < 2 ^ (prefixWord ++ tailWord_601687).sum := by decide
  have hdescent : baseEnd_601687 < baseStart_601687 := by decide
  rcases family_descends (prefixWord ++ tailWord_601687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601701 : List Nat := [1, 3, 1, 3, 3, 1, 2, 3, 3]
def baseStart_601701 : Nat := 118140960795 + 601701 * 2 ^ 59
def prefixEnd_601701 : Nat := 4983230072969 + 3 ^ 40 * 601701 * 2
def baseEnd_601701 : Nat := 274632731814271622906963

theorem tailTrace_601701 : CollatzResearch.WordTrace tailWord_601701 prefixEnd_601701 274632731814271622906963 := by
  unfold tailWord_601701
  simp only [CollatzResearch.WordTrace]
  refine ⟨21945838393147514194580957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14630558928765009463053971 21945838393147514194580957)
  ·
    refine ⟨8229689397430317822967859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21945838393147514194580957 8229689397430317822967859)
    ·
      refine ⟨12344534096145476734451789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8229689397430317822967859 12344534096145476734451789)
      ·
        refine ⟨4629200286054553775419421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12344534096145476734451789 4629200286054553775419421)
        ·
          refine ⟨1735950107270457665782283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4629200286054553775419421 1735950107270457665782283)
          ·
            refine ⟨2603925160905686498673425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1735950107270457665782283 2603925160905686498673425)
            ·
              refine ⟨1952943870679264874005069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2603925160905686498673425 1952943870679264874005069)
              ·
                refine ⟨732353951504724327751901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1952943870679264874005069 732353951504724327751901)
                ·
                  refine ⟨274632731814271622906963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732353951504724327751901 274632731814271622906963)
                  ·
                    rfl

theorem cell20_601701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_601701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601701 prefixEnd_601701 := by exact prefixLift 601701
  have htrace : WordTrace (prefixWord ++ tailWord_601701) baseStart_601701 baseEnd_601701 := by
    simpa [prefixWord, tailWord_601701, baseEnd_601701] using wordTrace_append hprefix tailTrace_601701
  have hstable : (prefixWord ++ tailWord_601701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601701).length < 2 ^ (prefixWord ++ tailWord_601701).sum := by decide
  have hdescent : baseEnd_601701 < baseStart_601701 := by decide
  rcases family_descends (prefixWord ++ tailWord_601701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601725 : List Nat := [1, 4, 1, 1, 4, 1, 1, 5, 2]
def baseStart_601725 : Nat := 118140960795 + 601725 * 2 ^ 59
def prefixEnd_601725 : Nat := 4983230072969 + 3 ^ 40 * 601725 * 2
def baseEnd_601725 : Nat := 274643686068234206106865

theorem tailTrace_601725 : CollatzResearch.WordTrace tailWord_601725 prefixEnd_601725 274643686068234206106865 := by
  unfold tailWord_601725
  simp only [CollatzResearch.WordTrace]
  refine ⟨21946713745060566293454629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14631142496707044195636419 21946713745060566293454629)
  ·
    refine ⟨4115008827198856180022743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21946713745060566293454629 4115008827198856180022743)
    ·
      refine ⟨6172513240798284270034115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4115008827198856180022743 6172513240798284270034115)
      ·
        refine ⟨9258769861197426405051173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6172513240798284270034115 9258769861197426405051173)
        ·
          refine ⟨1736019348974517450947095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9258769861197426405051173 1736019348974517450947095)
          ·
            refine ⟨2604029023461776176420643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1736019348974517450947095 2604029023461776176420643)
            ·
              refine ⟨3906043535192664264630965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2604029023461776176420643 3906043535192664264630965)
              ·
                refine ⟨366191581424312274809153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3906043535192664264630965 366191581424312274809153)
                ·
                  refine ⟨274643686068234206106865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366191581424312274809153 274643686068234206106865)
                  ·
                    rfl

theorem cell20_601725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_601725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601725 prefixEnd_601725 := by exact prefixLift 601725
  have htrace : WordTrace (prefixWord ++ tailWord_601725) baseStart_601725 baseEnd_601725 := by
    simpa [prefixWord, tailWord_601725, baseEnd_601725] using wordTrace_append hprefix tailTrace_601725
  have hstable : (prefixWord ++ tailWord_601725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601725).length < 2 ^ (prefixWord ++ tailWord_601725).sum := by decide
  have hdescent : baseEnd_601725 < baseStart_601725 := by decide
  rcases family_descends (prefixWord ++ tailWord_601725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601863 : List Nat := [1, 1, 4, 4, 3, 1, 1, 5]
def baseStart_601863 : Nat := 118140960795 + 601863 * 2 ^ 59
def prefixEnd_601863 : Nat := 4983230072969 + 3 ^ 40 * 601863 * 2
def baseEnd_601863 : Nat := 91568891009506353168767

theorem tailTrace_601863 : CollatzResearch.WordTrace tailWord_601863 prefixEnd_601863 91568891009506353168767 := by
  unfold tailWord_601863
  simp only [CollatzResearch.WordTrace]
  refine ⟨21951747018560615861978243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14634498012373743907985495 21951747018560615861978243)
  ·
    refine ⟨32927620527840923792967365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21951747018560615861978243 32927620527840923792967365)
    ·
      refine ⟨6173928848970173211181381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32927620527840923792967365 6173928848970173211181381)
      ·
        refine ⟨1157611659181907477096509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6173928848970173211181381 1157611659181907477096509)
        ·
          refine ⟨434104372193215303911191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1157611659181907477096509 434104372193215303911191)
          ·
            refine ⟨651156558289822955866787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434104372193215303911191 651156558289822955866787)
            ·
              refine ⟨976734837434734433800181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651156558289822955866787 976734837434734433800181)
              ·
                refine ⟨91568891009506353168767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 976734837434734433800181 91568891009506353168767)
                ·
                  rfl

theorem cell20_601863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 5].length) (baseStart_601863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601863 prefixEnd_601863 := by exact prefixLift 601863
  have htrace : WordTrace (prefixWord ++ tailWord_601863) baseStart_601863 baseEnd_601863 := by
    simpa [prefixWord, tailWord_601863, baseEnd_601863] using wordTrace_append hprefix tailTrace_601863
  have hstable : (prefixWord ++ tailWord_601863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601863).length < 2 ^ (prefixWord ++ tailWord_601863).sum := by decide
  have hdescent : baseEnd_601863 < baseStart_601863 := by decide
  rcases family_descends (prefixWord ++ tailWord_601863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601908 : List Nat := [2, 5, 1, 1, 2, 1, 3, 2, 3]
def baseStart_601908 : Nat := 118140960795 + 601908 * 2 ^ 59
def prefixEnd_601908 : Nat := 4983230072969 + 3 ^ 40 * 601908 * 2
def baseEnd_601908 : Nat := 274727212254698903006117

theorem tailTrace_601908 : CollatzResearch.WordTrace tailWord_601908 prefixEnd_601908 274727212254698903006117 := by
  unfold tailWord_601908
  simp only [CollatzResearch.WordTrace]
  refine ⟨10976694151698794273683189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14635592202265059031577585 10976694151698794273683189)
  ·
    refine ⟨1029065076721761963157799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10976694151698794273683189 1029065076721761963157799)
    ·
      refine ⟨1543597615082642944736699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1029065076721761963157799 1543597615082642944736699)
      ·
        refine ⟨2315396422623964417105049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1543597615082642944736699 2315396422623964417105049)
        ·
          refine ⟨1736547316967973312828787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2315396422623964417105049 1736547316967973312828787)
          ·
            refine ⟨2604820975451959969243181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1736547316967973312828787 2604820975451959969243181)
            ·
              refine ⟨976807865794484988466193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2604820975451959969243181 976807865794484988466193)
              ·
                refine ⟨732605899345863741349645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976807865794484988466193 732605899345863741349645)
                ·
                  refine ⟨274727212254698903006117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732605899345863741349645 274727212254698903006117)
                  ·
                    rfl

theorem cell20_601908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_601908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601908 prefixEnd_601908 := by exact prefixLift 601908
  have htrace : WordTrace (prefixWord ++ tailWord_601908) baseStart_601908 baseEnd_601908 := by
    simpa [prefixWord, tailWord_601908, baseEnd_601908] using wordTrace_append hprefix tailTrace_601908
  have hstable : (prefixWord ++ tailWord_601908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601908).length < 2 ^ (prefixWord ++ tailWord_601908).sum := by decide
  have hdescent : baseEnd_601908 < baseStart_601908 := by decide
  rcases family_descends (prefixWord ++ tailWord_601908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601912 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 5]
def baseStart_601912 : Nat := 118140960795 + 601912 * 2 ^ 59
def prefixEnd_601912 : Nat := 4983230072969 + 3 ^ 40 * 601912 * 2
def baseEnd_601912 : Nat := 274729037963692666872767

theorem tailTrace_601912 : CollatzResearch.WordTrace tailWord_601912 prefixEnd_601912 274729037963692666872767 := by
  unfold tailWord_601912
  simp only [CollatzResearch.WordTrace]
  refine ⟨10976767097691548615255995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14635689463588731487007993 10976767097691548615255995)
  ·
    refine ⟨16465150646537322922883993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10976767097691548615255995 16465150646537322922883993)
    ·
      refine ⟨12348862984902992192162995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16465150646537322922883993 12348862984902992192162995)
      ·
        refine ⟨18523294477354488288244493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12348862984902992192162995 18523294477354488288244493)
        ·
          refine ⟨6946235429007933108091685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18523294477354488288244493 6946235429007933108091685)
          ·
            refine ⟨1302419142938987457767191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6946235429007933108091685 1302419142938987457767191)
            ·
              refine ⟨1953628714408481186650787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1302419142938987457767191 1953628714408481186650787)
              ·
                refine ⟨2930443071612721779976181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1953628714408481186650787 2930443071612721779976181)
                ·
                  refine ⟨274729037963692666872767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2930443071612721779976181 274729037963692666872767)
                  ·
                    rfl

theorem cell20_601912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_601912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601912 prefixEnd_601912 := by exact prefixLift 601912
  have htrace : WordTrace (prefixWord ++ tailWord_601912) baseStart_601912 baseEnd_601912 := by
    simpa [prefixWord, tailWord_601912, baseEnd_601912] using wordTrace_append hprefix tailTrace_601912
  have hstable : (prefixWord ++ tailWord_601912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601912).length < 2 ^ (prefixWord ++ tailWord_601912).sum := by decide
  have hdescent : baseEnd_601912 < baseStart_601912 := by decide
  rcases family_descends (prefixWord ++ tailWord_601912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601929 : List Nat := [1, 2, 1, 1, 2, 4, 5, 1, 3]
def baseStart_601929 : Nat := 118140960795 + 601929 * 2 ^ 59
def prefixEnd_601929 : Nat := 4983230072969 + 3 ^ 40 * 601929 * 2
def baseEnd_601929 : Nat := 274736797226916163306031

theorem tailTrace_601929 : CollatzResearch.WordTrace tailWord_601929 prefixEnd_601929 274736797226916163306031 := by
  unfold tailWord_601929
  simp only [CollatzResearch.WordTrace]
  refine ⟨21954154236321509133880841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14636102824214339422587227 21954154236321509133880841)
  ·
    refine ⟨16465615677241131850410631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21954154236321509133880841 16465615677241131850410631)
    ·
      refine ⟨24698423515861697775615947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16465615677241131850410631 24698423515861697775615947)
      ·
        refine ⟨37047635273792546663423921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24698423515861697775615947 37047635273792546663423921)
        ·
          refine ⟨27785726455344409997567941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37047635273792546663423921 27785726455344409997567941)
          ·
            refine ⟨5209823710377076874543989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27785726455344409997567941 5209823710377076874543989)
            ·
              refine ⟨488420972847850956988499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5209823710377076874543989 488420972847850956988499)
              ·
                refine ⟨732631459271776435482749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488420972847850956988499 732631459271776435482749)
                ·
                  refine ⟨274736797226916163306031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732631459271776435482749 274736797226916163306031)
                  ·
                    rfl

theorem cell20_601929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_601929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601929 prefixEnd_601929 := by exact prefixLift 601929
  have htrace : WordTrace (prefixWord ++ tailWord_601929) baseStart_601929 baseEnd_601929 := by
    simpa [prefixWord, tailWord_601929, baseEnd_601929] using wordTrace_append hprefix tailTrace_601929
  have hstable : (prefixWord ++ tailWord_601929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601929).length < 2 ^ (prefixWord ++ tailWord_601929).sum := by decide
  have hdescent : baseEnd_601929 < baseStart_601929 := by decide
  rcases family_descends (prefixWord ++ tailWord_601929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601943 : List Nat := [1, 1, 3, 2, 5, 1, 1, 6]
def baseStart_601943 : Nat := 118140960795 + 601943 * 2 ^ 59
def prefixEnd_601943 : Nat := 4983230072969 + 3 ^ 40 * 601943 * 2
def baseEnd_601943 : Nat := 91581062402798112279769

theorem tailTrace_601943 : CollatzResearch.WordTrace tailWord_601943 prefixEnd_601943 91581062402798112279769 := by
  unfold tailWord_601943
  simp only [CollatzResearch.WordTrace]
  refine ⟨21954664858270789524890483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14636443238847193016593655 21954664858270789524890483)
  ·
    refine ⟨32931997287406184287335725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21954664858270789524890483 32931997287406184287335725)
    ·
      refine ⟨12349498982777319107750897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32931997287406184287335725 12349498982777319107750897)
      ·
        refine ⟨9262124237082989330813173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12349498982777319107750897 9262124237082989330813173)
        ·
          refine ⟨868324147226530249763735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9262124237082989330813173 868324147226530249763735)
          ·
            refine ⟨1302486220839795374645603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868324147226530249763735 1302486220839795374645603)
            ·
              refine ⟨1953729331259693061968405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1302486220839795374645603 1953729331259693061968405)
              ·
                refine ⟨91581062402798112279769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1953729331259693061968405 91581062402798112279769)
                ·
                  rfl

theorem cell20_601943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 6].length) (baseStart_601943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601943 prefixEnd_601943 := by exact prefixLift 601943
  have htrace : WordTrace (prefixWord ++ tailWord_601943) baseStart_601943 baseEnd_601943 := by
    simpa [prefixWord, tailWord_601943, baseEnd_601943] using wordTrace_append hprefix tailTrace_601943
  have hstable : (prefixWord ++ tailWord_601943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601943).length < 2 ^ (prefixWord ++ tailWord_601943).sum := by decide
  have hdescent : baseEnd_601943 < baseStart_601943 := by decide
  rcases family_descends (prefixWord ++ tailWord_601943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601964 : List Nat := [2, 2, 1, 1, 4, 2, 8]
def baseStart_601964 : Nat := 118140960795 + 601964 * 2 ^ 59
def prefixEnd_601964 : Nat := 4983230072969 + 3 ^ 40 * 601964 * 2
def baseEnd_601964 : Nat := 30528085797845733015469

theorem tailTrace_601964 : CollatzResearch.WordTrace tailWord_601964 prefixEnd_601964 30528085797845733015469 := by
  unfold tailWord_601964
  simp only [CollatzResearch.WordTrace]
  refine ⟨10977715395597355055702473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14636953860796473407603297 10977715395597355055702473)
  ·
    refine ⟨8233286546698016291776855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10977715395597355055702473 8233286546698016291776855)
    ·
      refine ⟨12349929820047024437665283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8233286546698016291776855 12349929820047024437665283)
      ·
        refine ⟨18524894730070536656497925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12349929820047024437665283 18524894730070536656497925)
        ·
          refine ⟨3473417761888225623093361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18524894730070536656497925 3473417761888225623093361)
          ·
            refine ⟨2605063321416169217320021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3473417761888225623093361 2605063321416169217320021)
            ·
              refine ⟨30528085797845733015469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2605063321416169217320021 30528085797845733015469)
              ·
                rfl

theorem cell20_601964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 8].length) (baseStart_601964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601964 prefixEnd_601964 := by exact prefixLift 601964
  have htrace : WordTrace (prefixWord ++ tailWord_601964) baseStart_601964 baseEnd_601964 := by
    simpa [prefixWord, tailWord_601964, baseEnd_601964] using wordTrace_append hprefix tailTrace_601964
  have hstable : (prefixWord ++ tailWord_601964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601964).length < 2 ^ (prefixWord ++ tailWord_601964).sum := by decide
  have hdescent : baseEnd_601964 < baseStart_601964 := by decide
  rcases family_descends (prefixWord ++ tailWord_601964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602009 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 7]
def baseStart_602009 : Nat := 118140960795 + 602009 * 2 ^ 59
def prefixEnd_602009 : Nat := 4983230072969 + 3 ^ 40 * 602009 * 2
def baseEnd_602009 : Nat := 274773311406791440639037

theorem tailTrace_602009 : CollatzResearch.WordTrace tailWord_602009 prefixEnd_602009 274773311406791440639037 := by
  unfold tailWord_602009
  simp only [CollatzResearch.WordTrace]
  refine ⟨21957072076031682796793081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14638048050687788531195387 21957072076031682796793081)
  ·
    refine ⟨16467804057023762097594811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21957072076031682796793081 16467804057023762097594811)
    ·
      refine ⟨24701706085535643146392217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16467804057023762097594811 24701706085535643146392217)
      ·
        refine ⟨18526279564151732359794163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24701706085535643146392217 18526279564151732359794163)
        ·
          refine ⟨27789419346227598539691245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18526279564151732359794163 27789419346227598539691245)
          ·
            refine ⟨10421032254835349452384217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27789419346227598539691245 10421032254835349452384217)
            ·
              refine ⟨7815774191126512089288163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10421032254835349452384217 7815774191126512089288163)
              ·
                refine ⟨11723661286689768133932245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7815774191126512089288163 11723661286689768133932245)
                ·
                  refine ⟨274773311406791440639037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11723661286689768133932245 274773311406791440639037)
                  ·
                    rfl

theorem cell20_602009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_602009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602009 prefixEnd_602009 := by exact prefixLift 602009
  have htrace : WordTrace (prefixWord ++ tailWord_602009) baseStart_602009 baseEnd_602009 := by
    simpa [prefixWord, tailWord_602009, baseEnd_602009] using wordTrace_append hprefix tailTrace_602009
  have hstable : (prefixWord ++ tailWord_602009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602009).length < 2 ^ (prefixWord ++ tailWord_602009).sum := by decide
  have hdescent : baseEnd_602009 < baseStart_602009 := by decide
  rcases family_descends (prefixWord ++ tailWord_602009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602077 : List Nat := [1, 4, 3, 1, 4, 1, 1, 2, 3]
def baseStart_602077 : Nat := 118140960795 + 602077 * 2 ^ 59
def prefixEnd_602077 : Nat := 4983230072969 + 3 ^ 40 * 602077 * 2
def baseEnd_602077 : Nat := 274804348459685426372093

theorem tailTrace_602077 : CollatzResearch.WordTrace tailWord_602077 prefixEnd_602077 274804348459685426372093 := by
  unfold tailWord_602077
  simp only [CollatzResearch.WordTrace]
  refine ⟨21959552239785330410268485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14639701493190220273512323 21959552239785330410268485)
  ·
    refine ⟨4117416044959749451925341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21959552239785330410268485 4117416044959749451925341)
    ·
      refine ⟨1544031016859906044472003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4117416044959749451925341 1544031016859906044472003)
      ·
        refine ⟨2316046525289859066708005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544031016859906044472003 2316046525289859066708005)
        ·
          refine ⟨434258723491848575007751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2316046525289859066708005 434258723491848575007751)
          ·
            refine ⟨651388085237772862511627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434258723491848575007751 651388085237772862511627)
            ·
              refine ⟨977082127856659293767441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651388085237772862511627 977082127856659293767441)
              ·
                refine ⟨732811595892494470325581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 977082127856659293767441 732811595892494470325581)
                ·
                  refine ⟨274804348459685426372093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732811595892494470325581 274804348459685426372093)
                  ·
                    rfl

theorem cell20_602077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_602077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602077 prefixEnd_602077 := by exact prefixLift 602077
  have htrace : WordTrace (prefixWord ++ tailWord_602077) baseStart_602077 baseEnd_602077 := by
    simpa [prefixWord, tailWord_602077, baseEnd_602077] using wordTrace_append hprefix tailTrace_602077
  have hstable : (prefixWord ++ tailWord_602077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602077).length < 2 ^ (prefixWord ++ tailWord_602077).sum := by decide
  have hdescent : baseEnd_602077 < baseStart_602077 := by decide
  rcases family_descends (prefixWord ++ tailWord_602077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602109 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 4]
def baseStart_602109 : Nat := 118140960795 + 602109 * 2 ^ 59
def prefixEnd_602109 : Nat := 4983230072969 + 3 ^ 40 * 602109 * 2
def baseEnd_602109 : Nat := 274818954131635537305295

theorem tailTrace_602109 : CollatzResearch.WordTrace tailWord_602109 prefixEnd_602109 274818954131635537305295 := by
  unfold tailWord_602109
  simp only [CollatzResearch.WordTrace]
  refine ⟨21960719375669399875433381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14640479583779599916955587 21960719375669399875433381)
  ·
    refine ⟨4117634882938012476643759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21960719375669399875433381 4117634882938012476643759)
    ·
      refine ⟨6176452324407018714965639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4117634882938012476643759 6176452324407018714965639)
      ·
        refine ⟨9264678486610528072448459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6176452324407018714965639 9264678486610528072448459)
        ·
          refine ⟨13897017729915792108672689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9264678486610528072448459 13897017729915792108672689)
          ·
            refine ⟨10422763297436844081504517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13897017729915792108672689 10422763297436844081504517)
            ·
              refine ⟨1954268118269408265282097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10422763297436844081504517 1954268118269408265282097)
              ·
                refine ⟨1465701088702056198961573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1954268118269408265282097 1465701088702056198961573)
                ·
                  refine ⟨274818954131635537305295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1465701088702056198961573 274818954131635537305295)
                  ·
                    rfl

theorem cell20_602109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_602109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602109 prefixEnd_602109 := by exact prefixLift 602109
  have htrace : WordTrace (prefixWord ++ tailWord_602109) baseStart_602109 baseEnd_602109 := by
    simpa [prefixWord, tailWord_602109, baseEnd_602109] using wordTrace_append hprefix tailTrace_602109
  have hstable : (prefixWord ++ tailWord_602109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602109).length < 2 ^ (prefixWord ++ tailWord_602109).sum := by decide
  have hdescent : baseEnd_602109 < baseStart_602109 := by decide
  rcases family_descends (prefixWord ++ tailWord_602109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602122 : List Nat := [3, 1, 2, 2, 4, 2, 1, 3, 2]
def baseStart_602122 : Nat := 118140960795 + 602122 * 2 ^ 59
def prefixEnd_602122 : Nat := 4983230072969 + 3 ^ 40 * 602122 * 2
def baseEnd_602122 : Nat := 274824887685865269871909

theorem tailTrace_602122 : CollatzResearch.WordTrace tailWord_602122 prefixEnd_602122 274824887685865269871909 := by
  unfold tailWord_602122
  simp only [CollatzResearch.WordTrace]
  refine ⟨5490298381155575773914155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14640795683081535397104413 5490298381155575773914155)
  ·
    refine ⟨8235447571733363660871233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5490298381155575773914155 8235447571733363660871233)
    ·
      refine ⟨6176585678800022745653425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8235447571733363660871233 6176585678800022745653425)
      ·
        refine ⟨4632439259100017059240069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6176585678800022745653425 4632439259100017059240069)
        ·
          refine ⟨868582361081253198607513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4632439259100017059240069 868582361081253198607513)
          ·
            refine ⟨651436770810939898955635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 868582361081253198607513 651436770810939898955635)
            ·
              refine ⟨977155156216409848433453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651436770810939898955635 977155156216409848433453)
              ·
                refine ⟨366433183581153693162545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 977155156216409848433453 366433183581153693162545)
                ·
                  refine ⟨274824887685865269871909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366433183581153693162545 274824887685865269871909)
                  ·
                    rfl

theorem cell20_602122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_602122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602122 prefixEnd_602122 := by exact prefixLift 602122
  have htrace : WordTrace (prefixWord ++ tailWord_602122) baseStart_602122 baseEnd_602122 := by
    simpa [prefixWord, tailWord_602122, baseEnd_602122] using wordTrace_append hprefix tailTrace_602122
  have hstable : (prefixWord ++ tailWord_602122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602122).length < 2 ^ (prefixWord ++ tailWord_602122).sum := by decide
  have hdescent : baseEnd_602122 < baseStart_602122 := by decide
  rcases family_descends (prefixWord ++ tailWord_602122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602123 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 7]
def baseStart_602123 : Nat := 118140960795 + 602123 * 2 ^ 59
def prefixEnd_602123 : Nat := 4983230072969 + 3 ^ 40 * 602123 * 2
def baseEnd_602123 : Nat := 274825344113113710838571

theorem tailTrace_602123 : CollatzResearch.WordTrace tailWord_602123 prefixEnd_602123 274825344113113710838571 := by
  unfold tailWord_602123
  simp only [CollatzResearch.WordTrace]
  refine ⟨21961229997618680266443023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14640819998412453510962015 21961229997618680266443023)
  ·
    refine ⟨32941844996428020399664535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21961229997618680266443023 32941844996428020399664535)
    ·
      refine ⟨49412767494642030599496803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32941844996428020399664535 49412767494642030599496803)
      ·
        refine ⟨74119151241963045899245205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49412767494642030599496803 74119151241963045899245205)
        ·
          refine ⟨3474335214467017776527119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74119151241963045899245205 3474335214467017776527119)
          ·
            refine ⟨5211502821700526664790679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3474335214467017776527119 5211502821700526664790679)
            ·
              refine ⟨7817254232550789997186019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5211502821700526664790679 7817254232550789997186019)
              ·
                refine ⟨11725881348826184995779029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7817254232550789997186019 11725881348826184995779029)
                ·
                  refine ⟨274825344113113710838571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11725881348826184995779029 274825344113113710838571)
                  ·
                    rfl

theorem cell20_602123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_602123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602123 prefixEnd_602123 := by exact prefixLift 602123
  have htrace : WordTrace (prefixWord ++ tailWord_602123) baseStart_602123 baseEnd_602123 := by
    simpa [prefixWord, tailWord_602123, baseEnd_602123] using wordTrace_append hprefix tailTrace_602123
  have hstable : (prefixWord ++ tailWord_602123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602123).length < 2 ^ (prefixWord ++ tailWord_602123).sum := by decide
  have hdescent : baseEnd_602123 < baseStart_602123 := by decide
  rcases family_descends (prefixWord ++ tailWord_602123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602133 : List Nat := [1, 3, 2, 1, 5, 2, 6]
def baseStart_602133 : Nat := 118140960795 + 602133 * 2 ^ 59
def prefixEnd_602133 : Nat := 4983230072969 + 3 ^ 40 * 602133 * 2
def baseEnd_602133 : Nat := 30536656487288680056133

theorem tailTrace_602133 : CollatzResearch.WordTrace tailWord_602133 prefixEnd_602133 30536656487288680056133 := by
  unfold tailWord_602133
  simp only [CollatzResearch.WordTrace]
  refine ⟨21961594727582451974307053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14641063151721634649538035 21961594727582451974307053)
  ·
    refine ⟨8235598022843419490365145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21961594727582451974307053 8235598022843419490365145)
    ·
      refine ⟨6176698517132564617773859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8235598022843419490365145 6176698517132564617773859)
      ·
        refine ⟨9265047775698846926660789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6176698517132564617773859 9265047775698846926660789)
        ·
          refine ⟨868598228971766899374449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9265047775698846926660789 868598228971766899374449)
          ·
            refine ⟨651448671728825174530837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 868598228971766899374449 651448671728825174530837)
            ·
              refine ⟨30536656487288680056133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 651448671728825174530837 30536656487288680056133)
              ·
                rfl

theorem cell20_602133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 6].length) (baseStart_602133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602133 prefixEnd_602133 := by exact prefixLift 602133
  have htrace : WordTrace (prefixWord ++ tailWord_602133) baseStart_602133 baseEnd_602133 := by
    simpa [prefixWord, tailWord_602133, baseEnd_602133] using wordTrace_append hprefix tailTrace_602133
  have hstable : (prefixWord ++ tailWord_602133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602133).length < 2 ^ (prefixWord ++ tailWord_602133).sum := by decide
  have hdescent : baseEnd_602133 < baseStart_602133 := by decide
  rcases family_descends (prefixWord ++ tailWord_602133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602140 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_602140 : Nat := 118140960795 + 602140 * 2 ^ 59
def prefixEnd_602140 : Nat := 4983230072969 + 3 ^ 40 * 602140 * 2
def baseEnd_602140 : Nat := 274833103376337207271835

theorem tailTrace_602140 : CollatzResearch.WordTrace tailWord_602140 prefixEnd_602140 274833103376337207271835 := by
  unfold tailWord_602140
  simp only [CollatzResearch.WordTrace]
  refine ⟨10980925019278546084905937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14641233359038061446541249 10980925019278546084905937)
  ·
    refine ⟨8235693764458909563679453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10980925019278546084905937 8235693764458909563679453)
    ·
      refine ⟨3088385161672091086379795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8235693764458909563679453 3088385161672091086379795)
      ·
        refine ⟨4632577742508136629569693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3088385161672091086379795 4632577742508136629569693)
        ·
          refine ⟨1737216653440551236088635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4632577742508136629569693 1737216653440551236088635)
          ·
            refine ⟨2605824980160826854132953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1737216653440551236088635 2605824980160826854132953)
            ·
              refine ⟨1954368735120620140599715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2605824980160826854132953 1954368735120620140599715)
              ·
                refine ⟨2931553102680930210899573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1954368735120620140599715 2931553102680930210899573)
                ·
                  refine ⟨274833103376337207271835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2931553102680930210899573 274833103376337207271835)
                  ·
                    rfl

theorem cell20_602140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_602140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602140 prefixEnd_602140 := by exact prefixLift 602140
  have htrace : WordTrace (prefixWord ++ tailWord_602140) baseStart_602140 baseEnd_602140 := by
    simpa [prefixWord, tailWord_602140, baseEnd_602140] using wordTrace_append hprefix tailTrace_602140
  have hstable : (prefixWord ++ tailWord_602140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602140).length < 2 ^ (prefixWord ++ tailWord_602140).sum := by decide
  have hdescent : baseEnd_602140 < baseStart_602140 := by decide
  rcases family_descends (prefixWord ++ tailWord_602140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602143 : List Nat := [1, 1, 2, 4, 1, 2, 5, 2, 2]
def baseStart_602143 : Nat := 118140960795 + 602143 * 2 ^ 59
def prefixEnd_602143 : Nat := 4983230072969 + 3 ^ 40 * 602143 * 2
def baseEnd_602143 : Nat := 274834472658082530171823

theorem tailTrace_602143 : CollatzResearch.WordTrace tailWord_602143 prefixEnd_602143 274834472658082530171823 := by
  unfold tailWord_602143
  simp only [CollatzResearch.WordTrace]
  refine ⟨21961959457546223682171083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14641306305030815788114055 21961959457546223682171083)
  ·
    refine ⟨32942939186319335523256625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21961959457546223682171083 32942939186319335523256625)
    ·
      refine ⟨24707204389739501642442469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32942939186319335523256625 24707204389739501642442469)
      ·
        refine ⟨4632600823076156557957963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24707204389739501642442469 4632600823076156557957963)
        ·
          refine ⟨6948901234614234836936945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4632600823076156557957963 6948901234614234836936945)
          ·
            refine ⟨5211675925960676127702709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6948901234614234836936945 5211675925960676127702709)
            ·
              refine ⟨488594618058813386972129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5211675925960676127702709 488594618058813386972129)
              ·
                refine ⟨366445963544110040229097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 488594618058813386972129 366445963544110040229097)
                ·
                  refine ⟨274834472658082530171823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366445963544110040229097 274834472658082530171823)
                  ·
                    rfl

theorem cell20_602143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 2].length) (baseStart_602143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602143 prefixEnd_602143 := by exact prefixLift 602143
  have htrace : WordTrace (prefixWord ++ tailWord_602143) baseStart_602143 baseEnd_602143 := by
    simpa [prefixWord, tailWord_602143, baseEnd_602143] using wordTrace_append hprefix tailTrace_602143
  have hstable : (prefixWord ++ tailWord_602143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602143).length < 2 ^ (prefixWord ++ tailWord_602143).sum := by decide
  have hdescent : baseEnd_602143 < baseStart_602143 := by decide
  rcases family_descends (prefixWord ++ tailWord_602143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602199 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 5]
def baseStart_602199 : Nat := 118140960795 + 602199 * 2 ^ 59
def prefixEnd_602199 : Nat := 4983230072969 + 3 ^ 40 * 602199 * 2
def baseEnd_602199 : Nat := 274860032583995224304927

theorem tailTrace_602199 : CollatzResearch.WordTrace tailWord_602199 prefixEnd_602199 274860032583995224304927 := by
  unfold tailWord_602199
  simp only [CollatzResearch.WordTrace]
  refine ⟨21964001945343345246209651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14642667963562230164139767 21964001945343345246209651)
  ·
    refine ⟨32946002918015017869314477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21964001945343345246209651 32946002918015017869314477)
    ·
      refine ⟨12354751094255631700992929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32946002918015017869314477 12354751094255631700992929)
      ·
        refine ⟨9266063320691723775744697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12354751094255631700992929 9266063320691723775744697)
        ·
          refine ⟨6949547490518792831808523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9266063320691723775744697 6949547490518792831808523)
          ·
            refine ⟨10424321235778189247712785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6949547490518792831808523 10424321235778189247712785)
            ·
              refine ⟨7818240926833641935784589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10424321235778189247712785 7818240926833641935784589)
              ·
                refine ⟨2931840347562615725919221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7818240926833641935784589 2931840347562615725919221)
                ·
                  refine ⟨274860032583995224304927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2931840347562615725919221 274860032583995224304927)
                  ·
                    rfl

theorem cell20_602199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_602199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602199 prefixEnd_602199 := by exact prefixLift 602199
  have htrace : WordTrace (prefixWord ++ tailWord_602199) baseStart_602199 baseEnd_602199 := by
    simpa [prefixWord, tailWord_602199, baseEnd_602199] using wordTrace_append hprefix tailTrace_602199
  have hstable : (prefixWord ++ tailWord_602199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602199).length < 2 ^ (prefixWord ++ tailWord_602199).sum := by decide
  have hdescent : baseEnd_602199 < baseStart_602199 := by decide
  rcases family_descends (prefixWord ++ tailWord_602199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602202 : List Nat := [3, 1, 1, 2, 1, 1, 5, 4, 2]
def baseStart_602202 : Nat := 118140960795 + 602202 * 2 ^ 59
def prefixEnd_602202 : Nat := 4983230072969 + 3 ^ 40 * 602202 * 2
def baseEnd_602202 : Nat := 274861401865740547204915

theorem tailTrace_602202 : CollatzResearch.WordTrace tailWord_602202 prefixEnd_602202 274861401865740547204915 := by
  unfold tailWord_602202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5491027841083119189642215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14642740909554984505712573 5491027841083119189642215)
  ·
    refine ⟨8236541761624678784463323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5491027841083119189642215 8236541761624678784463323)
    ·
      refine ⟨12354812642437018176694985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8236541761624678784463323 12354812642437018176694985)
      ·
        refine ⟨9266109481827763632521239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12354812642437018176694985 9266109481827763632521239)
        ·
          refine ⟨13899164222741645448781859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9266109481827763632521239 13899164222741645448781859)
          ·
            refine ⟨20848746334112468173172789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13899164222741645448781859 20848746334112468173172789)
            ·
              refine ⟨1954569968823043891234949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20848746334112468173172789 1954569968823043891234949)
              ·
                refine ⟨366481869154320729606553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1954569968823043891234949 366481869154320729606553)
                ·
                  refine ⟨274861401865740547204915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366481869154320729606553 274861401865740547204915)
                  ·
                    rfl

theorem cell20_602202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_602202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602202 prefixEnd_602202 := by exact prefixLift 602202
  have htrace : WordTrace (prefixWord ++ tailWord_602202) baseStart_602202 baseEnd_602202 := by
    simpa [prefixWord, tailWord_602202, baseEnd_602202] using wordTrace_append hprefix tailTrace_602202
  have hstable : (prefixWord ++ tailWord_602202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602202).length < 2 ^ (prefixWord ++ tailWord_602202).sum := by decide
  have hdescent : baseEnd_602202 < baseStart_602202 := by decide
  rcases family_descends (prefixWord ++ tailWord_602202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602223 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 4]
def baseStart_602223 : Nat := 118140960795 + 602223 * 2 ^ 59
def prefixEnd_602223 : Nat := 4983230072969 + 3 ^ 40 * 602223 * 2
def baseEnd_602223 : Nat := 274870986837957807504829

theorem tailTrace_602223 : CollatzResearch.WordTrace tailWord_602223 prefixEnd_602223 274870986837957807504829 := by
  unfold tailWord_602223
  simp only [CollatzResearch.WordTrace]
  refine ⟨21964877297256397345083323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14643251531504264896722215 21964877297256397345083323)
  ·
    refine ⟨32947315945884596017624985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21964877297256397345083323 32947315945884596017624985)
    ·
      refine ⟨24710486959413447013218739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32947315945884596017624985 24710486959413447013218739)
      ·
        refine ⟨37065730439120170519828109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24710486959413447013218739 37065730439120170519828109)
        ·
          refine ⟨13899648914670063944935541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37065730439120170519828109 13899648914670063944935541)
          ·
            refine ⟨1303092085750318494837707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13899648914670063944935541 1303092085750318494837707)
            ·
              refine ⟨1954638128625477742256561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303092085750318494837707 1954638128625477742256561)
              ·
                refine ⟨1465978596469108306692421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1954638128625477742256561 1465978596469108306692421)
                ·
                  refine ⟨274870986837957807504829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1465978596469108306692421 274870986837957807504829)
                  ·
                    rfl

theorem cell20_602223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_602223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602223 prefixEnd_602223 := by exact prefixLift 602223
  have htrace : WordTrace (prefixWord ++ tailWord_602223) baseStart_602223 baseEnd_602223 := by
    simpa [prefixWord, tailWord_602223, baseEnd_602223] using wordTrace_append hprefix tailTrace_602223
  have hstable : (prefixWord ++ tailWord_602223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602223).length < 2 ^ (prefixWord ++ tailWord_602223).sum := by decide
  have hdescent : baseEnd_602223 < baseStart_602223 := by decide
  rcases family_descends (prefixWord ++ tailWord_602223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602261 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 4]
def baseStart_602261 : Nat := 118140960795 + 602261 * 2 ^ 59
def prefixEnd_602261 : Nat := 4983230072969 + 3 ^ 40 * 602261 * 2
def baseEnd_602261 : Nat := 274888331073398564238007

theorem tailTrace_602261 : CollatzResearch.WordTrace tailWord_602261 prefixEnd_602261 274888331073398564238007 := by
  unfold tailWord_602261
  simp only [CollatzResearch.WordTrace]
  refine ⟨21966263271118729834966637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14644175514079153223311091 21966263271118729834966637)
  ·
    refine ⟨8237348726669523688112489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21966263271118729834966637 8237348726669523688112489)
    ·
      refine ⟨6178011545002142766084367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8237348726669523688112489 6178011545002142766084367)
      ·
        refine ⟨9267017317503214149126551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6178011545002142766084367 9267017317503214149126551)
        ·
          refine ⟨13900525976254821223689827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9267017317503214149126551 13900525976254821223689827)
          ·
            refine ⟨20850788964382231835534741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13900525976254821223689827 20850788964382231835534741)
            ·
              refine ⟨977380732705417117290691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20850788964382231835534741 977380732705417117290691)
              ·
                refine ⟨1466071099058125675936037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 977380732705417117290691 1466071099058125675936037)
                ·
                  refine ⟨274888331073398564238007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1466071099058125675936037 274888331073398564238007)
                  ·
                    rfl

theorem cell20_602261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_602261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602261 prefixEnd_602261 := by exact prefixLift 602261
  have htrace : WordTrace (prefixWord ++ tailWord_602261) baseStart_602261 baseEnd_602261 := by
    simpa [prefixWord, tailWord_602261, baseEnd_602261] using wordTrace_append hprefix tailTrace_602261
  have hstable : (prefixWord ++ tailWord_602261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602261).length < 2 ^ (prefixWord ++ tailWord_602261).sum := by decide
  have hdescent : baseEnd_602261 < baseStart_602261 := by decide
  rcases family_descends (prefixWord ++ tailWord_602261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602268 : List Nat := [2, 2, 3, 2, 1, 1, 2, 7]
def baseStart_602268 : Nat := 118140960795 + 602268 * 2 ^ 59
def prefixEnd_602268 : Nat := 4983230072969 + 3 ^ 40 * 602268 * 2
def baseEnd_602268 : Nat := 91630508688045883668215

theorem tailTrace_602268 : CollatzResearch.WordTrace tailWord_602268 prefixEnd_602268 91630508688045883668215 := by
  unfold tailWord_602268
  simp only [CollatzResearch.WordTrace]
  refine ⟨10983259291046685015235729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14644345721395580020314305 10983259291046685015235729)
  ·
    refine ⟨8237444468285013761426797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10983259291046685015235729 8237444468285013761426797)
    ·
      refine ⟨3089041675606880160535049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8237444468285013761426797 3089041675606880160535049)
      ·
        refine ⟨2316781256705160120401287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3089041675606880160535049 2316781256705160120401287)
        ·
          refine ⟨3475171885057740180601931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316781256705160120401287 3475171885057740180601931)
          ·
            refine ⟨5212757827586610270902897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475171885057740180601931 5212757827586610270902897)
            ·
              refine ⟨3909568370689957703177173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5212757827586610270902897 3909568370689957703177173)
              ·
                refine ⟨91630508688045883668215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3909568370689957703177173 91630508688045883668215)
                ·
                  rfl

theorem cell20_602268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_602268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602268 prefixEnd_602268 := by exact prefixLift 602268
  have htrace : WordTrace (prefixWord ++ tailWord_602268) baseStart_602268 baseEnd_602268 := by
    simpa [prefixWord, tailWord_602268, baseEnd_602268] using wordTrace_append hprefix tailTrace_602268
  have hstable : (prefixWord ++ tailWord_602268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602268).length < 2 ^ (prefixWord ++ tailWord_602268).sum := by decide
  have hdescent : baseEnd_602268 < baseStart_602268 := by decide
  rcases family_descends (prefixWord ++ tailWord_602268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602285 : List Nat := [1, 5, 2, 1, 2, 2, 1, 6]
def baseStart_602285 : Nat := 118140960795 + 602285 * 2 ^ 59
def prefixEnd_602285 : Nat := 4983230072969 + 3 ^ 40 * 602285 * 2
def baseEnd_602285 : Nat := 91633095109120382479303

theorem tailTrace_602285 : CollatzResearch.WordTrace tailWord_602285 prefixEnd_602285 91633095109120382479303 := by
  unfold tailWord_602285
  simp only [CollatzResearch.WordTrace]
  refine ⟨21967138623031781933840309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14644759082021187955893539 21967138623031781933840309)
  ·
    refine ⟨2059419245909229556297529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21967138623031781933840309 2059419245909229556297529)
    ·
      refine ⟨1544564434431922167223147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2059419245909229556297529 1544564434431922167223147)
      ·
        refine ⟨2316846651647883250834721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544564434431922167223147 2316846651647883250834721)
        ·
          refine ⟨1737634988735912438126041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2316846651647883250834721 1737634988735912438126041)
          ·
            refine ⟨1303226241551934328594531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1737634988735912438126041 1303226241551934328594531)
            ·
              refine ⟨1954839362327901492891797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303226241551934328594531 1954839362327901492891797)
              ·
                refine ⟨91633095109120382479303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1954839362327901492891797 91633095109120382479303)
                ·
                  rfl

theorem cell20_602285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 6].length) (baseStart_602285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602285 prefixEnd_602285 := by exact prefixLift 602285
  have htrace : WordTrace (prefixWord ++ tailWord_602285) baseStart_602285 baseEnd_602285 := by
    simpa [prefixWord, tailWord_602285, baseEnd_602285] using wordTrace_append hprefix tailTrace_602285
  have hstable : (prefixWord ++ tailWord_602285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602285).length < 2 ^ (prefixWord ++ tailWord_602285).sum := by decide
  have hdescent : baseEnd_602285 < baseStart_602285 := by decide
  rcases family_descends (prefixWord ++ tailWord_602285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602295 : List Nat := [1, 1, 3, 1, 4, 4, 1, 3, 2]
def baseStart_602295 : Nat := 118140960795 + 602295 * 2 ^ 59
def prefixEnd_602295 : Nat := 4983230072969 + 3 ^ 40 * 602295 * 2
def baseEnd_602295 : Nat := 274903849599845557104535

theorem tailTrace_602295 : CollatzResearch.WordTrace tailWord_602295 prefixEnd_602295 274903849599845557104535 := by
  unfold tailWord_602295
  simp only [CollatzResearch.WordTrace]
  refine ⟨21967503352995553641704339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14645002235330369094469559 21967503352995553641704339)
  ·
    refine ⟨32951255029493330462556509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21967503352995553641704339 32951255029493330462556509)
    ·
      refine ⟨12356720636059998923458691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32951255029493330462556509 12356720636059998923458691)
      ·
        refine ⟨18535080954089998385188037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12356720636059998923458691 18535080954089998385188037)
        ·
          refine ⟨3475327678891874697222757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18535080954089998385188037 3475327678891874697222757)
          ·
            refine ⟨651623939792226505729267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3475327678891874697222757 651623939792226505729267)
            ·
              refine ⟨977435909688339758593901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651623939792226505729267 977435909688339758593901)
              ·
                refine ⟨366538466133127409472713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 977435909688339758593901 366538466133127409472713)
                ·
                  refine ⟨274903849599845557104535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366538466133127409472713 274903849599845557104535)
                  ·
                    rfl

theorem cell20_602295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 2].length) (baseStart_602295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602295 prefixEnd_602295 := by exact prefixLift 602295
  have htrace : WordTrace (prefixWord ++ tailWord_602295) baseStart_602295 baseEnd_602295 := by
    simpa [prefixWord, tailWord_602295, baseEnd_602295] using wordTrace_append hprefix tailTrace_602295
  have hstable : (prefixWord ++ tailWord_602295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602295).length < 2 ^ (prefixWord ++ tailWord_602295).sum := by decide
  have hdescent : baseEnd_602295 < baseStart_602295 := by decide
  rcases family_descends (prefixWord ++ tailWord_602295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602302 : List Nat := [4, 2, 1, 1, 5, 1, 6]
def baseStart_602302 : Nat := 118140960795 + 602302 * 2 ^ 59
def prefixEnd_602302 : Nat := 4983230072969 + 3 ^ 40 * 602302 * 2
def baseEnd_602302 : Nat := 30545227176731627096797

theorem tailTrace_602302 : CollatzResearch.WordTrace tailWord_602302 prefixEnd_602302 30545227176731627096797 := by
  unfold tailWord_602302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2745969832996274229651145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14645172442646795891472773 2745969832996274229651145)
  ·
    refine ⟨2059477374747205672238359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2745969832996274229651145 2059477374747205672238359)
    ·
      refine ⟨3089216062120808508357539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2059477374747205672238359 3089216062120808508357539)
      ·
        refine ⟨4633824093181212762536309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3089216062120808508357539 4633824093181212762536309)
        ·
          refine ⟨434421008735738696487779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4633824093181212762536309 434421008735738696487779)
          ·
            refine ⟨651631513103608044731669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434421008735738696487779 651631513103608044731669)
            ·
              refine ⟨30545227176731627096797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 651631513103608044731669 30545227176731627096797)
              ·
                rfl

theorem cell20_602302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 6].length) (baseStart_602302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602302 prefixEnd_602302 := by exact prefixLift 602302
  have htrace : WordTrace (prefixWord ++ tailWord_602302) baseStart_602302 baseEnd_602302 := by
    simpa [prefixWord, tailWord_602302, baseEnd_602302] using wordTrace_append hprefix tailTrace_602302
  have hstable : (prefixWord ++ tailWord_602302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602302).length < 2 ^ (prefixWord ++ tailWord_602302).sum := by decide
  have hdescent : baseEnd_602302 < baseStart_602302 := by decide
  rcases family_descends (prefixWord ++ tailWord_602302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602326 : List Nat := [5, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_602326 : Nat := 118140960795 + 602326 * 2 ^ 59
def prefixEnd_602326 : Nat := 4983230072969 + 3 ^ 40 * 602326 * 2
def baseEnd_602326 : Nat := 274917998844547227071075

theorem tailTrace_602326 : CollatzResearch.WordTrace tailWord_602326 prefixEnd_602326 274917998844547227071075 := by
  unfold tailWord_602326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1373039625992702871005177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14645756010588830624055221 1373039625992702871005177)
  ·
    refine ⟨1029779719494527153253883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1373039625992702871005177 1029779719494527153253883)
    ·
      refine ⟨1544669579241790729880825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1029779719494527153253883 1544669579241790729880825)
      ·
        refine ⟨1158502184431343047410619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1544669579241790729880825 1158502184431343047410619)
        ·
          refine ⟨1737753276647014571115929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158502184431343047410619 1737753276647014571115929)
          ·
            refine ⟨1303314957485260928336947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1737753276647014571115929 1303314957485260928336947)
            ·
              refine ⟨1954972436227891392505421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303314957485260928336947 1954972436227891392505421)
              ·
                refine ⟨733114663585459272189533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1954972436227891392505421 733114663585459272189533)
                ·
                  refine ⟨274917998844547227071075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733114663585459272189533 274917998844547227071075)
                  ·
                    rfl

theorem cell20_602326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_602326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602326 prefixEnd_602326 := by exact prefixLift 602326
  have htrace : WordTrace (prefixWord ++ tailWord_602326) baseStart_602326 baseEnd_602326 := by
    simpa [prefixWord, tailWord_602326, baseEnd_602326] using wordTrace_append hprefix tailTrace_602326
  have hstable : (prefixWord ++ tailWord_602326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602326).length < 2 ^ (prefixWord ++ tailWord_602326).sum := by decide
  have hdescent : baseEnd_602326 < baseStart_602326 := by decide
  rcases family_descends (prefixWord ++ tailWord_602326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602344 : List Nat := [2, 1, 4, 1, 2, 2, 2, 6]
def baseStart_602344 : Nat := 118140960795 + 602344 * 2 ^ 59
def prefixEnd_602344 : Nat := 4983230072969 + 3 ^ 40 * 602344 * 2
def baseEnd_602344 : Nat := 91642071511673054823667

theorem tailTrace_602344 : CollatzResearch.WordTrace tailWord_602344 prefixEnd_602344 91642071511673054823667 := by
  unfold tailWord_602344
  simp only [CollatzResearch.WordTrace]
  refine ⟨10984645264909017505119043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14646193686545356673492057 10984645264909017505119043)
  ·
    refine ⟨16476967897363526257678565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10984645264909017505119043 16476967897363526257678565)
    ·
      refine ⟨3089431480755661173314731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16476967897363526257678565 3089431480755661173314731)
      ·
        refine ⟨4634147221133491759972097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3089431480755661173314731 4634147221133491759972097)
        ·
          refine ⟨3475610415850118819979073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4634147221133491759972097 3475610415850118819979073)
          ·
            refine ⟨2606707811887589114984305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3475610415850118819979073 2606707811887589114984305)
            ·
              refine ⟨1955030858915691836238229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2606707811887589114984305 1955030858915691836238229)
              ·
                refine ⟨91642071511673054823667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1955030858915691836238229 91642071511673054823667)
                ·
                  rfl

theorem cell20_602344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_602344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602344 prefixEnd_602344 := by exact prefixLift 602344
  have htrace : WordTrace (prefixWord ++ tailWord_602344) baseStart_602344 baseEnd_602344 := by
    simpa [prefixWord, tailWord_602344, baseEnd_602344] using wordTrace_append hprefix tailTrace_602344
  have hstable : (prefixWord ++ tailWord_602344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602344).length < 2 ^ (prefixWord ++ tailWord_602344).sum := by decide
  have hdescent : baseEnd_602344 < baseStart_602344 := by decide
  rcases family_descends (prefixWord ++ tailWord_602344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602399 : List Nat := [1, 1, 2, 4, 3, 2, 3, 4]
def baseStart_602399 : Nat := 118140960795 + 602399 * 2 ^ 59
def prefixEnd_602399 : Nat := 4983230072969 + 3 ^ 40 * 602399 * 2
def baseEnd_602399 : Nat := 91650439344561139212481

theorem tailTrace_602399 : CollatzResearch.WordTrace tailWord_602399 prefixEnd_602399 91650439344561139212481 := by
  unfold tailWord_602399
  simp only [CollatzResearch.WordTrace]
  refine ⟨21971296544618779403490251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14647531029745852935660167 21971296544618779403490251)
  ·
    refine ⟨32956944816928169105235377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21971296544618779403490251 32956944816928169105235377)
    ·
      refine ⟨24717708612696126828926533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32956944816928169105235377 24717708612696126828926533)
      ·
        refine ⟨4634570364880523780423725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24717708612696126828926533 4634570364880523780423725)
        ·
          refine ⟨1737963886830196417658897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4634570364880523780423725 1737963886830196417658897)
          ·
            refine ⟨1303472915122647313244173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1737963886830196417658897 1303472915122647313244173)
            ·
              refine ⟨488802343170992742466565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1303472915122647313244173 488802343170992742466565)
              ·
                refine ⟨91650439344561139212481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 488802343170992742466565 91650439344561139212481)
                ·
                  rfl

theorem cell20_602399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 4].length) (baseStart_602399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602399 prefixEnd_602399 := by exact prefixLift 602399
  have htrace : WordTrace (prefixWord ++ tailWord_602399) baseStart_602399 baseEnd_602399 := by
    simpa [prefixWord, tailWord_602399, baseEnd_602399] using wordTrace_append hprefix tailTrace_602399
  have hstable : (prefixWord ++ tailWord_602399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602399).length < 2 ^ (prefixWord ++ tailWord_602399).sum := by decide
  have hdescent : baseEnd_602399 < baseStart_602399 := by decide
  rcases family_descends (prefixWord ++ tailWord_602399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602430 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_602430 : Nat := 118140960795 + 602430 * 2 ^ 59
def prefixEnd_602430 : Nat := 4983230072969 + 3 ^ 40 * 602430 * 2
def baseEnd_602430 : Nat := 274965467278385087603983

theorem tailTrace_602430 : CollatzResearch.WordTrace tailWord_602430 prefixEnd_602430 274965467278385087603983 := by
  unfold tailWord_602430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2746553400938308962233593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14648284805004314465245829 2746553400938308962233593)
  ·
    refine ⟨2059915050703731721675195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2746553400938308962233593 2059915050703731721675195)
    ·
      refine ⟨3089872576055597582512793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2059915050703731721675195 3089872576055597582512793)
      ·
        refine ⟨2317404432041698186884595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3089872576055597582512793 2317404432041698186884595)
        ·
          refine ⟨3476106648062547280326893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2317404432041698186884595 3476106648062547280326893)
          ·
            refine ⟨1303539993023455230122585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3476106648062547280326893 1303539993023455230122585)
            ·
              refine ⟨977654994767591422591939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1303539993023455230122585 977654994767591422591939)
              ·
                refine ⟨1466482492151387133887909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 977654994767591422591939 1466482492151387133887909)
                ·
                  refine ⟨274965467278385087603983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1466482492151387133887909 274965467278385087603983)
                  ·
                    rfl

theorem cell20_602430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_602430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602430 prefixEnd_602430 := by exact prefixLift 602430
  have htrace : WordTrace (prefixWord ++ tailWord_602430) baseStart_602430 baseEnd_602430 := by
    simpa [prefixWord, tailWord_602430, baseEnd_602430] using wordTrace_append hprefix tailTrace_602430
  have hstable : (prefixWord ++ tailWord_602430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602430).length < 2 ^ (prefixWord ++ tailWord_602430).sum := by decide
  have hdescent : baseEnd_602430 < baseStart_602430 := by decide
  rcases family_descends (prefixWord ++ tailWord_602430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602441 : List Nat := [1, 2, 1, 1, 2, 3, 1, 9]
def baseStart_602441 : Nat := 118140960795 + 602441 * 2 ^ 59
def prefixEnd_602441 : Nat := 4983230072969 + 3 ^ 40 * 602441 * 2
def baseEnd_602441 : Nat := 91656829326039312745757

theorem tailTrace_602441 : CollatzResearch.WordTrace tailWord_602441 prefixEnd_602441 91656829326039312745757 := by
  unfold tailWord_602441
  simp only [CollatzResearch.WordTrace]
  refine ⟨21972828410466620576519177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14648552273644413717679451 21972828410466620576519177)
  ·
    refine ⟨16479621307849965432389383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21972828410466620576519177 16479621307849965432389383)
    ·
      refine ⟨24719431961774948148584075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16479621307849965432389383 24719431961774948148584075)
      ·
        refine ⟨37079147942662422222876113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24719431961774948148584075 37079147942662422222876113)
        ·
          refine ⟨27809360956996816667157085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37079147942662422222876113 27809360956996816667157085)
          ·
            refine ⟨10428510358873806250183907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27809360956996816667157085 10428510358873806250183907)
            ·
              refine ⟨15642765538310709375275861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10428510358873806250183907 15642765538310709375275861)
              ·
                refine ⟨91656829326039312745757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15642765538310709375275861 91656829326039312745757)
                ·
                  rfl

theorem cell20_602441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_602441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602441 prefixEnd_602441 := by exact prefixLift 602441
  have htrace : WordTrace (prefixWord ++ tailWord_602441) baseStart_602441 baseEnd_602441 := by
    simpa [prefixWord, tailWord_602441, baseEnd_602441] using wordTrace_append hprefix tailTrace_602441
  have hstable : (prefixWord ++ tailWord_602441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602441).length < 2 ^ (prefixWord ++ tailWord_602441).sum := by decide
  have hdescent : baseEnd_602441 < baseStart_602441 := by decide
  rcases family_descends (prefixWord ++ tailWord_602441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602464 : List Nat := [2, 1, 1, 3, 6, 1, 1, 3, 2]
def baseStart_602464 : Nat := 118140960795 + 602464 * 2 ^ 59
def prefixEnd_602464 : Nat := 4983230072969 + 3 ^ 40 * 602464 * 2
def baseEnd_602464 : Nat := 274980985804832080470511

theorem tailTrace_602464 : CollatzResearch.WordTrace tailWord_602464 prefixEnd_602464 274980985804832080470511 := by
  unfold tailWord_602464
  simp only [CollatzResearch.WordTrace]
  refine ⟨10986833644691647752303223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14649111526255530336404297 10986833644691647752303223)
  ·
    refine ⟨16480250467037471628454835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10986833644691647752303223 16480250467037471628454835)
    ·
      refine ⟨24720375700556207442682253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16480250467037471628454835 24720375700556207442682253)
      ·
        refine ⟨9270140887708577791005845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24720375700556207442682253 9270140887708577791005845)
        ·
          refine ⟨434537854111339583953399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9270140887708577791005845 434537854111339583953399)
          ·
            refine ⟨651806781167009375930099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434537854111339583953399 651806781167009375930099)
            ·
              refine ⟨977710171750514063895149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651806781167009375930099 977710171750514063895149)
              ·
                refine ⟨366641314406442773960681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 977710171750514063895149 366641314406442773960681)
                ·
                  refine ⟨274980985804832080470511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366641314406442773960681 274980985804832080470511)
                  ·
                    rfl

theorem cell20_602464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 2].length) (baseStart_602464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602464 prefixEnd_602464 := by exact prefixLift 602464
  have htrace : WordTrace (prefixWord ++ tailWord_602464) baseStart_602464 baseEnd_602464 := by
    simpa [prefixWord, tailWord_602464, baseEnd_602464] using wordTrace_append hprefix tailTrace_602464
  have hstable : (prefixWord ++ tailWord_602464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602464).length < 2 ^ (prefixWord ++ tailWord_602464).sum := by decide
  have hdescent : baseEnd_602464 < baseStart_602464 := by decide
  rcases family_descends (prefixWord ++ tailWord_602464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602558 : List Nat := [4, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_602558 : Nat := 118140960795 + 602558 * 2 ^ 59
def prefixEnd_602558 : Nat := 4983230072969 + 3 ^ 40 * 602558 * 2
def baseEnd_602558 : Nat := 275023889966185531336793

theorem tailTrace_602558 : CollatzResearch.WordTrace tailWord_602558 prefixEnd_602558 275023889966185531336793 := by
  unfold tailWord_602558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2747136968880343694816041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14651397167361833039018885 2747136968880343694816041)
  ·
    refine ⟨2060352726660257771112031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2747136968880343694816041 2060352726660257771112031)
    ·
      refine ⟨3090529089990386656668047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2060352726660257771112031 3090529089990386656668047)
      ·
        refine ⟨4635793634985579985002071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3090529089990386656668047 4635793634985579985002071)
        ·
          refine ⟨6953690452478369977503107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4635793634985579985002071 6953690452478369977503107)
          ·
            refine ⟨10430535678717554966254661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6953690452478369977503107 10430535678717554966254661)
            ·
              refine ⟨1955725439759541556172749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10430535678717554966254661 1955725439759541556172749)
              ·
                refine ⟨733397039909828083564781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1955725439759541556172749 733397039909828083564781)
                ·
                  refine ⟨275023889966185531336793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733397039909828083564781 275023889966185531336793)
                  ·
                    rfl

theorem cell20_602558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_602558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602558 prefixEnd_602558 := by exact prefixLift 602558
  have htrace : WordTrace (prefixWord ++ tailWord_602558) baseStart_602558 baseEnd_602558 := by
    simpa [prefixWord, tailWord_602558, baseEnd_602558] using wordTrace_append hprefix tailTrace_602558
  have hstable : (prefixWord ++ tailWord_602558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602558).length < 2 ^ (prefixWord ++ tailWord_602558).sum := by decide
  have hdescent : baseEnd_602558 < baseStart_602558 := by decide
  rcases family_descends (prefixWord ++ tailWord_602558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602578 : List Nat := [3, 2, 2, 4, 1, 1, 2, 3, 2]
def baseStart_602578 : Nat := 118140960795 + 602578 * 2 ^ 59
def prefixEnd_602578 : Nat := 4983230072969 + 3 ^ 40 * 602578 * 2
def baseEnd_602578 : Nat := 275033018511154350670045

theorem tailTrace_602578 : CollatzResearch.WordTrace tailWord_602578 prefixEnd_602578 275033018511154350670045 := by
  unfold tailWord_602578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5494456302742573243564097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14651883473980195316170925 5494456302742573243564097)
  ·
    refine ⟨4120842227056929932673073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5494456302742573243564097 4120842227056929932673073)
    ·
      refine ⟨3090631670292697449504805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4120842227056929932673073 3090631670292697449504805)
      ·
        refine ⟨579493438179880771782151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3090631670292697449504805 579493438179880771782151)
        ·
          refine ⟨869240157269821157673227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579493438179880771782151 869240157269821157673227)
          ·
            refine ⟨1303860235904731736509841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869240157269821157673227 1303860235904731736509841)
            ·
              refine ⟨977895176928548802382381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1303860235904731736509841 977895176928548802382381)
              ·
                refine ⟨366710691348205800893393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 977895176928548802382381 366710691348205800893393)
                ·
                  refine ⟨275033018511154350670045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366710691348205800893393 275033018511154350670045)
                  ·
                    rfl

theorem cell20_602578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_602578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602578 prefixEnd_602578 := by exact prefixLift 602578
  have htrace : WordTrace (prefixWord ++ tailWord_602578) baseStart_602578 baseEnd_602578 := by
    simpa [prefixWord, tailWord_602578, baseEnd_602578] using wordTrace_append hprefix tailTrace_602578
  have hstable : (prefixWord ++ tailWord_602578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602578).length < 2 ^ (prefixWord ++ tailWord_602578).sum := by decide
  have hdescent : baseEnd_602578 < baseStart_602578 := by decide
  rcases family_descends (prefixWord ++ tailWord_602578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602586 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_602586 : Nat := 118140960795 + 602586 * 2 ^ 59
def prefixEnd_602586 : Nat := 4983230072969 + 3 ^ 40 * 602586 * 2
def baseEnd_602586 : Nat := 275036669929141878403345

theorem tailTrace_602586 : CollatzResearch.WordTrace tailWord_602586 prefixEnd_602586 275036669929141878403345 := by
  unfold tailWord_602586
  simp only [CollatzResearch.WordTrace]
  refine ⟨5494529248735327585136903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14652077996627540227031741 5494529248735327585136903)
  ·
    refine ⟨8241793873102991377705355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5494529248735327585136903 8241793873102991377705355)
    ·
      refine ⟨12362690809654487066558033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8241793873102991377705355 12362690809654487066558033)
      ·
        refine ⟨9272018107240865299918525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12362690809654487066558033 9272018107240865299918525)
        ·
          refine ⟨3477006790215324487469447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9272018107240865299918525 3477006790215324487469447)
          ·
            refine ⟨5215510185322986731204171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3477006790215324487469447 5215510185322986731204171)
            ·
              refine ⟨7823265277984480096806257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5215510185322986731204171 7823265277984480096806257)
              ·
                refine ⟨5867448958488360072604693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7823265277984480096806257 5867448958488360072604693)
                ·
                  refine ⟨275036669929141878403345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5867448958488360072604693 275036669929141878403345)
                  ·
                    rfl

theorem cell20_602586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_602586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602586 prefixEnd_602586 := by exact prefixLift 602586
  have htrace : WordTrace (prefixWord ++ tailWord_602586) baseStart_602586 baseEnd_602586 := by
    simpa [prefixWord, tailWord_602586, baseEnd_602586] using wordTrace_append hprefix tailTrace_602586
  have hstable : (prefixWord ++ tailWord_602586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602586).length < 2 ^ (prefixWord ++ tailWord_602586).sum := by decide
  have hdescent : baseEnd_602586 < baseStart_602586 := by decide
  rcases family_descends (prefixWord ++ tailWord_602586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602593 : List Nat := [1, 2, 3, 1, 2, 2, 9]
def baseStart_602593 : Nat := 118140960795 + 602593 * 2 ^ 59
def prefixEnd_602593 : Nat := 4983230072969 + 3 ^ 40 * 602593 * 2
def baseEnd_602593 : Nat := 30559984991097885018887

theorem tailTrace_602593 : CollatzResearch.WordTrace tailWord_602593 prefixEnd_602593 30559984991097885018887 := by
  unfold tailWord_602593
  simp only [CollatzResearch.WordTrace]
  refine ⟨21978372305915950536052433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14652248203943967024034955 21978372305915950536052433)
  ·
    refine ⟨16483779229436962902039325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21978372305915950536052433 16483779229436962902039325)
    ·
      refine ⟨6181417211038861088264747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16483779229436962902039325 6181417211038861088264747)
      ·
        refine ⟨9272125816558291632397121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6181417211038861088264747 9272125816558291632397121)
        ·
          refine ⟨6954094362418718724297841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9272125816558291632397121 6954094362418718724297841)
          ·
            refine ⟨5215570771814039043223381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6954094362418718724297841 5215570771814039043223381)
            ·
              refine ⟨30559984991097885018887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5215570771814039043223381 30559984991097885018887)
              ·
                rfl

theorem cell20_602593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 9].length) (baseStart_602593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602593 prefixEnd_602593 := by exact prefixLift 602593
  have htrace : WordTrace (prefixWord ++ tailWord_602593) baseStart_602593 baseEnd_602593 := by
    simpa [prefixWord, tailWord_602593, baseEnd_602593] using wordTrace_append hprefix tailTrace_602593
  have hstable : (prefixWord ++ tailWord_602593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602593).length < 2 ^ (prefixWord ++ tailWord_602593).sum := by decide
  have hdescent : baseEnd_602593 < baseStart_602593 := by decide
  rcases family_descends (prefixWord ++ tailWord_602593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602603 : List Nat := [1, 1, 1, 1, 2, 3, 3, 6, 2]
def baseStart_602603 : Nat := 118140960795 + 602603 * 2 ^ 59
def prefixEnd_602603 : Nat := 4983230072969 + 3 ^ 40 * 602603 * 2
def baseEnd_602603 : Nat := 275044429192365374836609

theorem tailTrace_602603 : CollatzResearch.WordTrace tailWord_602603 prefixEnd_602603 275044429192365374836609 := by
  unfold tailWord_602603
  simp only [CollatzResearch.WordTrace]
  refine ⟨21978737035879722243916463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14652491357253148162610975 21978737035879722243916463)
  ·
    refine ⟨32968105553819583365874695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21978737035879722243916463 32968105553819583365874695)
    ·
      refine ⟨49452158330729375048812043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32968105553819583365874695 49452158330729375048812043)
      ·
        refine ⟨74178237496094062573218065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49452158330729375048812043 74178237496094062573218065)
        ·
          refine ⟨55633678122070546929913549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74178237496094062573218065 55633678122070546929913549)
          ·
            refine ⟨20862629295776455098717581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55633678122070546929913549 20862629295776455098717581)
            ·
              refine ⟨7823485985916170662019093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20862629295776455098717581 7823485985916170662019093)
              ·
                refine ⟨366725905589820499782145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7823485985916170662019093 366725905589820499782145)
                ·
                  refine ⟨275044429192365374836609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366725905589820499782145 275044429192365374836609)
                  ·
                    rfl

theorem cell20_602603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 2].length) (baseStart_602603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602603 prefixEnd_602603 := by exact prefixLift 602603
  have htrace : WordTrace (prefixWord ++ tailWord_602603) baseStart_602603 baseEnd_602603 := by
    simpa [prefixWord, tailWord_602603, baseEnd_602603] using wordTrace_append hprefix tailTrace_602603
  have hstable : (prefixWord ++ tailWord_602603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602603).length < 2 ^ (prefixWord ++ tailWord_602603).sum := by decide
  have hdescent : baseEnd_602603 < baseStart_602603 := by decide
  rcases family_descends (prefixWord ++ tailWord_602603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602617 : List Nat := [1, 2, 1, 3, 1, 2, 2, 5, 3]
def baseStart_602617 : Nat := 118140960795 + 602617 * 2 ^ 59
def prefixEnd_602617 : Nat := 4983230072969 + 3 ^ 40 * 602617 * 2
def baseEnd_602617 : Nat := 275050819173843548369885

theorem tailTrace_602617 : CollatzResearch.WordTrace tailWord_602617 prefixEnd_602617 275050819173843548369885 := by
  unfold tailWord_602617
  simp only [CollatzResearch.WordTrace]
  refine ⟨21979247657829002634926105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14652831771886001756617403 21979247657829002634926105)
  ·
    refine ⟨16484435743371751976194579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21979247657829002634926105 16484435743371751976194579)
    ·
      refine ⟨24726653615057627964291869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16484435743371751976194579 24726653615057627964291869)
      ·
        refine ⟨9272495105646610486609451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24726653615057627964291869 9272495105646610486609451)
        ·
          refine ⟨13908742658469915729914177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9272495105646610486609451 13908742658469915729914177)
          ·
            refine ⟨10431556993852436797435633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13908742658469915729914177 10431556993852436797435633)
            ·
              refine ⟨7823667745389327598076725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10431556993852436797435633 7823667745389327598076725)
              ·
                refine ⟨733468851130249462319693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7823667745389327598076725 733468851130249462319693)
                ·
                  refine ⟨275050819173843548369885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733468851130249462319693 275050819173843548369885)
                  ·
                    rfl

theorem cell20_602617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_602617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602617 prefixEnd_602617 := by exact prefixLift 602617
  have htrace : WordTrace (prefixWord ++ tailWord_602617) baseStart_602617 baseEnd_602617 := by
    simpa [prefixWord, tailWord_602617, baseEnd_602617] using wordTrace_append hprefix tailTrace_602617
  have hstable : (prefixWord ++ tailWord_602617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602617).length < 2 ^ (prefixWord ++ tailWord_602617).sum := by decide
  have hdescent : baseEnd_602617 < baseStart_602617 := by decide
  rcases family_descends (prefixWord ++ tailWord_602617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602630 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_602630 : Nat := 118140960795 + 602630 * 2 ^ 59
def prefixEnd_602630 : Nat := 4983230072969 + 3 ^ 40 * 602630 * 2
def baseEnd_602630 : Nat := 275056752728073280936499

theorem tailTrace_602630 : CollatzResearch.WordTrace tailWord_602630 prefixEnd_602630 275056752728073280936499 := by
  unfold tailWord_602630
  simp only [CollatzResearch.WordTrace]
  refine ⟨686866306461934557973417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14653147871187937236766229 686866306461934557973417)
  ·
    refine ⟨515149729846450918480063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 686866306461934557973417 515149729846450918480063)
    ·
      refine ⟨772724594769676377720095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 515149729846450918480063 772724594769676377720095)
      ·
        refine ⟨1159086892154514566580143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 772724594769676377720095 1159086892154514566580143)
        ·
          refine ⟨1738630338231771849870215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1159086892154514566580143 1738630338231771849870215)
          ·
            refine ⟨2607945507347657774805323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1738630338231771849870215 2607945507347657774805323)
            ·
              refine ⟨3911918261021486662207985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2607945507347657774805323 3911918261021486662207985)
              ·
                refine ⟨2933938695766114996655989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3911918261021486662207985 2933938695766114996655989)
                ·
                  refine ⟨275056752728073280936499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2933938695766114996655989 275056752728073280936499)
                  ·
                    rfl

theorem cell20_602630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_602630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602630 prefixEnd_602630 := by exact prefixLift 602630
  have htrace : WordTrace (prefixWord ++ tailWord_602630) baseStart_602630 baseEnd_602630 := by
    simpa [prefixWord, tailWord_602630, baseEnd_602630] using wordTrace_append hprefix tailTrace_602630
  have hstable : (prefixWord ++ tailWord_602630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602630).length < 2 ^ (prefixWord ++ tailWord_602630).sum := by decide
  have hdescent : baseEnd_602630 < baseStart_602630 := by decide
  rcases family_descends (prefixWord ++ tailWord_602630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602641 : List Nat := [1, 2, 2, 1, 1, 2, 2, 7, 2]
def baseStart_602641 : Nat := 118140960795 + 602641 * 2 ^ 59
def prefixEnd_602641 : Nat := 4983230072969 + 3 ^ 40 * 602641 * 2
def baseEnd_602641 : Nat := 275061773427806131569787

theorem tailTrace_602641 : CollatzResearch.WordTrace tailWord_602641 prefixEnd_602641 275061773427806131569787 := by
  unfold tailWord_602641
  simp only [CollatzResearch.WordTrace]
  refine ⟨21980123009742054733799777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14653415339828036489199851 21980123009742054733799777)
  ·
    refine ⟨16485092257306541050349833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21980123009742054733799777 16485092257306541050349833)
    ·
      refine ⟨12363819192979905787762375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16485092257306541050349833 12363819192979905787762375)
      ·
        refine ⟨18545728789469858681643563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12363819192979905787762375 18545728789469858681643563)
        ·
          refine ⟨27818593184204788022465345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18545728789469858681643563 27818593184204788022465345)
          ·
            refine ⟨20863944888153591016849009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27818593184204788022465345 20863944888153591016849009)
            ·
              refine ⟨15647958666115193262636757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20863944888153591016849009 15647958666115193262636757)
              ·
                refine ⟨366749031237074842093049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15647958666115193262636757 366749031237074842093049)
                ·
                  refine ⟨275061773427806131569787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366749031237074842093049 275061773427806131569787)
                  ·
                    rfl

theorem cell20_602641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 2].length) (baseStart_602641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602641 prefixEnd_602641 := by exact prefixLift 602641
  have htrace : WordTrace (prefixWord ++ tailWord_602641) baseStart_602641 baseEnd_602641 := by
    simpa [prefixWord, tailWord_602641, baseEnd_602641] using wordTrace_append hprefix tailTrace_602641
  have hstable : (prefixWord ++ tailWord_602641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602641).length < 2 ^ (prefixWord ++ tailWord_602641).sum := by decide
  have hdescent : baseEnd_602641 < baseStart_602641 := by decide
  rcases family_descends (prefixWord ++ tailWord_602641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602648 : List Nat := [2, 1, 2, 3, 3, 3, 6]
def baseStart_602648 : Nat := 118140960795 + 602648 * 2 ^ 59
def prefixEnd_602648 : Nat := 4983230072969 + 3 ^ 40 * 602648 * 2
def baseEnd_602648 : Nat := 30562774268727246481825

theorem tailTrace_602648 : CollatzResearch.WordTrace tailWord_602648 prefixEnd_602648 30562774268727246481825 := by
  unfold tailWord_602648
  simp only [CollatzResearch.WordTrace]
  refine ⟨10990189160358347464652299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14653585547144463286203065 10990189160358347464652299)
  ·
    refine ⟨16485283740537521196978449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10990189160358347464652299 16485283740537521196978449)
    ·
      refine ⟨12363962805403140897733837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16485283740537521196978449 12363962805403140897733837)
      ·
        refine ⟨4636486052026177836650189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12363962805403140897733837 4636486052026177836650189)
        ·
          refine ⟨1738682269509816688743821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4636486052026177836650189 1738682269509816688743821)
          ·
            refine ⟨652005851066181258278933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1738682269509816688743821 652005851066181258278933)
            ·
              refine ⟨30562774268727246481825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 652005851066181258278933 30562774268727246481825)
              ·
                rfl

theorem cell20_602648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 6].length) (baseStart_602648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602648 prefixEnd_602648 := by exact prefixLift 602648
  have htrace : WordTrace (prefixWord ++ tailWord_602648) baseStart_602648 baseEnd_602648 := by
    simpa [prefixWord, tailWord_602648, baseEnd_602648] using wordTrace_append hprefix tailTrace_602648
  have hstable : (prefixWord ++ tailWord_602648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602648).length < 2 ^ (prefixWord ++ tailWord_602648).sum := by decide
  have hdescent : baseEnd_602648 < baseStart_602648 := by decide
  rcases family_descends (prefixWord ++ tailWord_602648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602655 : List Nat := [1, 1, 2, 4, 1, 1, 1, 6, 3]
def baseStart_602655 : Nat := 118140960795 + 602655 * 2 ^ 59
def prefixEnd_602655 : Nat := 4983230072969 + 3 ^ 40 * 602655 * 2
def baseEnd_602655 : Nat := 275068163409284305103063

theorem tailTrace_602655 : CollatzResearch.WordTrace tailWord_602655 prefixEnd_602655 275068163409284305103063 := by
  unfold tailWord_602655
  simp only [CollatzResearch.WordTrace]
  refine ⟨21980633631691335124809419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14653755754460890083206279 21980633631691335124809419)
  ·
    refine ⟨32970950447537002687214129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21980633631691335124809419 32970950447537002687214129)
    ·
      refine ⟨24728212835652752015410597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32970950447537002687214129 24728212835652752015410597)
      ·
        refine ⟨4636539906684891002889487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24728212835652752015410597 4636539906684891002889487)
        ·
          refine ⟨6954809860027336504334231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4636539906684891002889487 6954809860027336504334231)
          ·
            refine ⟨10432214790041004756501347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6954809860027336504334231 10432214790041004756501347)
            ·
              refine ⟨15648322185061507134752021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10432214790041004756501347 15648322185061507134752021)
              ·
                refine ⟨733515102424758146941501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15648322185061507134752021 733515102424758146941501)
                ·
                  refine ⟨275068163409284305103063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733515102424758146941501 275068163409284305103063)
                  ·
                    rfl

theorem cell20_602655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 3].length) (baseStart_602655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602655 prefixEnd_602655 := by exact prefixLift 602655
  have htrace : WordTrace (prefixWord ++ tailWord_602655) baseStart_602655 baseEnd_602655 := by
    simpa [prefixWord, tailWord_602655, baseEnd_602655] using wordTrace_append hprefix tailTrace_602655
  have hstable : (prefixWord ++ tailWord_602655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602655).length < 2 ^ (prefixWord ++ tailWord_602655).sum := by decide
  have hdescent : baseEnd_602655 < baseStart_602655 := by decide
  rcases family_descends (prefixWord ++ tailWord_602655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602672 : List Nat := [2, 1, 1, 1, 2, 3, 6, 1, 3]
def baseStart_602672 : Nat := 118140960795 + 602672 * 2 ^ 59
def prefixEnd_602672 : Nat := 4983230072969 + 3 ^ 40 * 602672 * 2
def baseEnd_602672 : Nat := 275075922672507801536327

theorem tailTrace_602672 : CollatzResearch.WordTrace tailWord_602672 prefixEnd_602672 275075922672507801536327 := by
  unfold tailWord_602672
  simp only [CollatzResearch.WordTrace]
  refine ⟨10990626836314873514089135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14654169115086498018785513 10990626836314873514089135)
  ·
    refine ⟨16485940254472310271133703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10990626836314873514089135 16485940254472310271133703)
    ·
      refine ⟨24728910381708465406700555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16485940254472310271133703 24728910381708465406700555)
      ·
        refine ⟨37093365572562698110050833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24728910381708465406700555 37093365572562698110050833)
        ·
          refine ⟨27820024179422023582538125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37093365572562698110050833 27820024179422023582538125)
          ·
            refine ⟨10432509067283258843451797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27820024179422023582538125 10432509067283258843451797)
            ·
              refine ⟨489023862528902758286803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10432509067283258843451797 489023862528902758286803)
              ·
                refine ⟨733535793793354137430205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489023862528902758286803 733535793793354137430205)
                ·
                  refine ⟨275075922672507801536327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733535793793354137430205 275075922672507801536327)
                  ·
                    rfl

theorem cell20_602672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_602672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602672 prefixEnd_602672 := by exact prefixLift 602672
  have htrace : WordTrace (prefixWord ++ tailWord_602672) baseStart_602672 baseEnd_602672 := by
    simpa [prefixWord, tailWord_602672, baseEnd_602672] using wordTrace_append hprefix tailTrace_602672
  have hstable : (prefixWord ++ tailWord_602672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602672).length < 2 ^ (prefixWord ++ tailWord_602672).sum := by decide
  have hdescent : baseEnd_602672 < baseStart_602672 := by decide
  rcases family_descends (prefixWord ++ tailWord_602672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602755 : List Nat := [1, 1, 1, 3, 3, 1, 3, 5, 2]
def baseStart_602755 : Nat := 118140960795 + 602755 * 2 ^ 59
def prefixEnd_602755 : Nat := 4983230072969 + 3 ^ 40 * 602755 * 2
def baseEnd_602755 : Nat := 275113806134128401769321

theorem tailTrace_602755 : CollatzResearch.WordTrace tailWord_602755 prefixEnd_602755 275113806134128401769321 := by
  unfold tailWord_602755
  simp only [CollatzResearch.WordTrace]
  refine ⟨21984280931329052203449719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14656187287552701468966479 21984280931329052203449719)
  ·
    refine ⟨32976421396993578305174579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21984280931329052203449719 32976421396993578305174579)
    ·
      refine ⟨49464632095490367457761869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32976421396993578305174579 49464632095490367457761869)
      ·
        refine ⟨18549237035808887796660701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49464632095490367457761869 18549237035808887796660701)
        ·
          refine ⟨6955963888428332923747763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18549237035808887796660701 6955963888428332923747763)
          ·
            refine ⟨10433945832642499385621645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6955963888428332923747763 10433945832642499385621645)
            ·
              refine ⟨3912729687240937269608117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10433945832642499385621645 3912729687240937269608117)
              ·
                refine ⟨366818408178837869025761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3912729687240937269608117 366818408178837869025761)
                ·
                  refine ⟨275113806134128401769321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366818408178837869025761 275113806134128401769321)
                  ·
                    rfl

theorem cell20_602755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 2].length) (baseStart_602755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602755 prefixEnd_602755 := by exact prefixLift 602755
  have htrace : WordTrace (prefixWord ++ tailWord_602755) baseStart_602755 baseEnd_602755 := by
    simpa [prefixWord, tailWord_602755, baseEnd_602755] using wordTrace_append hprefix tailTrace_602755
  have hstable : (prefixWord ++ tailWord_602755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602755).length < 2 ^ (prefixWord ++ tailWord_602755).sum := by decide
  have hdescent : baseEnd_602755 < baseStart_602755 := by decide
  rcases family_descends (prefixWord ++ tailWord_602755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602762 : List Nat := [3, 1, 2, 3, 3, 1, 7]
def baseStart_602762 : Nat := 118140960795 + 602762 * 2 ^ 59
def prefixEnd_602762 : Nat := 4983230072969 + 3 ^ 40 * 602762 * 2
def baseEnd_602762 : Nat := 30568555680540832059551

theorem tailTrace_602762 : CollatzResearch.WordTrace tailWord_602762 prefixEnd_602762 30568555680540832059551 := by
  unfold tailWord_602762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5496134060575923099738635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14656357494869128265969693 5496134060575923099738635)
  ·
    refine ⟨8244201090863884649607953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5496134060575923099738635 8244201090863884649607953)
    ·
      refine ⟨6183150818147913487205965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8244201090863884649607953 6183150818147913487205965)
      ·
        refine ⟨2318681556805467557702237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6183150818147913487205965 2318681556805467557702237)
        ·
          refine ⟨869505583802050334138339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2318681556805467557702237 869505583802050334138339)
          ·
            refine ⟨1304258375703075501207509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869505583802050334138339 1304258375703075501207509)
            ·
              refine ⟨30568555680540832059551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1304258375703075501207509 30568555680540832059551)
              ·
                rfl

theorem cell20_602762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 7].length) (baseStart_602762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602762 prefixEnd_602762 := by exact prefixLift 602762
  have htrace : WordTrace (prefixWord ++ tailWord_602762) baseStart_602762 baseEnd_602762 := by
    simpa [prefixWord, tailWord_602762, baseEnd_602762] using wordTrace_append hprefix tailTrace_602762
  have hstable : (prefixWord ++ tailWord_602762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602762).length < 2 ^ (prefixWord ++ tailWord_602762).sum := by decide
  have hdescent : baseEnd_602762 < baseStart_602762 := by decide
  rcases family_descends (prefixWord ++ tailWord_602762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602772 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 4]
def baseStart_602772 : Nat := 118140960795 + 602772 * 2 ^ 59
def prefixEnd_602772 : Nat := 4983230072969 + 3 ^ 40 * 602772 * 2
def baseEnd_602772 : Nat := 275121565397351898202585

theorem tailTrace_602772 : CollatzResearch.WordTrace tailWord_602772 prefixEnd_602772 275121565397351898202585 := by
  unfold tailWord_602772
  simp only [CollatzResearch.WordTrace]
  refine ⟨10992450486133732053409285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14656600648178309404545713 10992450486133732053409285)
  ·
    refine ⟨2061084466150074760014241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10992450486133732053409285 2061084466150074760014241)
    ·
      refine ⟨1545813349612556070010681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2061084466150074760014241 1545813349612556070010681)
      ·
        refine ⟨1159360012209417052508011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1545813349612556070010681 1159360012209417052508011)
        ·
          refine ⟨1739040018314125578762017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1159360012209417052508011 1739040018314125578762017)
          ·
            refine ⟨1304280013735594184071513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1739040018314125578762017 1304280013735594184071513)
            ·
              refine ⟨978210010301695638053635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1304280013735594184071513 978210010301695638053635)
              ·
                refine ⟨1467315015452543457080453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978210010301695638053635 1467315015452543457080453)
                ·
                  refine ⟨275121565397351898202585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1467315015452543457080453 275121565397351898202585)
                  ·
                    rfl

theorem cell20_602772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_602772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602772 prefixEnd_602772 := by exact prefixLift 602772
  have htrace : WordTrace (prefixWord ++ tailWord_602772) baseStart_602772 baseEnd_602772 := by
    simpa [prefixWord, tailWord_602772, baseEnd_602772] using wordTrace_append hprefix tailTrace_602772
  have hstable : (prefixWord ++ tailWord_602772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602772).length < 2 ^ (prefixWord ++ tailWord_602772).sum := by decide
  have hdescent : baseEnd_602772 < baseStart_602772 := by decide
  rcases family_descends (prefixWord ++ tailWord_602772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602837 : List Nat := [1, 3, 2, 5, 2, 1, 2, 1, 3]
def baseStart_602837 : Nat := 118140960795 + 602837 * 2 ^ 59
def prefixEnd_602837 : Nat := 4983230072969 + 3 ^ 40 * 602837 * 2
def baseEnd_602837 : Nat := 275151233168500561035653

theorem tailTrace_602837 : CollatzResearch.WordTrace tailWord_602837 prefixEnd_602837 275151233168500561035653 := by
  unfold tailWord_602837
  simp only [CollatzResearch.WordTrace]
  refine ⟨21987271717031980207934765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14658181144687986805289843 21987271717031980207934765)
  ·
    refine ⟨8245226893886992577975537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21987271717031980207934765 8245226893886992577975537)
    ·
      refine ⟨6183920170415244433481653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8245226893886992577975537 6183920170415244433481653)
      ·
        refine ⟨579742515976429165638905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6183920170415244433481653 579742515976429165638905)
        ·
          refine ⟨434806886982321874229179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 579742515976429165638905 434806886982321874229179)
          ·
            refine ⟨652210330473482811343769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434806886982321874229179 652210330473482811343769)
            ·
              refine ⟨489157747855112108507827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 652210330473482811343769 489157747855112108507827)
              ·
                refine ⟨733736621782668162761741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489157747855112108507827 733736621782668162761741)
                ·
                  refine ⟨275151233168500561035653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733736621782668162761741 275151233168500561035653)
                  ·
                    rfl

theorem cell20_602837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_602837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602837 prefixEnd_602837 := by exact prefixLift 602837
  have htrace : WordTrace (prefixWord ++ tailWord_602837) baseStart_602837 baseEnd_602837 := by
    simpa [prefixWord, tailWord_602837, baseEnd_602837] using wordTrace_append hprefix tailTrace_602837
  have hstable : (prefixWord ++ tailWord_602837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602837).length < 2 ^ (prefixWord ++ tailWord_602837).sum := by decide
  have hdescent : baseEnd_602837 < baseStart_602837 := by decide
  rcases family_descends (prefixWord ++ tailWord_602837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602882 : List Nat := [3, 4, 1, 1, 1, 4, 2, 2, 2]
def baseStart_602882 : Nat := 118140960795 + 602882 * 2 ^ 59
def prefixEnd_602882 : Nat := 4983230072969 + 3 ^ 40 * 602882 * 2
def baseEnd_602882 : Nat := 275171772394680404535469

theorem tailTrace_602882 : CollatzResearch.WordTrace tailWord_602882 prefixEnd_602882 275171772394680404535469 := by
  unfold tailWord_602882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5497228250467238223330725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14659275334579301928881933 5497228250467238223330725)
  ·
    refine ⟨1030730296962607166874511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5497228250467238223330725 1030730296962607166874511)
    ·
      refine ⟨1546095445443910750311767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1030730296962607166874511 1546095445443910750311767)
      ·
        refine ⟨2319143168165866125467651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546095445443910750311767 2319143168165866125467651)
        ·
          refine ⟨3478714752248799188201477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2319143168165866125467651 3478714752248799188201477)
          ·
            refine ⟨652259016046649847787777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3478714752248799188201477 652259016046649847787777)
            ·
              refine ⟨489194262034987385840833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 652259016046649847787777 489194262034987385840833)
              ·
                refine ⟨366895696526240539380625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489194262034987385840833 366895696526240539380625)
                ·
                  refine ⟨275171772394680404535469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366895696526240539380625 275171772394680404535469)
                  ·
                    rfl

theorem cell20_602882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_602882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602882 prefixEnd_602882 := by exact prefixLift 602882
  have htrace : WordTrace (prefixWord ++ tailWord_602882) baseStart_602882 baseEnd_602882 := by
    simpa [prefixWord, tailWord_602882, baseEnd_602882] using wordTrace_append hprefix tailTrace_602882
  have hstable : (prefixWord ++ tailWord_602882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602882).length < 2 ^ (prefixWord ++ tailWord_602882).sum := by decide
  have hdescent : baseEnd_602882 < baseStart_602882 := by decide
  rcases family_descends (prefixWord ++ tailWord_602882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602890 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_602890 : Nat := 118140960795 + 602890 * 2 ^ 59
def prefixEnd_602890 : Nat := 4983230072969 + 3 ^ 40 * 602890 * 2
def baseEnd_602890 : Nat := 275175423812667932268769

theorem tailTrace_602890 : CollatzResearch.WordTrace tailWord_602890 prefixEnd_602890 275175423812667932268769 := by
  unfold tailWord_602890
  simp only [CollatzResearch.WordTrace]
  refine ⟨5497301196459992564903531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14659469857226646839742749 5497301196459992564903531)
  ·
    refine ⟨8245951794689988847355297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5497301196459992564903531 8245951794689988847355297)
    ·
      refine ⟨6184463846017491635516473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8245951794689988847355297 6184463846017491635516473)
      ·
        refine ⟨4638347884513118726637355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6184463846017491635516473 4638347884513118726637355)
        ·
          refine ⟨6957521826769678089956033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4638347884513118726637355 6957521826769678089956033)
          ·
            refine ⟨5218141370077258567467025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6957521826769678089956033 5218141370077258567467025)
            ·
              refine ⟨3913606027557943925600269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5218141370077258567467025 3913606027557943925600269)
              ·
                refine ⟨1467602260334228972100101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3913606027557943925600269 1467602260334228972100101)
                ·
                  refine ⟨275175423812667932268769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1467602260334228972100101 275175423812667932268769)
                  ·
                    rfl

theorem cell20_602890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_602890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602890 prefixEnd_602890 := by exact prefixLift 602890
  have htrace : WordTrace (prefixWord ++ tailWord_602890) baseStart_602890 baseEnd_602890 := by
    simpa [prefixWord, tailWord_602890, baseEnd_602890] using wordTrace_append hprefix tailTrace_602890
  have hstable : (prefixWord ++ tailWord_602890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602890).length < 2 ^ (prefixWord ++ tailWord_602890).sum := by decide
  have hdescent : baseEnd_602890 < baseStart_602890 := by decide
  rcases family_descends (prefixWord ++ tailWord_602890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602897 : List Nat := [1, 2, 2, 1, 1, 3, 5, 5]
def baseStart_602897 : Nat := 118140960795 + 602897 * 2 ^ 59
def prefixEnd_602897 : Nat := 4983230072969 + 3 ^ 40 * 602897 * 2
def baseEnd_602897 : Nat := 91726206267802339678469

theorem tailTrace_602897 : CollatzResearch.WordTrace tailWord_602897 prefixEnd_602897 91726206267802339678469 := by
  unfold tailWord_602897
  simp only [CollatzResearch.WordTrace]
  refine ⟨21989460096814610455118945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14659640064543073636745963 21989460096814610455118945)
  ·
    refine ⟨16492095072610957841339209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21989460096814610455118945 16492095072610957841339209)
    ·
      refine ⟨12369071304458218381004407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16492095072610957841339209 12369071304458218381004407)
      ·
        refine ⟨18553606956687327571506611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12369071304458218381004407 18553606956687327571506611)
        ·
          refine ⟨27830410435030991357259917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18553606956687327571506611 27830410435030991357259917)
          ·
            refine ⟨10436403913136621758972469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27830410435030991357259917 10436403913136621758972469)
            ·
              refine ⟨978412866856558289903669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10436403913136621758972469 978412866856558289903669)
              ·
                refine ⟨91726206267802339678469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 978412866856558289903669 91726206267802339678469)
                ·
                  rfl

theorem cell20_602897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 5].length) (baseStart_602897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602897 prefixEnd_602897 := by exact prefixLift 602897
  have htrace : WordTrace (prefixWord ++ tailWord_602897) baseStart_602897 baseEnd_602897 := by
    simpa [prefixWord, tailWord_602897, baseEnd_602897] using wordTrace_append hprefix tailTrace_602897
  have hstable : (prefixWord ++ tailWord_602897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602897).length < 2 ^ (prefixWord ++ tailWord_602897).sum := by decide
  have hdescent : baseEnd_602897 < baseStart_602897 := by decide
  rcases family_descends (prefixWord ++ tailWord_602897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602904 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_602904 : Nat := 118140960795 + 602904 * 2 ^ 59
def prefixEnd_602904 : Nat := 4983230072969 + 3 ^ 40 * 602904 * 2
def baseEnd_602904 : Nat := 275181813794146105802045

theorem tailTrace_602904 : CollatzResearch.WordTrace tailWord_602904 prefixEnd_602904 275181813794146105802045 := by
  unfold tailWord_602904
  simp only [CollatzResearch.WordTrace]
  refine ⟨10994857703894625325311883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14659810271859500433749177 10994857703894625325311883)
  ·
    refine ⟨16492286555841937987967825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10994857703894625325311883 16492286555841937987967825)
    ·
      refine ⟨12369214916881453490975869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16492286555841937987967825 12369214916881453490975869)
      ·
        refine ⟨4638455593830545059115951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12369214916881453490975869 4638455593830545059115951)
        ·
          refine ⟨6957683390745817588673927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4638455593830545059115951 6957683390745817588673927)
          ·
            refine ⟨10436525086118726383010891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6957683390745817588673927 10436525086118726383010891)
            ·
              refine ⟨15654787629178089574516337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10436525086118726383010891 15654787629178089574516337)
              ·
                refine ⟨11741090721883567180887253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15654787629178089574516337 11741090721883567180887253)
                ·
                  refine ⟨275181813794146105802045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11741090721883567180887253 275181813794146105802045)
                  ·
                    rfl

theorem cell20_602904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_602904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602904 prefixEnd_602904 := by exact prefixLift 602904
  have htrace : WordTrace (prefixWord ++ tailWord_602904) baseStart_602904 baseEnd_602904 := by
    simpa [prefixWord, tailWord_602904, baseEnd_602904] using wordTrace_append hprefix tailTrace_602904
  have hstable : (prefixWord ++ tailWord_602904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602904).length < 2 ^ (prefixWord ++ tailWord_602904).sum := by decide
  have hdescent : baseEnd_602904 < baseStart_602904 := by decide
  rcases family_descends (prefixWord ++ tailWord_602904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602934 : List Nat := [5, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_602934 : Nat := 118140960795 + 602934 * 2 ^ 59
def prefixEnd_602934 : Nat := 4983230072969 + 3 ^ 40 * 602934 * 2
def baseEnd_602934 : Nat := 275195506611599334801923

theorem tailTrace_602934 : CollatzResearch.WordTrace tailWord_602934 prefixEnd_602934 275195506611599334801923 := by
  unfold tailWord_602934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1374425599855035360888491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14660539731787043849477237 1374425599855035360888491)
  ·
    refine ⟨2061638399782553041332737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1374425599855035360888491 2061638399782553041332737)
    ·
      refine ⟨1546228799836914780999553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2061638399782553041332737 1546228799836914780999553)
      ·
        refine ⟨1159671599877686085749665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1546228799836914780999553 1159671599877686085749665)
        ·
          refine ⟨869753699908264564312249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1159671599877686085749665 869753699908264564312249)
          ·
            refine ⟨652315274931198423234187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 869753699908264564312249 652315274931198423234187)
            ·
              refine ⟨978472912396797634851281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652315274931198423234187 978472912396797634851281)
              ·
                refine ⟨733854684297598226138461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 978472912396797634851281 733854684297598226138461)
                ·
                  refine ⟨275195506611599334801923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733854684297598226138461 275195506611599334801923)
                  ·
                    rfl

theorem cell20_602934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_602934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602934 prefixEnd_602934 := by exact prefixLift 602934
  have htrace : WordTrace (prefixWord ++ tailWord_602934) baseStart_602934 baseEnd_602934 := by
    simpa [prefixWord, tailWord_602934, baseEnd_602934] using wordTrace_append hprefix tailTrace_602934
  have hstable : (prefixWord ++ tailWord_602934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602934).length < 2 ^ (prefixWord ++ tailWord_602934).sum := by decide
  have hdescent : baseEnd_602934 < baseStart_602934 := by decide
  rcases family_descends (prefixWord ++ tailWord_602934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602987 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 6]
def baseStart_602987 : Nat := 118140960795 + 602987 * 2 ^ 59
def prefixEnd_602987 : Nat := 4983230072969 + 3 ^ 40 * 602987 * 2
def baseEnd_602987 : Nat := 275219697255766706035039

theorem tailTrace_602987 : CollatzResearch.WordTrace tailWord_602987 prefixEnd_602987 275219697255766706035039 := by
  unfold tailWord_602987
  simp only [CollatzResearch.WordTrace]
  refine ⟨21992742666488555825895215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14661828444325703883930143 21992742666488555825895215)
  ·
    refine ⟨32989113999732833738842823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21992742666488555825895215 32989113999732833738842823)
    ·
      refine ⟨49483670999599250608264235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32989113999732833738842823 49483670999599250608264235)
      ·
        refine ⟨74225506499398875912396353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49483670999599250608264235 74225506499398875912396353)
        ·
          refine ⟨55669129874549156934297265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74225506499398875912396353 55669129874549156934297265)
          ·
            refine ⟨41751847405911867700722949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55669129874549156934297265 41751847405911867700722949)
            ·
              refine ⟨7828471388608475193885553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41751847405911867700722949 7828471388608475193885553)
              ·
                refine ⟨5871353541456356395414165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7828471388608475193885553 5871353541456356395414165)
                ·
                  refine ⟨275219697255766706035039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5871353541456356395414165 275219697255766706035039)
                  ·
                    rfl

theorem cell20_602987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_602987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602987 prefixEnd_602987 := by exact prefixLift 602987
  have htrace : WordTrace (prefixWord ++ tailWord_602987) baseStart_602987 baseEnd_602987 := by
    simpa [prefixWord, tailWord_602987, baseEnd_602987] using wordTrace_append hprefix tailTrace_602987
  have hstable : (prefixWord ++ tailWord_602987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602987).length < 2 ^ (prefixWord ++ tailWord_602987).sum := by decide
  have hdescent : baseEnd_602987 < baseStart_602987 := by decide
  rcases family_descends (prefixWord ++ tailWord_602987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602997 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 5]
def baseStart_602997 : Nat := 118140960795 + 602997 * 2 ^ 59
def prefixEnd_602997 : Nat := 4983230072969 + 3 ^ 40 * 602997 * 2
def baseEnd_602997 : Nat := 275224261528251115701665

theorem tailTrace_602997 : CollatzResearch.WordTrace tailWord_602997 prefixEnd_602997 275224261528251115701665 := by
  unfold tailWord_602997
  simp only [CollatzResearch.WordTrace]
  refine ⟨21993107396452327533759245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14662071597634885022506163 21993107396452327533759245)
  ·
    refine ⟨8247415273669622825159717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21993107396452327533759245 8247415273669622825159717)
    ·
      refine ⟨1546390363813054279717447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8247415273669622825159717 1546390363813054279717447)
      ·
        refine ⟨2319585545719581419576171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546390363813054279717447 2319585545719581419576171)
        ·
          refine ⟨3479378318579372129364257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2319585545719581419576171 3479378318579372129364257)
          ·
            refine ⟨2609533738934529097023193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3479378318579372129364257 2609533738934529097023193)
            ·
              refine ⟨1957150304200896822767395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2609533738934529097023193 1957150304200896822767395)
              ·
                refine ⟨2935725456301345234151093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957150304200896822767395 2935725456301345234151093)
                ·
                  refine ⟨275224261528251115701665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2935725456301345234151093 275224261528251115701665)
                  ·
                    rfl

theorem cell20_602997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_602997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_602997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_602997 prefixEnd_602997 := by exact prefixLift 602997
  have htrace : WordTrace (prefixWord ++ tailWord_602997) baseStart_602997 baseEnd_602997 := by
    simpa [prefixWord, tailWord_602997, baseEnd_602997] using wordTrace_append hprefix tailTrace_602997
  have hstable : (prefixWord ++ tailWord_602997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602997).length < 2 ^ (prefixWord ++ tailWord_602997).sum := by decide
  have hdescent : baseEnd_602997 < baseStart_602997 := by decide
  rcases family_descends (prefixWord ++ tailWord_602997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603010 : List Nat := [3, 4, 2, 2, 1, 1, 1, 3, 3]
def baseStart_603010 : Nat := 118140960795 + 603010 * 2 ^ 59
def prefixEnd_603010 : Nat := 4983230072969 + 3 ^ 40 * 603010 * 2
def baseEnd_603010 : Nat := 275230195082480848268279

theorem tailTrace_603010 : CollatzResearch.WordTrace tailWord_603010 prefixEnd_603010 275230195082480848268279 := by
  unfold tailWord_603010
  simp only [CollatzResearch.WordTrace]
  refine ⟨5498395386351307688495621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14662387696936820502654989 5498395386351307688495621)
  ·
    refine ⟨1030949134940870191592929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5498395386351307688495621 1030949134940870191592929)
    ·
      refine ⟨773211851205652643694697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1030949134940870191592929 773211851205652643694697)
      ·
        refine ⟨579908888404239482771023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 773211851205652643694697 579908888404239482771023)
        ·
          refine ⟨869863332606359224156535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579908888404239482771023 869863332606359224156535)
          ·
            refine ⟨1304794998909538836234803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869863332606359224156535 1304794998909538836234803)
            ·
              refine ⟨1957192498364308254352205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304794998909538836234803 1957192498364308254352205)
              ·
                refine ⟨733947186886615595382077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1957192498364308254352205 733947186886615595382077)
                ·
                  refine ⟨275230195082480848268279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733947186886615595382077 275230195082480848268279)
                  ·
                    rfl

theorem cell20_603010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_603010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603010 prefixEnd_603010 := by exact prefixLift 603010
  have htrace : WordTrace (prefixWord ++ tailWord_603010) baseStart_603010 baseEnd_603010 := by
    simpa [prefixWord, tailWord_603010, baseEnd_603010] using wordTrace_append hprefix tailTrace_603010
  have hstable : (prefixWord ++ tailWord_603010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603010).length < 2 ^ (prefixWord ++ tailWord_603010).sum := by decide
  have hdescent : baseEnd_603010 < baseStart_603010 := by decide
  rcases family_descends (prefixWord ++ tailWord_603010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603011 : List Nat := [1, 1, 1, 3, 4, 1, 4, 5]
def baseStart_603011 : Nat := 118140960795 + 603011 * 2 ^ 59
def prefixEnd_603011 : Nat := 4983230072969 + 3 ^ 40 * 603011 * 2
def baseEnd_603011 : Nat := 91743550503243096411647

theorem tailTrace_603011 : CollatzResearch.WordTrace tailWord_603011 prefixEnd_603011 91743550503243096411647 := by
  unfold tailWord_603011
  simp only [CollatzResearch.WordTrace]
  refine ⟨21993618018401607924768887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14662412012267738616512591 21993618018401607924768887)
  ·
    refine ⟨32990427027602411887153331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21993618018401607924768887 32990427027602411887153331)
    ·
      refine ⟨49485640541403617830729997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32990427027602411887153331 49485640541403617830729997)
      ·
        refine ⟨18557115203026356686523749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49485640541403617830729997 18557115203026356686523749)
        ·
          refine ⟨3479459100567441878723203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18557115203026356686523749 3479459100567441878723203)
          ·
            refine ⟨5219188650851162818084805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3479459100567441878723203 5219188650851162818084805)
            ·
              refine ⟨978597872034593028390901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5219188650851162818084805 978597872034593028390901)
              ·
                refine ⟨91743550503243096411647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 978597872034593028390901 91743550503243096411647)
                ·
                  rfl

theorem cell20_603011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 5].length) (baseStart_603011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603011 prefixEnd_603011 := by exact prefixLift 603011
  have htrace : WordTrace (prefixWord ++ tailWord_603011) baseStart_603011 baseEnd_603011 := by
    simpa [prefixWord, tailWord_603011, baseEnd_603011] using wordTrace_append hprefix tailTrace_603011
  have hstable : (prefixWord ++ tailWord_603011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603011).length < 2 ^ (prefixWord ++ tailWord_603011).sum := by decide
  have hdescent : baseEnd_603011 < baseStart_603011 := by decide
  rcases family_descends (prefixWord ++ tailWord_603011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603025 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 6]
def baseStart_603025 : Nat := 118140960795 + 603025 * 2 ^ 59
def prefixEnd_603025 : Nat := 4983230072969 + 3 ^ 40 * 603025 * 2
def baseEnd_603025 : Nat := 275237041491207462768217

theorem tailTrace_603025 : CollatzResearch.WordTrace tailWord_603025 prefixEnd_603025 275237041491207462768217 := by
  unfold tailWord_603025
  simp only [CollatzResearch.WordTrace]
  refine ⟨21994128640350888315778529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14662752426900592210519019 21994128640350888315778529)
  ·
    refine ⟨16495596480263166236833897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21994128640350888315778529 16495596480263166236833897)
    ·
      refine ⟨12371697360197374677625423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16495596480263166236833897 12371697360197374677625423)
      ·
        refine ⟨18557546040296062016438135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12371697360197374677625423 18557546040296062016438135)
        ·
          refine ⟨27836319060444093024657203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18557546040296062016438135 27836319060444093024657203)
          ·
            refine ⟨41754478590666139536985805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27836319060444093024657203 41754478590666139536985805)
            ·
              refine ⟨15657929471499802326369677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41754478590666139536985805 15657929471499802326369677)
              ·
                refine ⟨5871723551812425872388629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15657929471499802326369677 5871723551812425872388629)
                ·
                  refine ⟨275237041491207462768217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5871723551812425872388629 275237041491207462768217)
                  ·
                    rfl

theorem cell20_603025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_603025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603025 prefixEnd_603025 := by exact prefixLift 603025
  have htrace : WordTrace (prefixWord ++ tailWord_603025) baseStart_603025 baseEnd_603025 := by
    simpa [prefixWord, tailWord_603025, baseEnd_603025] using wordTrace_append hprefix tailTrace_603025
  have hstable : (prefixWord ++ tailWord_603025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603025).length < 2 ^ (prefixWord ++ tailWord_603025).sum := by decide
  have hdescent : baseEnd_603025 < baseStart_603025 := by decide
  rcases family_descends (prefixWord ++ tailWord_603025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603076 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 4]
def baseStart_603076 : Nat := 118140960795 + 603076 * 2 ^ 59
def prefixEnd_603076 : Nat := 4983230072969 + 3 ^ 40 * 603076 * 2
def baseEnd_603076 : Nat := 275260319280877952068009

theorem tailTrace_603076 : CollatzResearch.WordTrace tailWord_603076 prefixEnd_603076 275260319280877952068009 := by
  unfold tailWord_603076
  simp only [CollatzResearch.WordTrace]
  refine ⟨10997994381583062012942541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14663992508777416017256721 10997994381583062012942541)
  ·
    refine ⟨4124247893093648254853453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10997994381583062012942541 4124247893093648254853453)
    ·
      refine ⟨1546592959910118095570045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4124247893093648254853453 1546592959910118095570045)
      ·
        refine ⟨579972359966294285838767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1546592959910118095570045 579972359966294285838767)
        ·
          refine ⟨869958539949441428758151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579972359966294285838767 869958539949441428758151)
          ·
            refine ⟨1304937809924162143137227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869958539949441428758151 1304937809924162143137227)
            ·
              refine ⟨1957406714886243214705841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304937809924162143137227 1957406714886243214705841)
              ·
                refine ⟨1468055036164682411029381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1957406714886243214705841 1468055036164682411029381)
                ·
                  refine ⟨275260319280877952068009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1468055036164682411029381 275260319280877952068009)
                  ·
                    rfl

theorem cell20_603076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_603076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603076 prefixEnd_603076 := by exact prefixLift 603076
  have htrace : WordTrace (prefixWord ++ tailWord_603076) baseStart_603076 baseEnd_603076 := by
    simpa [prefixWord, tailWord_603076, baseEnd_603076] using wordTrace_append hprefix tailTrace_603076
  have hstable : (prefixWord ++ tailWord_603076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603076).length < 2 ^ (prefixWord ++ tailWord_603076).sum := by decide
  have hdescent : baseEnd_603076 < baseStart_603076 := by decide
  rcases family_descends (prefixWord ++ tailWord_603076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603097 : List Nat := [1, 2, 1, 2, 5, 1, 1, 5, 2]
def baseStart_603097 : Nat := 118140960795 + 603097 * 2 ^ 59
def prefixEnd_603097 : Nat := 4983230072969 + 3 ^ 40 * 603097 * 2
def baseEnd_603097 : Nat := 275269904253095212367923

theorem tailTrace_603097 : CollatzResearch.WordTrace tailWord_603097 prefixEnd_603097 275269904253095212367923 := by
  unfold tailWord_603097
  simp only [CollatzResearch.WordTrace]
  refine ⟨21996754696090044612399545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14664503130726696408266363 21996754696090044612399545)
  ·
    refine ⟨16497566022067533459299659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21996754696090044612399545 16497566022067533459299659)
    ·
      refine ⟨24746349033101300188949489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16497566022067533459299659 24746349033101300188949489)
      ·
        refine ⟨18559761774825975141712117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24746349033101300188949489 18559761774825975141712117)
        ·
          refine ⟨1739977666389935169535511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18559761774825975141712117 1739977666389935169535511)
          ·
            refine ⟨2609966499584902754303267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1739977666389935169535511 2609966499584902754303267)
            ·
              refine ⟨3914949749377354131454901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2609966499584902754303267 3914949749377354131454901)
              ·
                refine ⟨367026539004126949823897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3914949749377354131454901 367026539004126949823897)
                ·
                  refine ⟨275269904253095212367923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367026539004126949823897 275269904253095212367923)
                  ·
                    rfl

theorem cell20_603097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 2].length) (baseStart_603097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603097 prefixEnd_603097 := by exact prefixLift 603097
  have htrace : WordTrace (prefixWord ++ tailWord_603097) baseStart_603097 baseEnd_603097 := by
    simpa [prefixWord, tailWord_603097, baseEnd_603097] using wordTrace_append hprefix tailTrace_603097
  have hstable : (prefixWord ++ tailWord_603097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603097).length < 2 ^ (prefixWord ++ tailWord_603097).sum := by decide
  have hdescent : baseEnd_603097 < baseStart_603097 := by decide
  rcases family_descends (prefixWord ++ tailWord_603097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603111 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 5]
def baseStart_603111 : Nat := 118140960795 + 603111 * 2 ^ 59
def prefixEnd_603111 : Nat := 4983230072969 + 3 ^ 40 * 603111 * 2
def baseEnd_603111 : Nat := 275276294234573385901199

theorem tailTrace_603111 : CollatzResearch.WordTrace tailWord_603111 prefixEnd_603111 275276294234573385901199 := by
  unfold tailWord_603111
  simp only [CollatzResearch.WordTrace]
  refine ⟨21997265318039325003409187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14664843545359550002272791 21997265318039325003409187)
  ·
    refine ⟨32995897977058987505113781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21997265318039325003409187 32995897977058987505113781)
    ·
      refine ⟨3093365435349280078604417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32995897977058987505113781 3093365435349280078604417)
      ·
        refine ⟨2320024076511960058953313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3093365435349280078604417 2320024076511960058953313)
        ·
          refine ⟨1740018057383970044214985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2320024076511960058953313 1740018057383970044214985)
          ·
            refine ⟨1305013543037977533161239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1740018057383970044214985 1305013543037977533161239)
            ·
              refine ⟨1957520314556966299741859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305013543037977533161239 1957520314556966299741859)
              ·
                refine ⟨2936280471835449449612789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957520314556966299741859 2936280471835449449612789)
                ·
                  refine ⟨275276294234573385901199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2936280471835449449612789 275276294234573385901199)
                  ·
                    rfl

theorem cell20_603111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_603111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603111 prefixEnd_603111 := by exact prefixLift 603111
  have htrace : WordTrace (prefixWord ++ tailWord_603111) baseStart_603111 baseEnd_603111 := by
    simpa [prefixWord, tailWord_603111, baseEnd_603111] using wordTrace_append hprefix tailTrace_603111
  have hstable : (prefixWord ++ tailWord_603111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603111).length < 2 ^ (prefixWord ++ tailWord_603111).sum := by decide
  have hdescent : baseEnd_603111 < baseStart_603111 := by decide
  rcases family_descends (prefixWord ++ tailWord_603111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603239 : List Nat := [1, 1, 5, 1, 1, 3, 3, 5]
def baseStart_603239 : Nat := 118140960795 + 603239 * 2 ^ 59
def prefixEnd_603239 : Nat := 4983230072969 + 3 ^ 40 * 603239 * 2
def baseEnd_603239 : Nat := 91778238974124609878003

theorem tailTrace_603239 : CollatzResearch.WordTrace tailWord_603239 prefixEnd_603239 91778238974124609878003 := by
  unfold tailWord_603239
  simp only [CollatzResearch.WordTrace]
  refine ⟨22001933861575602864068771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14667955907717068576045847 22001933861575602864068771)
  ·
    refine ⟨33002900792363404296103157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22001933861575602864068771 33002900792363404296103157)
    ·
      refine ⟨3094021949284069152759671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33002900792363404296103157 3094021949284069152759671)
      ·
        refine ⟨4641032923926103729139507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3094021949284069152759671 4641032923926103729139507)
        ·
          refine ⟨6961549385889155593709261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4641032923926103729139507 6961549385889155593709261)
          ·
            refine ⟨2610581019708433347640973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6961549385889155593709261 2610581019708433347640973)
            ·
              refine ⟨978967882390662505365365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2610581019708433347640973 978967882390662505365365)
              ·
                refine ⟨91778238974124609878003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 978967882390662505365365 91778238974124609878003)
                ·
                  rfl

theorem cell20_603239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 5].length) (baseStart_603239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603239 prefixEnd_603239 := by exact prefixLift 603239
  have htrace : WordTrace (prefixWord ++ tailWord_603239) baseStart_603239 baseEnd_603239 := by
    simpa [prefixWord, tailWord_603239, baseEnd_603239] using wordTrace_append hprefix tailTrace_603239
  have hstable : (prefixWord ++ tailWord_603239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603239).length < 2 ^ (prefixWord ++ tailWord_603239).sum := by decide
  have hdescent : baseEnd_603239 < baseStart_603239 := by decide
  rcases family_descends (prefixWord ++ tailWord_603239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603287 : List Nat := [1, 1, 3, 3, 3, 1, 2, 4, 2]
def baseStart_603287 : Nat := 118140960795 + 603287 * 2 ^ 59
def prefixEnd_603287 : Nat := 4983230072969 + 3 ^ 40 * 603287 * 2
def baseEnd_603287 : Nat := 275356625430298996033813

theorem tailTrace_603287 : CollatzResearch.WordTrace tailWord_603287 prefixEnd_603287 275356625430298996033813 := by
  unfold tailWord_603287
  simp only [CollatzResearch.WordTrace]
  refine ⟨22003684565401707061816115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14669123043601138041210743 22003684565401707061816115)
  ·
    refine ⟨33005526848102560592724173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22003684565401707061816115 33005526848102560592724173)
    ·
      refine ⟨12377072568038460222271565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33005526848102560592724173 12377072568038460222271565)
      ·
        refine ⟨4641402213014422583351837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12377072568038460222271565 4641402213014422583351837)
        ·
          refine ⟨1740525829880408468756939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4641402213014422583351837 1740525829880408468756939)
          ·
            refine ⟨2610788744820612703135409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740525829880408468756939 2610788744820612703135409)
            ·
              refine ⟨1958091558615459527351557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2610788744820612703135409 1958091558615459527351557)
              ·
                refine ⟨367142167240398661378417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1958091558615459527351557 367142167240398661378417)
                ·
                  refine ⟨275356625430298996033813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367142167240398661378417 275356625430298996033813)
                  ·
                    rfl

theorem cell20_603287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 2].length) (baseStart_603287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603287 prefixEnd_603287 := by exact prefixLift 603287
  have htrace : WordTrace (prefixWord ++ tailWord_603287) baseStart_603287 baseEnd_603287 := by
    simpa [prefixWord, tailWord_603287, baseEnd_603287] using wordTrace_append hprefix tailTrace_603287
  have hstable : (prefixWord ++ tailWord_603287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603287).length < 2 ^ (prefixWord ++ tailWord_603287).sum := by decide
  have hdescent : baseEnd_603287 < baseStart_603287 := by decide
  rcases family_descends (prefixWord ++ tailWord_603287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603315 : List Nat := [1, 1, 1, 2, 3, 2, 6, 4]
def baseStart_603315 : Nat := 118140960795 + 603315 * 2 ^ 59
def prefixEnd_603315 : Nat := 4983230072969 + 3 ^ 40 * 603315 * 2
def baseEnd_603315 : Nat := 91789801797751781033455

theorem tailTrace_603315 : CollatzResearch.WordTrace tailWord_603315 prefixEnd_603315 91789801797751781033455 := by
  unfold tailWord_603315
  simp only [CollatzResearch.WordTrace]
  refine ⟨22004705809300267843835399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14669803872866845229223599 22004705809300267843835399)
  ·
    refine ⟨33007058713950401765753099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22004705809300267843835399 33007058713950401765753099)
    ·
      refine ⟨49510588070925602648629649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33007058713950401765753099 49510588070925602648629649)
      ·
        refine ⟨37132941053194201986472237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49510588070925602648629649 37132941053194201986472237)
        ·
          refine ⟨13924852894947825744927089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37132941053194201986472237 13924852894947825744927089)
          ·
            refine ⟨10443639671210869308695317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13924852894947825744927089 10443639671210869308695317)
            ·
              refine ⟨489545609588009498845093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10443639671210869308695317 489545609588009498845093)
              ·
                refine ⟨91789801797751781033455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 489545609588009498845093 91789801797751781033455)
                ·
                  rfl

theorem cell20_603315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 4].length) (baseStart_603315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603315 prefixEnd_603315 := by exact prefixLift 603315
  have htrace : WordTrace (prefixWord ++ tailWord_603315) baseStart_603315 baseEnd_603315 := by
    simpa [prefixWord, tailWord_603315, baseEnd_603315] using wordTrace_append hprefix tailTrace_603315
  have hstable : (prefixWord ++ tailWord_603315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603315).length < 2 ^ (prefixWord ++ tailWord_603315).sum := by decide
  have hdescent : baseEnd_603315 < baseStart_603315 := by decide
  rcases family_descends (prefixWord ++ tailWord_603315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603325 : List Nat := [1, 4, 1, 2, 1, 1, 5, 3, 2]
def baseStart_603325 : Nat := 118140960795 + 603325 * 2 ^ 59
def prefixEnd_603325 : Nat := 4983230072969 + 3 ^ 40 * 603325 * 2
def baseEnd_603325 : Nat := 275373969665739752766991

theorem tailTrace_603325 : CollatzResearch.WordTrace tailWord_603325 prefixEnd_603325 275373969665739752766991 := by
  unfold tailWord_603325
  simp only [CollatzResearch.WordTrace]
  refine ⟨22005070539264039551699429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14670047026176026367799619 22005070539264039551699429)
  ·
    refine ⟨4125950726112007415943643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22005070539264039551699429 4125950726112007415943643)
    ·
      refine ⟨6188926089168011123915465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4125950726112007415943643 6188926089168011123915465)
      ·
        refine ⟨4641694566876008342936599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6188926089168011123915465 4641694566876008342936599)
        ·
          refine ⟨6962541850314012514404899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4641694566876008342936599 6962541850314012514404899)
          ·
            refine ⟨10443812775471018771607349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6962541850314012514404899 10443812775471018771607349)
            ·
              refine ⟨979107447700408009838189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10443812775471018771607349 979107447700408009838189)
              ·
                refine ⟨367165292887653003689321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 979107447700408009838189 367165292887653003689321)
                ·
                  refine ⟨275373969665739752766991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367165292887653003689321 275373969665739752766991)
                  ·
                    rfl

theorem cell20_603325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_603325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603325 prefixEnd_603325 := by exact prefixLift 603325
  have htrace : WordTrace (prefixWord ++ tailWord_603325) baseStart_603325 baseEnd_603325 := by
    simpa [prefixWord, tailWord_603325, baseEnd_603325] using wordTrace_append hprefix tailTrace_603325
  have hstable : (prefixWord ++ tailWord_603325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603325).length < 2 ^ (prefixWord ++ tailWord_603325).sum := by decide
  have hdescent : baseEnd_603325 < baseStart_603325 := by decide
  rcases family_descends (prefixWord ++ tailWord_603325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603332 : List Nat := [2, 3, 3, 1, 3, 2, 6]
def baseStart_603332 : Nat := 118140960795 + 603332 * 2 ^ 59
def prefixEnd_603332 : Nat := 4983230072969 + 3 ^ 40 * 603332 * 2
def baseEnd_603332 : Nat := 30597462739608759948181

theorem tailTrace_603332 : CollatzResearch.WordTrace tailWord_603332 prefixEnd_603332 30597462739608759948181 := by
  unfold tailWord_603332
  simp only [CollatzResearch.WordTrace]
  refine ⟨11002662925119339873602125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14670217233492453164802833 11002662925119339873602125)
  ·
    refine ⟨4125998596919752452600797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11002662925119339873602125 4125998596919752452600797)
    ·
      refine ⟨1547249473844907169725299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4125998596919752452600797 1547249473844907169725299)
      ·
        refine ⟨2320874210767360754587949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1547249473844907169725299 2320874210767360754587949)
        ·
          refine ⟨870327829037760282970481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2320874210767360754587949 870327829037760282970481)
          ·
            refine ⟨652745871778320212227861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 870327829037760282970481 652745871778320212227861)
            ·
              refine ⟨30597462739608759948181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 652745871778320212227861 30597462739608759948181)
              ·
                rfl

theorem cell20_603332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 6].length) (baseStart_603332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603332 prefixEnd_603332 := by exact prefixLift 603332
  have htrace : WordTrace (prefixWord ++ tailWord_603332) baseStart_603332 baseEnd_603332 := by
    simpa [prefixWord, tailWord_603332, baseEnd_603332] using wordTrace_append hprefix tailTrace_603332
  have hstable : (prefixWord ++ tailWord_603332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603332).length < 2 ^ (prefixWord ++ tailWord_603332).sum := by decide
  have hdescent : baseEnd_603332 < baseStart_603332 := by decide
  rcases family_descends (prefixWord ++ tailWord_603332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603336 : List Nat := [2, 1, 3, 1, 2, 1, 10]
def baseStart_603336 : Nat := 118140960795 + 603336 * 2 ^ 59
def prefixEnd_603336 : Nat := 4983230072969 + 3 ^ 40 * 603336 * 2
def baseEnd_603336 : Nat := 30597665596163622600031

theorem tailTrace_603336 : CollatzResearch.WordTrace tailWord_603336 prefixEnd_603336 30597665596163622600031 := by
  unfold tailWord_603336
  simp only [CollatzResearch.WordTrace]
  refine ⟨11002735871112094215174931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14670314494816125620233241 11002735871112094215174931)
  ·
    refine ⟨16504103806668141322762397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11002735871112094215174931 16504103806668141322762397)
    ·
      refine ⟨6189038927500552996035899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16504103806668141322762397 6189038927500552996035899)
      ·
        refine ⟨9283558391250829494053849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6189038927500552996035899 9283558391250829494053849)
        ·
          refine ⟨6962668793438122120540387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9283558391250829494053849 6962668793438122120540387)
          ·
            refine ⟨10444003190157183180810581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6962668793438122120540387 10444003190157183180810581)
            ·
              refine ⟨30597665596163622600031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10444003190157183180810581 30597665596163622600031)
              ·
                rfl

theorem cell20_603336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 10].length) (baseStart_603336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603336 prefixEnd_603336 := by exact prefixLift 603336
  have htrace : WordTrace (prefixWord ++ tailWord_603336) baseStart_603336 baseEnd_603336 := by
    simpa [prefixWord, tailWord_603336, baseEnd_603336] using wordTrace_append hprefix tailTrace_603336
  have hstable : (prefixWord ++ tailWord_603336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603336).length < 2 ^ (prefixWord ++ tailWord_603336).sum := by decide
  have hdescent : baseEnd_603336 < baseStart_603336 := by decide
  rcases family_descends (prefixWord ++ tailWord_603336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603342 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_603342 : Nat := 118140960795 + 603342 * 2 ^ 59
def prefixEnd_603342 : Nat := 4983230072969 + 3 ^ 40 * 603342 * 2
def baseEnd_603342 : Nat := 275381728928963249200255

theorem tailTrace_603342 : CollatzResearch.WordTrace tailWord_603342 prefixEnd_603342 275381728928963249200255 := by
  unfold tailWord_603342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2750711322525306431883535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14670460386801634303378853 2750711322525306431883535)
  ·
    refine ⟨4126066983787959647825303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2750711322525306431883535 4126066983787959647825303)
    ·
      refine ⟨6189100475681939471737955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4126066983787959647825303 6189100475681939471737955)
      ·
        refine ⟨9283650713522909207606933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6189100475681939471737955 9283650713522909207606933)
        ·
          refine ⟨435171127196386369106575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9283650713522909207606933 435171127196386369106575)
          ·
            refine ⟨652756690794579553659863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435171127196386369106575 652756690794579553659863)
            ·
              refine ⟨979135036191869330489795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652756690794579553659863 979135036191869330489795)
              ·
                refine ⟨1468702554287803995734693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979135036191869330489795 1468702554287803995734693)
                ·
                  refine ⟨275381728928963249200255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1468702554287803995734693 275381728928963249200255)
                  ·
                    rfl

theorem cell20_603342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_603342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603342 prefixEnd_603342 := by exact prefixLift 603342
  have htrace : WordTrace (prefixWord ++ tailWord_603342) baseStart_603342 baseEnd_603342 := by
    simpa [prefixWord, tailWord_603342, baseEnd_603342] using wordTrace_append hprefix tailTrace_603342
  have hstable : (prefixWord ++ tailWord_603342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603342).length < 2 ^ (prefixWord ++ tailWord_603342).sum := by decide
  have hdescent : baseEnd_603342 < baseStart_603342 := by decide
  rcases family_descends (prefixWord ++ tailWord_603342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603419 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 7]
def baseStart_603419 : Nat := 118140960795 + 603419 * 2 ^ 59
def prefixEnd_603419 : Nat := 4983230072969 + 3 ^ 40 * 603419 * 2
def baseEnd_603419 : Nat := 275416873827093203633273

theorem tailTrace_603419 : CollatzResearch.WordTrace tailWord_603419 prefixEnd_603419 275416873827093203633273 := by
  unfold tailWord_603419
  simp only [CollatzResearch.WordTrace]
  refine ⟨22008499000923493605621311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14672332667282329070414207 22008499000923493605621311)
  ·
    refine ⟨33012748501385240408431967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22008499000923493605621311 33012748501385240408431967)
    ·
      refine ⟨49519122752077860612647951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33012748501385240408431967 49519122752077860612647951)
      ·
        refine ⟨74278684128116790918971927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49519122752077860612647951 74278684128116790918971927)
        ·
          refine ⟨111418026192175186378457891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74278684128116790918971927 111418026192175186378457891)
          ·
            refine ⟨167127039288262779567686837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111418026192175186378457891 167127039288262779567686837)
            ·
              refine ⟨15668159933274635584470641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167127039288262779567686837 15668159933274635584470641)
              ·
                refine ⟨11751119949955976688352981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15668159933274635584470641 11751119949955976688352981)
                ·
                  refine ⟨275416873827093203633273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11751119949955976688352981 275416873827093203633273)
                  ·
                    rfl

theorem cell20_603419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_603419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603419 prefixEnd_603419 := by exact prefixLift 603419
  have htrace : WordTrace (prefixWord ++ tailWord_603419) baseStart_603419 baseEnd_603419 := by
    simpa [prefixWord, tailWord_603419, baseEnd_603419] using wordTrace_append hprefix tailTrace_603419
  have hstable : (prefixWord ++ tailWord_603419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603419).length < 2 ^ (prefixWord ++ tailWord_603419).sum := by decide
  have hdescent : baseEnd_603419 < baseStart_603419 := by decide
  rcases family_descends (prefixWord ++ tailWord_603419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603449 : List Nat := [1, 2, 1, 6, 3, 1, 1, 2, 3]
def baseStart_603449 : Nat := 118140960795 + 603449 * 2 ^ 59
def prefixEnd_603449 : Nat := 4983230072969 + 3 ^ 40 * 603449 * 2
def baseEnd_603449 : Nat := 275430566644546432633151

theorem tailTrace_603449 : CollatzResearch.WordTrace tailWord_603449 prefixEnd_603449 275430566644546432633151 := by
  unfold tailWord_603449
  simp only [CollatzResearch.WordTrace]
  refine ⟨22009593190814808729213401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14673062127209872486142267 22009593190814808729213401)
  ·
    refine ⟨16507194893111106546910051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22009593190814808729213401 16507194893111106546910051)
    ·
      refine ⟨24760792339666659820365077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16507194893111106546910051 24760792339666659820365077)
      ·
        refine ⟨1160662140921874679079613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24760792339666659820365077 1160662140921874679079613)
        ·
          refine ⟨435248302845703004654855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1160662140921874679079613 435248302845703004654855)
          ·
            refine ⟨652872454268554506982283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435248302845703004654855 652872454268554506982283)
            ·
              refine ⟨979308681402831760473425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652872454268554506982283 979308681402831760473425)
              ·
                refine ⟨734481511052123820355069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 979308681402831760473425 734481511052123820355069)
                ·
                  refine ⟨275430566644546432633151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 734481511052123820355069 275430566644546432633151)
                  ·
                    rfl

theorem cell20_603449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 3].length) (baseStart_603449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603449 prefixEnd_603449 := by exact prefixLift 603449
  have htrace : WordTrace (prefixWord ++ tailWord_603449) baseStart_603449 baseEnd_603449 := by
    simpa [prefixWord, tailWord_603449, baseEnd_603449] using wordTrace_append hprefix tailTrace_603449
  have hstable : (prefixWord ++ tailWord_603449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603449).length < 2 ^ (prefixWord ++ tailWord_603449).sum := by decide
  have hdescent : baseEnd_603449 < baseStart_603449 := by decide
  rcases family_descends (prefixWord ++ tailWord_603449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603450 : List Nat := [3, 1, 1, 1, 4, 1, 9]
def baseStart_603450 : Nat := 118140960795 + 603450 * 2 ^ 59
def prefixEnd_603450 : Nat := 4983230072969 + 3 ^ 40 * 603450 * 2
def baseEnd_603450 : Nat := 30603447007977208177757

theorem tailTrace_603450 : CollatzResearch.WordTrace tailWord_603450 prefixEnd_603450 30603447007977208177757 := by
  unfold tailWord_603450
  simp only [CollatzResearch.WordTrace]
  refine ⟨5502407415952796474999951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14673086442540790599999869 5502407415952796474999951)
  ·
    refine ⟨8253611123929194712499927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5502407415952796474999951 8253611123929194712499927)
    ·
      refine ⟨12380416685893792068749891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8253611123929194712499927 12380416685893792068749891)
      ·
        refine ⟨18570625028840688103124837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12380416685893792068749891 18570625028840688103124837)
        ·
          refine ⟨3481992192907629019335907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18570625028840688103124837 3481992192907629019335907)
          ·
            refine ⟨5222988289361443529003861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3481992192907629019335907 5222988289361443529003861)
            ·
              refine ⟨30603447007977208177757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5222988289361443529003861 30603447007977208177757)
              ·
                rfl

theorem cell20_603450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 9].length) (baseStart_603450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603450 prefixEnd_603450 := by exact prefixLift 603450
  have htrace : WordTrace (prefixWord ++ tailWord_603450) baseStart_603450 baseEnd_603450 := by
    simpa [prefixWord, tailWord_603450, baseEnd_603450] using wordTrace_append hprefix tailTrace_603450
  have hstable : (prefixWord ++ tailWord_603450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603450).length < 2 ^ (prefixWord ++ tailWord_603450).sum := by decide
  have hdescent : baseEnd_603450 < baseStart_603450 := by decide
  rcases family_descends (prefixWord ++ tailWord_603450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603481 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 4]
def baseStart_603481 : Nat := 118140960795 + 603481 * 2 ^ 59
def prefixEnd_603481 : Nat := 4983230072969 + 3 ^ 40 * 603481 * 2
def baseEnd_603481 : Nat := 275445172316496543566353

theorem tailTrace_603481 : CollatzResearch.WordTrace tailWord_603481 prefixEnd_603481 275445172316496543566353 := by
  unfold tailWord_603481
  simp only [CollatzResearch.WordTrace]
  refine ⟨22010760326698878194378297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14673840217799252129585531 22010760326698878194378297)
  ·
    refine ⟨16508070245024158645783723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22010760326698878194378297 16508070245024158645783723)
    ·
      refine ⟨24762105367536237968675585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16508070245024158645783723 24762105367536237968675585)
      ·
        refine ⟨18571579025652178476506689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24762105367536237968675585 18571579025652178476506689)
        ·
          refine ⟨13928684269239133857380017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18571579025652178476506689 13928684269239133857380017)
          ·
            refine ⟨10446513201929350393035013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13928684269239133857380017 10446513201929350393035013)
            ·
              refine ⟨1958721225361753198694065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10446513201929350393035013 1958721225361753198694065)
              ·
                refine ⟨1469040919021314899020549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1958721225361753198694065 1469040919021314899020549)
                ·
                  refine ⟨275445172316496543566353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1469040919021314899020549 275445172316496543566353)
                  ·
                    rfl

theorem cell20_603481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_603481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603481 prefixEnd_603481 := by exact prefixLift 603481
  have htrace : WordTrace (prefixWord ++ tailWord_603481) baseStart_603481 baseEnd_603481 := by
    simpa [prefixWord, tailWord_603481, baseEnd_603481] using wordTrace_append hprefix tailTrace_603481
  have hstable : (prefixWord ++ tailWord_603481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603481).length < 2 ^ (prefixWord ++ tailWord_603481).sum := by decide
  have hdescent : baseEnd_603481 < baseStart_603481 := by decide
  rcases family_descends (prefixWord ++ tailWord_603481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603515 : List Nat := [1, 1, 1, 1, 1, 6, 5, 2, 2]
def baseStart_603515 : Nat := 118140960795 + 603515 * 2 ^ 59
def prefixEnd_603515 : Nat := 4983230072969 + 3 ^ 40 * 603515 * 2
def baseEnd_603515 : Nat := 275460690842943536432881

theorem tailTrace_603515 : CollatzResearch.WordTrace tailWord_603515 prefixEnd_603515 275460690842943536432881 := by
  unfold tailWord_603515
  simp only [CollatzResearch.WordTrace]
  refine ⟨22012000408575702001115999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14674666939050468000743999 22012000408575702001115999)
  ·
    refine ⟨33018000612863553001673999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22012000408575702001115999 33018000612863553001673999)
    ·
      refine ⟨49527000919295329502510999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33018000612863553001673999 49527000919295329502510999)
      ·
        refine ⟨74290501378942994253766499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49527000919295329502510999 74290501378942994253766499)
        ·
          refine ⟨111435752068414491380649749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74290501378942994253766499 111435752068414491380649749)
          ·
            refine ⟨5223550878206929283467957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111435752068414491380649749 5223550878206929283467957)
            ·
              refine ⟨489707894831899620325121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5223550878206929283467957 489707894831899620325121)
              ·
                refine ⟨367280921123924715243841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489707894831899620325121 367280921123924715243841)
                ·
                  refine ⟨275460690842943536432881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367280921123924715243841 275460690842943536432881)
                  ·
                    rfl

theorem cell20_603515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 2].length) (baseStart_603515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603515 prefixEnd_603515 := by exact prefixLift 603515
  have htrace : WordTrace (prefixWord ++ tailWord_603515) baseStart_603515 baseEnd_603515 := by
    simpa [prefixWord, tailWord_603515, baseEnd_603515] using wordTrace_append hprefix tailTrace_603515
  have hstable : (prefixWord ++ tailWord_603515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603515).length < 2 ^ (prefixWord ++ tailWord_603515).sum := by decide
  have hdescent : baseEnd_603515 < baseStart_603515 := by decide
  rcases family_descends (prefixWord ++ tailWord_603515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603522 : List Nat := [3, 4, 2, 1, 1, 1, 1, 7]
def baseStart_603522 : Nat := 118140960795 + 603522 * 2 ^ 59
def prefixEnd_603522 : Nat := 4983230072969 + 3 ^ 40 * 603522 * 2
def baseEnd_603522 : Nat := 91821295277894207733173

theorem tailTrace_603522 : CollatzResearch.WordTrace tailWord_603522 prefixEnd_603522 91821295277894207733173 := by
  unfold tailWord_603522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5503063929887585549155205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14674837146366894797747213 5503063929887585549155205)
  ·
    refine ⟨1031824486853922290466601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5503063929887585549155205 1031824486853922290466601)
    ·
      refine ⟨773868365140441717849951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1031824486853922290466601 773868365140441717849951)
      ·
        refine ⟨1160802547710662576774927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773868365140441717849951 1160802547710662576774927)
        ·
          refine ⟨1741203821565993865162391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160802547710662576774927 1741203821565993865162391)
          ·
            refine ⟨2611805732348990797743587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741203821565993865162391 2611805732348990797743587)
            ·
              refine ⟨3917708598523486196615381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2611805732348990797743587 3917708598523486196615381)
              ·
                refine ⟨91821295277894207733173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3917708598523486196615381 91821295277894207733173)
                ·
                  rfl

theorem cell20_603522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_603522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603522 prefixEnd_603522 := by exact prefixLift 603522
  have htrace : WordTrace (prefixWord ++ tailWord_603522) baseStart_603522 baseEnd_603522 := by
    simpa [prefixWord, tailWord_603522, baseEnd_603522] using wordTrace_append hprefix tailTrace_603522
  have hstable : (prefixWord ++ tailWord_603522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603522).length < 2 ^ (prefixWord ++ tailWord_603522).sum := by decide
  have hdescent : baseEnd_603522 < baseStart_603522 := by decide
  rcases family_descends (prefixWord ++ tailWord_603522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603529 : List Nat := [1, 2, 1, 1, 7, 1, 1, 3, 3]
def baseStart_603529 : Nat := 118140960795 + 603529 * 2 ^ 59
def prefixEnd_603529 : Nat := 4983230072969 + 3 ^ 40 * 603529 * 2
def baseEnd_603529 : Nat := 275467080824421709966157

theorem tailTrace_603529 : CollatzResearch.WordTrace tailWord_603529 prefixEnd_603529 275467080824421709966157 := by
  unfold tailWord_603529
  simp only [CollatzResearch.WordTrace]
  refine ⟨22012511030524982392125641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14675007353683321594750427 22012511030524982392125641)
  ·
    refine ⟨16509383272893736794094231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22012511030524982392125641 16509383272893736794094231)
    ·
      refine ⟨24764074909340605191141347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16509383272893736794094231 24764074909340605191141347)
      ·
        refine ⟨37146112364010907786712021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24764074909340605191141347 37146112364010907786712021)
        ·
          refine ⟨870612008531505651251063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 37146112364010907786712021 870612008531505651251063)
          ·
            refine ⟨1305918012797258476876595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870612008531505651251063 1305918012797258476876595)
            ·
              refine ⟨1958877019195887715314893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305918012797258476876595 1958877019195887715314893)
              ·
                refine ⟨734578882198457893243085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1958877019195887715314893 734578882198457893243085)
                ·
                  refine ⟨275467080824421709966157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 734578882198457893243085 275467080824421709966157)
                  ·
                    rfl

theorem cell20_603529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_603529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603529 prefixEnd_603529 := by exact prefixLift 603529
  have htrace : WordTrace (prefixWord ++ tailWord_603529) baseStart_603529 baseEnd_603529 := by
    simpa [prefixWord, tailWord_603529, baseEnd_603529] using wordTrace_append hprefix tailTrace_603529
  have hstable : (prefixWord ++ tailWord_603529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603529).length < 2 ^ (prefixWord ++ tailWord_603529).sum := by decide
  have hdescent : baseEnd_603529 < baseStart_603529 := by decide
  rcases family_descends (prefixWord ++ tailWord_603529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603560 : List Nat := [2, 1, 6, 1, 3, 7]
def baseStart_603560 : Nat := 118140960795 + 603560 * 2 ^ 59
def prefixEnd_603560 : Nat := 4983230072969 + 3 ^ 40 * 603560 * 2
def baseEnd_603560 : Nat := 10203008521078643701211

theorem tailTrace_603560 : CollatzResearch.WordTrace tailWord_603560 prefixEnd_603560 10203008521078643701211 := by
  unfold tailWord_603560
  simp only [CollatzResearch.WordTrace]
  refine ⟨11006820846706337343252067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14675761128941783124336089 11006820846706337343252067)
  ·
    refine ⟨16510231270059506014878101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11006820846706337343252067 16510231270059506014878101)
    ·
      refine ⟨773917090784039344447411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16510231270059506014878101 773917090784039344447411)
      ·
        refine ⟨1160875636176059016671117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773917090784039344447411 1160875636176059016671117)
        ·
          refine ⟨435328363566022131251669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1160875636176059016671117 435328363566022131251669)
          ·
            refine ⟨10203008521078643701211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 435328363566022131251669 10203008521078643701211)
            ·
              rfl

theorem cell20_603560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 7].length) (baseStart_603560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603560 prefixEnd_603560 := by exact prefixLift 603560
  have htrace : WordTrace (prefixWord ++ tailWord_603560) baseStart_603560 baseEnd_603560 := by
    simpa [prefixWord, tailWord_603560, baseEnd_603560] using wordTrace_append hprefix tailTrace_603560
  have hstable : (prefixWord ++ tailWord_603560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603560).length < 2 ^ (prefixWord ++ tailWord_603560).sum := by decide
  have hdescent : baseEnd_603560 < baseStart_603560 := by decide
  rcases family_descends (prefixWord ++ tailWord_603560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603571 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 5]
def baseStart_603571 : Nat := 118140960795 + 603571 * 2 ^ 59
def prefixEnd_603571 : Nat := 4983230072969 + 3 ^ 40 * 603571 * 2
def baseEnd_603571 : Nat := 275486250768856230565985

theorem tailTrace_603571 : CollatzResearch.WordTrace tailWord_603571 prefixEnd_603571 275486250768856230565985 := by
  unfold tailWord_603571
  simp only [CollatzResearch.WordTrace]
  refine ⟨22014042896372823565154567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14676028597581882376769711 22014042896372823565154567)
  ·
    refine ⟨33021064344559235347731851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22014042896372823565154567 33021064344559235347731851)
    ·
      refine ⟨49531596516838853021597777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33021064344559235347731851 49531596516838853021597777)
      ·
        refine ⟨37148697387629139766198333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49531596516838853021597777 37148697387629139766198333)
        ·
          refine ⟨13930761520360927412324375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37148697387629139766198333 13930761520360927412324375)
          ·
            refine ⟨20896142280541391118486563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13930761520360927412324375 20896142280541391118486563)
            ·
              refine ⟨31344213420812086677729845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20896142280541391118486563 31344213420812086677729845)
              ·
                refine ⟨2938520008201133126037173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31344213420812086677729845 2938520008201133126037173)
                ·
                  refine ⟨275486250768856230565985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2938520008201133126037173 275486250768856230565985)
                  ·
                    rfl

theorem cell20_603571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_603571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603571 prefixEnd_603571 := by exact prefixLift 603571
  have htrace : WordTrace (prefixWord ++ tailWord_603571) baseStart_603571 baseEnd_603571 := by
    simpa [prefixWord, tailWord_603571, baseEnd_603571] using wordTrace_append hprefix tailTrace_603571
  have hstable : (prefixWord ++ tailWord_603571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603571).length < 2 ^ (prefixWord ++ tailWord_603571).sum := by decide
  have hdescent : baseEnd_603571 < baseStart_603571 := by decide
  rcases family_descends (prefixWord ++ tailWord_603571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603629 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 4]
def baseStart_603629 : Nat := 118140960795 + 603629 * 2 ^ 59
def prefixEnd_603629 : Nat := 4983230072969 + 3 ^ 40 * 603629 * 2
def baseEnd_603629 : Nat := 275512723549265806632415

theorem tailTrace_603629 : CollatzResearch.WordTrace tailWord_603629 prefixEnd_603629 275512723549265806632415 := by
  unfold tailWord_603629
  simp only [CollatzResearch.WordTrace]
  refine ⟨22016158330162699470765941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14677438886775132980510627 22016158330162699470765941)
  ·
    refine ⟨2064014843452753075384307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22016158330162699470765941 2064014843452753075384307)
    ·
      refine ⟨3096022265179129613076461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2064014843452753075384307 3096022265179129613076461)
      ·
        refine ⟨1161008349442173604903673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3096022265179129613076461 1161008349442173604903673)
        ·
          refine ⟨870756262081630203677755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1161008349442173604903673 870756262081630203677755)
          ·
            refine ⟨1306134393122445305516633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870756262081630203677755 1306134393122445305516633)
            ·
              refine ⟨979600794841833979137475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1306134393122445305516633 979600794841833979137475)
              ·
                refine ⟨1469401192262750968706213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979600794841833979137475 1469401192262750968706213)
                ·
                  refine ⟨275512723549265806632415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1469401192262750968706213 275512723549265806632415)
                  ·
                    rfl

theorem cell20_603629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_603629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603629 prefixEnd_603629 := by exact prefixLift 603629
  have htrace : WordTrace (prefixWord ++ tailWord_603629) baseStart_603629 baseEnd_603629 := by
    simpa [prefixWord, tailWord_603629, baseEnd_603629] using wordTrace_append hprefix tailTrace_603629
  have hstable : (prefixWord ++ tailWord_603629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603629).length < 2 ^ (prefixWord ++ tailWord_603629).sum := by decide
  have hdescent : baseEnd_603629 < baseStart_603629 := by decide
  rcases family_descends (prefixWord ++ tailWord_603629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603633 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 4]
def baseStart_603633 : Nat := 118140960795 + 603633 * 2 ^ 59
def prefixEnd_603633 : Nat := 4983230072969 + 3 ^ 40 * 603633 * 2
def baseEnd_603633 : Nat := 275514549258259570499065

theorem tailTrace_603633 : CollatzResearch.WordTrace tailWord_603633 prefixEnd_603633 275514549258259570499065 := by
  unfold tailWord_603633
  simp only [CollatzResearch.WordTrace]
  refine ⟨22016304222148208153911553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14677536148098805435941035 22016304222148208153911553)
  ·
    refine ⟨16512228166611156115433665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22016304222148208153911553 16512228166611156115433665)
    ·
      refine ⟨12384171124958367086575249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16512228166611156115433665 12384171124958367086575249)
      ·
        refine ⟨9288128343718775314931437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12384171124958367086575249 9288128343718775314931437)
        ·
          refine ⟨3483048128894540743099289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9288128343718775314931437 3483048128894540743099289)
          ·
            refine ⟨2612286096670905557324467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3483048128894540743099289 2612286096670905557324467)
            ·
              refine ⟨3918429145006358335986701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2612286096670905557324467 3918429145006358335986701)
              ·
                refine ⟨1469410929377384375995013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3918429145006358335986701 1469410929377384375995013)
                ·
                  refine ⟨275514549258259570499065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1469410929377384375995013 275514549258259570499065)
                  ·
                    rfl

theorem cell20_603633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_603633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603633 prefixEnd_603633 := by exact prefixLift 603633
  have htrace : WordTrace (prefixWord ++ tailWord_603633) baseStart_603633 baseEnd_603633 := by
    simpa [prefixWord, tailWord_603633, baseEnd_603633] using wordTrace_append hprefix tailTrace_603633
  have hstable : (prefixWord ++ tailWord_603633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603633).length < 2 ^ (prefixWord ++ tailWord_603633).sum := by decide
  have hdescent : baseEnd_603633 < baseStart_603633 := by decide
  rcases family_descends (prefixWord ++ tailWord_603633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603667 : List Nat := [1, 1, 1, 2, 1, 8, 1, 3, 2]
def baseStart_603667 : Nat := 118140960795 + 603667 * 2 ^ 59
def prefixEnd_603667 : Nat := 4983230072969 + 3 ^ 40 * 603667 * 2
def baseEnd_603667 : Nat := 275530067784706563365593

theorem tailTrace_603667 : CollatzResearch.WordTrace tailWord_603667 prefixEnd_603667 275530067784706563365593 := by
  unfold tailWord_603667
  simp only [CollatzResearch.WordTrace]
  refine ⟨22017544304025031960649255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14678362869350021307099503 22017544304025031960649255)
  ·
    refine ⟨33026316456037547940973883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22017544304025031960649255 33026316456037547940973883)
    ·
      refine ⟨49539474684056321911460825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33026316456037547940973883 49539474684056321911460825)
      ·
        refine ⟨37154606013042241433595619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49539474684056321911460825 37154606013042241433595619)
        ·
          refine ⟨55731909019563362150393429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37154606013042241433595619 55731909019563362150393429)
          ·
            refine ⟨653108308823008150199923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 55731909019563362150393429 653108308823008150199923)
            ·
              refine ⟨979662463234512225299885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653108308823008150199923 979662463234512225299885)
              ·
                refine ⟨367373423712942084487457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 979662463234512225299885 367373423712942084487457)
                ·
                  refine ⟨275530067784706563365593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367373423712942084487457 275530067784706563365593)
                  ·
                    rfl

theorem cell20_603667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 2].length) (baseStart_603667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603667 prefixEnd_603667 := by exact prefixLift 603667
  have htrace : WordTrace (prefixWord ++ tailWord_603667) baseStart_603667 baseEnd_603667 := by
    simpa [prefixWord, tailWord_603667, baseEnd_603667] using wordTrace_append hprefix tailTrace_603667
  have hstable : (prefixWord ++ tailWord_603667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603667).length < 2 ^ (prefixWord ++ tailWord_603667).sum := by decide
  have hdescent : baseEnd_603667 < baseStart_603667 := by decide
  rcases family_descends (prefixWord ++ tailWord_603667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603726 : List Nat := [4, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_603726 : Nat := 118140960795 + 603726 * 2 ^ 59
def prefixEnd_603726 : Nat := 4983230072969 + 3 ^ 40 * 603726 * 2
def baseEnd_603726 : Nat := 275556996992364580398685

theorem tailTrace_603726 : CollatzResearch.WordTrace tailWord_603726 prefixEnd_603726 275556996992364580398685 := by
  unfold tailWord_603726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2752462026351410629630879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14679797473874190024698021 2752462026351410629630879)
  ·
    refine ⟨4128693039527115944446319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2752462026351410629630879 4128693039527115944446319)
    ·
      refine ⟨6193039559290673916669479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4128693039527115944446319 6193039559290673916669479)
      ·
        refine ⟨9289559338936010875004219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6193039559290673916669479 9289559338936010875004219)
        ·
          refine ⟨13934339008404016312506329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9289559338936010875004219 13934339008404016312506329)
          ·
            refine ⟨10450754256303012234379747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13934339008404016312506329 10450754256303012234379747)
            ·
              refine ⟨15676131384454518351569621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10450754256303012234379747 15676131384454518351569621)
              ·
                refine ⟨367409329323152773864913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15676131384454518351569621 367409329323152773864913)
                ·
                  refine ⟨275556996992364580398685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367409329323152773864913 275556996992364580398685)
                  ·
                    rfl

theorem cell20_603726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_603726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603726 prefixEnd_603726 := by exact prefixLift 603726
  have htrace : WordTrace (prefixWord ++ tailWord_603726) baseStart_603726 baseEnd_603726 := by
    simpa [prefixWord, tailWord_603726, baseEnd_603726] using wordTrace_append hprefix tailTrace_603726
  have hstable : (prefixWord ++ tailWord_603726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603726).length < 2 ^ (prefixWord ++ tailWord_603726).sum := by decide
  have hdescent : baseEnd_603726 < baseStart_603726 := by decide
  rcases family_descends (prefixWord ++ tailWord_603726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603822 : List Nat := [4, 1, 4, 1, 3, 1, 2, 4]
def baseStart_603822 : Nat := 118140960795 + 603822 * 2 ^ 59
def prefixEnd_603822 : Nat := 4983230072969 + 3 ^ 40 * 603822 * 2
def baseEnd_603822 : Nat := 91866938002738304399431

theorem tailTrace_603822 : CollatzResearch.WordTrace tailWord_603822 prefixEnd_603822 91866938002738304399431 := by
  unfold tailWord_603822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2752899702307936679067715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14682131745642328955027813 2752899702307936679067715)
  ·
    refine ⟨4129349553461905018601573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2752899702307936679067715 4129349553461905018601573)
    ·
      refine ⟨774253041274107190987795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4129349553461905018601573 774253041274107190987795)
      ·
        refine ⟨1161379561911160786481693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774253041274107190987795 1161379561911160786481693)
        ·
          refine ⟨435517335716685294930635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1161379561911160786481693 435517335716685294930635)
          ·
            refine ⟨653276003575027942395953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435517335716685294930635 653276003575027942395953)
            ·
              refine ⟨489957002681270956796965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653276003575027942395953 489957002681270956796965)
              ·
                refine ⟨91866938002738304399431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 489957002681270956796965 91866938002738304399431)
                ·
                  rfl

theorem cell20_603822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_603822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603822 prefixEnd_603822 := by exact prefixLift 603822
  have htrace : WordTrace (prefixWord ++ tailWord_603822) baseStart_603822 baseEnd_603822 := by
    simpa [prefixWord, tailWord_603822, baseEnd_603822] using wordTrace_append hprefix tailTrace_603822
  have hstable : (prefixWord ++ tailWord_603822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603822).length < 2 ^ (prefixWord ++ tailWord_603822).sum := by decide
  have hdescent : baseEnd_603822 < baseStart_603822 := by decide
  rcases family_descends (prefixWord ++ tailWord_603822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603837 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 7]
def baseStart_603837 : Nat := 118140960795 + 603837 * 2 ^ 59
def prefixEnd_603837 : Nat := 4983230072969 + 3 ^ 40 * 603837 * 2
def baseEnd_603837 : Nat := 275607660416941527698231

theorem tailTrace_603837 : CollatzResearch.WordTrace tailWord_603837 prefixEnd_603837 275607660416941527698231 := by
  unfold tailWord_603837
  simp only [CollatzResearch.WordTrace]
  refine ⟨22023744713409150994337765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14682496475606100662891843 22023744713409150994337765)
  ·
    refine ⟨4129452133764215811438331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22023744713409150994337765 4129452133764215811438331)
    ·
      refine ⟨6194178200646323717157497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4129452133764215811438331 6194178200646323717157497)
      ·
        refine ⟨4645633650484742787868123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6194178200646323717157497 4645633650484742787868123)
        ·
          refine ⟨6968450475727114181802185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4645633650484742787868123 6968450475727114181802185)
          ·
            refine ⟨5226337856795335636351639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6968450475727114181802185 5226337856795335636351639)
            ·
              refine ⟨7839506785193003454527459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5226337856795335636351639 7839506785193003454527459)
              ·
                refine ⟨11759260177789505181791189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7839506785193003454527459 11759260177789505181791189)
                ·
                  refine ⟨275607660416941527698231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11759260177789505181791189 275607660416941527698231)
                  ·
                    rfl

theorem cell20_603837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_603837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603837 prefixEnd_603837 := by exact prefixLift 603837
  have htrace : WordTrace (prefixWord ++ tailWord_603837) baseStart_603837 baseEnd_603837 := by
    simpa [prefixWord, tailWord_603837, baseEnd_603837] using wordTrace_append hprefix tailTrace_603837
  have hstable : (prefixWord ++ tailWord_603837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603837).length < 2 ^ (prefixWord ++ tailWord_603837).sum := by decide
  have hdescent : baseEnd_603837 < baseStart_603837 := by decide
  rcases family_descends (prefixWord ++ tailWord_603837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603853 : List Nat := [1, 6, 2, 1, 1, 2, 3, 2, 2]
def baseStart_603853 : Nat := 118140960795 + 603853 * 2 ^ 59
def prefixEnd_603853 : Nat := 4983230072969 + 3 ^ 40 * 603853 * 2
def baseEnd_603853 : Nat := 275614963252916583164833

theorem tailTrace_603853 : CollatzResearch.WordTrace tailWord_603853 prefixEnd_603853 275614963252916583164833 := by
  unfold tailWord_603853
  simp only [CollatzResearch.WordTrace]
  refine ⟨22024328281351185726920213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14682885520900790484613475 22024328281351185726920213)
  ·
    refine ⟨1032390388188336830949385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22024328281351185726920213 1032390388188336830949385)
    ·
      refine ⟨774292791141252623212039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1032390388188336830949385 774292791141252623212039)
      ·
        refine ⟨1161439186711878934818059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774292791141252623212039 1161439186711878934818059)
        ·
          refine ⟨1742158780067818402227089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1161439186711878934818059 1742158780067818402227089)
          ·
            refine ⟨1306619085050863801670317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1742158780067818402227089 1306619085050863801670317)
            ·
              refine ⟨489982156894073925626369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1306619085050863801670317 489982156894073925626369)
              ·
                refine ⟨367486617670555444219777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489982156894073925626369 367486617670555444219777)
                ·
                  refine ⟨275614963252916583164833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367486617670555444219777 275614963252916583164833)
                  ·
                    rfl

theorem cell20_603853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_603853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603853 prefixEnd_603853 := by exact prefixLift 603853
  have htrace : WordTrace (prefixWord ++ tailWord_603853) baseStart_603853 baseEnd_603853 := by
    simpa [prefixWord, tailWord_603853, baseEnd_603853] using wordTrace_append hprefix tailTrace_603853
  have hstable : (prefixWord ++ tailWord_603853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603853).length < 2 ^ (prefixWord ++ tailWord_603853).sum := by decide
  have hdescent : baseEnd_603853 < baseStart_603853 := by decide
  rcases family_descends (prefixWord ++ tailWord_603853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603854 : List Nat := [4, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_603854 : Nat := 118140960795 + 603854 * 2 ^ 59
def prefixEnd_603854 : Nat := 4983230072969 + 3 ^ 40 * 603854 * 2
def baseEnd_603854 : Nat := 275615419680165024131495

theorem tailTrace_603854 : CollatzResearch.WordTrace tailWord_603854 prefixEnd_603854 275615419680165024131495 := by
  unfold tailWord_603854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2753045594293445362213327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14682909836231708598471077 2753045594293445362213327)
  ·
    refine ⟨4129568391440168043319991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2753045594293445362213327 4129568391440168043319991)
    ·
      refine ⟨6194352587160252064979987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4129568391440168043319991 6194352587160252064979987)
      ·
        refine ⟨9291528880740378097469981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6194352587160252064979987 9291528880740378097469981)
        ·
          refine ⟨3484323330277641786551243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9291528880740378097469981 3484323330277641786551243)
          ·
            refine ⟨5226484995416462679826865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3484323330277641786551243 5226484995416462679826865)
            ·
              refine ⟨3919863746562347009870149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5226484995416462679826865 3919863746562347009870149)
              ·
                refine ⟨734974452480440064350653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3919863746562347009870149 734974452480440064350653)
                ·
                  refine ⟨275615419680165024131495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 734974452480440064350653 275615419680165024131495)
                  ·
                    rfl

theorem cell20_603854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_603854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603854 prefixEnd_603854 := by exact prefixLift 603854
  have htrace : WordTrace (prefixWord ++ tailWord_603854) baseStart_603854 baseEnd_603854 := by
    simpa [prefixWord, tailWord_603854, baseEnd_603854] using wordTrace_append hprefix tailTrace_603854
  have hstable : (prefixWord ++ tailWord_603854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603854).length < 2 ^ (prefixWord ++ tailWord_603854).sum := by decide
  have hdescent : baseEnd_603854 < baseStart_603854 := by decide
  rcases family_descends (prefixWord ++ tailWord_603854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603857 : List Nat := [1, 2, 2, 1, 2, 5, 3, 2, 2]
def baseStart_603857 : Nat := 118140960795 + 603857 * 2 ^ 59
def prefixEnd_603857 : Nat := 4983230072969 + 3 ^ 40 * 603857 * 2
def baseEnd_603857 : Nat := 275616788961910347031483

theorem tailTrace_603857 : CollatzResearch.WordTrace tailWord_603857 prefixEnd_603857 275616788961910347031483 := by
  unfold tailWord_603857
  simp only [CollatzResearch.WordTrace]
  refine ⟨22024474173336694410065825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14682982782224462940043883 22024474173336694410065825)
  ·
    refine ⟨16518355630002520807549369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22024474173336694410065825 16518355630002520807549369)
    ·
      refine ⟨12388766722501890605662027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16518355630002520807549369 12388766722501890605662027)
      ·
        refine ⟨18583150083752835908493041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12388766722501890605662027 18583150083752835908493041)
        ·
          refine ⟨13937362562814626931369781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18583150083752835908493041 13937362562814626931369781)
          ·
            refine ⟨1306627740263871274815917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13937362562814626931369781 1306627740263871274815917)
            ·
              refine ⟨489985402598951728055969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1306627740263871274815917 489985402598951728055969)
              ·
                refine ⟨367489051949213796041977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489985402598951728055969 367489051949213796041977)
                ·
                  refine ⟨275616788961910347031483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367489051949213796041977 275616788961910347031483)
                  ·
                    rfl

theorem cell20_603857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 2].length) (baseStart_603857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603857 prefixEnd_603857 := by exact prefixLift 603857
  have htrace : WordTrace (prefixWord ++ tailWord_603857) baseStart_603857 baseEnd_603857 := by
    simpa [prefixWord, tailWord_603857, baseEnd_603857] using wordTrace_append hprefix tailTrace_603857
  have hstable : (prefixWord ++ tailWord_603857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603857).length < 2 ^ (prefixWord ++ tailWord_603857).sum := by decide
  have hdescent : baseEnd_603857 < baseStart_603857 := by decide
  rcases family_descends (prefixWord ++ tailWord_603857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603930 : List Nat := [3, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_603930 : Nat := 118140960795 + 603930 * 2 ^ 59
def prefixEnd_603930 : Nat := 4983230072969 + 3 ^ 40 * 603930 * 2
def baseEnd_603930 : Nat := 275650108151046537597851

theorem tailTrace_603930 : CollatzResearch.WordTrace tailWord_603930 prefixEnd_603930 275650108151046537597851 := by
  unfold tailWord_603930
  simp only [CollatzResearch.WordTrace]
  refine ⟨5506784175518056969368311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14684757801381485251648829 5506784175518056969368311)
  ·
    refine ⟨8260176263277085454052467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5506784175518056969368311 8260176263277085454052467)
    ·
      refine ⟨12390264394915628181078701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8260176263277085454052467 12390264394915628181078701)
      ·
        refine ⟨4646349148093360567904513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12390264394915628181078701 4646349148093360567904513)
        ·
          refine ⟨3484761861070020425928385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4646349148093360567904513 3484761861070020425928385)
          ·
            refine ⟨2613571395802515319446289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3484761861070020425928385 2613571395802515319446289)
            ·
              refine ⟨1960178546851886489584717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2613571395802515319446289 1960178546851886489584717)
              ·
                refine ⟨735066955069457433594269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1960178546851886489584717 735066955069457433594269)
                ·
                  refine ⟨275650108151046537597851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 735066955069457433594269 275650108151046537597851)
                  ·
                    rfl

theorem cell20_603930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_603930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603930 prefixEnd_603930 := by exact prefixLift 603930
  have htrace : WordTrace (prefixWord ++ tailWord_603930) baseStart_603930 baseEnd_603930 := by
    simpa [prefixWord, tailWord_603930, baseEnd_603930] using wordTrace_append hprefix tailTrace_603930
  have hstable : (prefixWord ++ tailWord_603930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603930).length < 2 ^ (prefixWord ++ tailWord_603930).sum := by decide
  have hdescent : baseEnd_603930 < baseStart_603930 := by decide
  rcases family_descends (prefixWord ++ tailWord_603930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603937 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 4]
def baseStart_603937 : Nat := 118140960795 + 603937 * 2 ^ 59
def prefixEnd_603937 : Nat := 4983230072969 + 3 ^ 40 * 603937 * 2
def baseEnd_603937 : Nat := 275653303141785624364489

theorem tailTrace_603937 : CollatzResearch.WordTrace tailWord_603937 prefixEnd_603937 275653303141785624364489 := by
  unfold tailWord_603937
  simp only [CollatzResearch.WordTrace]
  refine ⟨22027392013046868072978065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14684928008697912048652043 22027392013046868072978065)
  ·
    refine ⟨16520544009785151054733549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22027392013046868072978065 16520544009785151054733549)
    ·
      refine ⟨6195204003669431645525081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16520544009785151054733549 6195204003669431645525081)
      ·
        refine ⟨4646403002752073734143811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6195204003669431645525081 4646403002752073734143811)
        ·
          refine ⟨6969604504128110601215717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4646403002752073734143811 6969604504128110601215717)
          ·
            refine ⟨1306800844524020737727947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6969604504128110601215717 1306800844524020737727947)
            ·
              refine ⟨1960201266786031106591921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1306800844524020737727947 1960201266786031106591921)
              ·
                refine ⟨1470150950089523329943941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1960201266786031106591921 1470150950089523329943941)
                ·
                  refine ⟨275653303141785624364489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1470150950089523329943941 275653303141785624364489)
                  ·
                    rfl

theorem cell20_603937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_603937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603937 prefixEnd_603937 := by exact prefixLift 603937
  have htrace : WordTrace (prefixWord ++ tailWord_603937) baseStart_603937 baseEnd_603937 := by
    simpa [prefixWord, tailWord_603937, baseEnd_603937] using wordTrace_append hprefix tailTrace_603937
  have hstable : (prefixWord ++ tailWord_603937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603937).length < 2 ^ (prefixWord ++ tailWord_603937).sum := by decide
  have hdescent : baseEnd_603937 < baseStart_603937 := by decide
  rcases family_descends (prefixWord ++ tailWord_603937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603950 : List Nat := [4, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_603950 : Nat := 118140960795 + 603950 * 2 ^ 59
def prefixEnd_603950 : Nat := 4983230072969 + 3 ^ 40 * 603950 * 2
def baseEnd_603950 : Nat := 275659236696015356931103

theorem tailTrace_603950 : CollatzResearch.WordTrace tailWord_603950 prefixEnd_603950 275659236696015356931103 := by
  unfold tailWord_603950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2753483270249971411650163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14685244107999847528800869 2753483270249971411650163)
  ·
    refine ⟨4130224905374957117475245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2753483270249971411650163 4130224905374957117475245)
    ·
      refine ⟨1548834339515608919053217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4130224905374957117475245 1548834339515608919053217)
      ·
        refine ⟨1161625754636706689289913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1548834339515608919053217 1161625754636706689289913)
        ·
          refine ⟨871219315977530016967435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1161625754636706689289913 871219315977530016967435)
          ·
            refine ⟨1306828973966295025451153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871219315977530016967435 1306828973966295025451153)
            ·
              refine ⟨980121730474721269088365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1306828973966295025451153 980121730474721269088365)
              ·
                refine ⟨367545648928020475908137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 980121730474721269088365 367545648928020475908137)
                ·
                  refine ⟨275659236696015356931103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367545648928020475908137 275659236696015356931103)
                  ·
                    rfl

theorem cell20_603950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_603950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603950 prefixEnd_603950 := by exact prefixLift 603950
  have htrace : WordTrace (prefixWord ++ tailWord_603950) baseStart_603950 baseEnd_603950 := by
    simpa [prefixWord, tailWord_603950, baseEnd_603950] using wordTrace_append hprefix tailTrace_603950
  have hstable : (prefixWord ++ tailWord_603950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603950).length < 2 ^ (prefixWord ++ tailWord_603950).sum := by decide
  have hdescent : baseEnd_603950 < baseStart_603950 := by decide
  rcases family_descends (prefixWord ++ tailWord_603950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603954 : List Nat := [3, 2, 1, 1, 3, 2, 1, 5, 2]
def baseStart_603954 : Nat := 118140960795 + 603954 * 2 ^ 59
def prefixEnd_603954 : Nat := 4983230072969 + 3 ^ 40 * 603954 * 2
def baseEnd_603954 : Nat := 275661062405009120797753

theorem tailTrace_603954 : CollatzResearch.WordTrace tailWord_603954 prefixEnd_603954 275661062405009120797753 := by
  unfold tailWord_603954
  simp only [CollatzResearch.WordTrace]
  refine ⟨5507003013496319994086729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14685341369323519984231277 5507003013496319994086729)
  ·
    refine ⟨4130252260122239995565047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5507003013496319994086729 4130252260122239995565047)
    ·
      refine ⟨6195378390183359993347571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4130252260122239995565047 6195378390183359993347571)
      ·
        refine ⟨9293067585275039990021357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6195378390183359993347571 9293067585275039990021357)
        ·
          refine ⟨3484900344478139996258009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9293067585275039990021357 3484900344478139996258009)
          ·
            refine ⟨2613675258358604997193507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3484900344478139996258009 2613675258358604997193507)
            ·
              refine ⟨3920512887537907495790261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613675258358604997193507 3920512887537907495790261)
              ·
                refine ⟨367548083206678827730337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3920512887537907495790261 367548083206678827730337)
                ·
                  refine ⟨275661062405009120797753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367548083206678827730337 275661062405009120797753)
                  ·
                    rfl

theorem cell20_603954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_603954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603954 prefixEnd_603954 := by exact prefixLift 603954
  have htrace : WordTrace (prefixWord ++ tailWord_603954) baseStart_603954 baseEnd_603954 := by
    simpa [prefixWord, tailWord_603954, baseEnd_603954] using wordTrace_append hprefix tailTrace_603954
  have hstable : (prefixWord ++ tailWord_603954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603954).length < 2 ^ (prefixWord ++ tailWord_603954).sum := by decide
  have hdescent : baseEnd_603954 < baseStart_603954 := by decide
  rcases family_descends (prefixWord ++ tailWord_603954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603961 : List Nat := [1, 2, 1, 7, 1, 1, 7]
def baseStart_603961 : Nat := 118140960795 + 603961 * 2 ^ 59
def prefixEnd_603961 : Nat := 4983230072969 + 3 ^ 40 * 603961 * 2
def baseEnd_603961 : Nat := 30629361932860911951599

theorem tailTrace_603961 : CollatzResearch.WordTrace tailWord_603961 prefixEnd_603961 30629361932860911951599 := by
  unfold tailWord_603961
  simp only [CollatzResearch.WordTrace]
  refine ⟨22028267364959920171851737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14685511576639946781234491 22028267364959920171851737)
  ·
    refine ⟨16521200523719940128888803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22028267364959920171851737 16521200523719940128888803)
    ·
      refine ⟨24781800785579910193333205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16521200523719940128888803 24781800785579910193333205)
      ·
        refine ⟨580823455912029145156247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 24781800785579910193333205 580823455912029145156247)
        ·
          refine ⟨871235183868043717734371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580823455912029145156247 871235183868043717734371)
          ·
            refine ⟨1306852775802065576601557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871235183868043717734371 1306852775802065576601557)
            ·
              refine ⟨30629361932860911951599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1306852775802065576601557 30629361932860911951599)
              ·
                rfl

theorem cell20_603961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 7].length) (baseStart_603961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603961 prefixEnd_603961 := by exact prefixLift 603961
  have htrace : WordTrace (prefixWord ++ tailWord_603961) baseStart_603961 baseEnd_603961 := by
    simpa [prefixWord, tailWord_603961, baseEnd_603961] using wordTrace_append hprefix tailTrace_603961
  have hstable : (prefixWord ++ tailWord_603961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603961).length < 2 ^ (prefixWord ++ tailWord_603961).sum := by decide
  have hdescent : baseEnd_603961 < baseStart_603961 := by decide
  rcases family_descends (prefixWord ++ tailWord_603961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603985 : List Nat := [1, 2, 2, 1, 5, 2, 3, 1, 3]
def baseStart_603985 : Nat := 118140960795 + 603985 * 2 ^ 59
def prefixEnd_603985 : Nat := 4983230072969 + 3 ^ 40 * 603985 * 2
def baseEnd_603985 : Nat := 275675211649710790764293

theorem tailTrace_603985 : CollatzResearch.WordTrace tailWord_603985 prefixEnd_603985 275675211649710790764293 := by
  unfold tailWord_603985
  simp only [CollatzResearch.WordTrace]
  refine ⟨22029142716872972270725409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14686095144581981513816939 22029142716872972270725409)
  ·
    refine ⟨16521857037654729203044057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22029142716872972270725409 16521857037654729203044057)
    ·
      refine ⟨12391392778241046902283043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16521857037654729203044057 12391392778241046902283043)
      ·
        refine ⟨18587089167361570353424565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12391392778241046902283043 18587089167361570353424565)
        ·
          refine ⟨1742539609440147220633553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18587089167361570353424565 1742539609440147220633553)
          ·
            refine ⟨1306904707080110415475165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1742539609440147220633553 1306904707080110415475165)
            ·
              refine ⟨490089265155041405803187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1306904707080110415475165 490089265155041405803187)
              ·
                refine ⟨735133897732562108704781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490089265155041405803187 735133897732562108704781)
                ·
                  refine ⟨275675211649710790764293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 735133897732562108704781 275675211649710790764293)
                  ·
                    rfl

theorem cell20_603985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_603985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603985 prefixEnd_603985 := by exact prefixLift 603985
  have htrace : WordTrace (prefixWord ++ tailWord_603985) baseStart_603985 baseEnd_603985 := by
    simpa [prefixWord, tailWord_603985, baseEnd_603985] using wordTrace_append hprefix tailTrace_603985
  have hstable : (prefixWord ++ tailWord_603985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603985).length < 2 ^ (prefixWord ++ tailWord_603985).sum := by decide
  have hdescent : baseEnd_603985 < baseStart_603985 := by decide
  rcases family_descends (prefixWord ++ tailWord_603985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603999 : List Nat := [1, 1, 2, 3, 1, 6, 2, 4]
def baseStart_603999 : Nat := 118140960795 + 603999 * 2 ^ 59
def prefixEnd_603999 : Nat := 4983230072969 + 3 ^ 40 * 603999 * 2
def baseEnd_603999 : Nat := 91893867210396321432523

theorem tailTrace_603999 : CollatzResearch.WordTrace tailWord_603999 prefixEnd_603999 91893867210396321432523 := by
  unfold tailWord_603999
  simp only [CollatzResearch.WordTrace]
  refine ⟨22029653338822252661735051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14686435559214835107823367 22029653338822252661735051)
  ·
    refine ⟨33044480008233378992602577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22029653338822252661735051 33044480008233378992602577)
    ·
      refine ⟨24783360006175034244451933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33044480008233378992602577 24783360006175034244451933)
      ·
        refine ⟨9293760002315637841669475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24783360006175034244451933 9293760002315637841669475)
        ·
          refine ⟨13940640003473456762504213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9293760002315637841669475 13940640003473456762504213)
          ·
            refine ⟨653467500162818285742385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13940640003473456762504213 653467500162818285742385)
            ·
              refine ⟨490100625122113714306789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653467500162818285742385 490100625122113714306789)
              ·
                refine ⟨91893867210396321432523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 490100625122113714306789 91893867210396321432523)
                ·
                  rfl

theorem cell20_603999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 4].length) (baseStart_603999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_603999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_603999 prefixEnd_603999 := by exact prefixLift 603999
  have htrace : WordTrace (prefixWord ++ tailWord_603999) baseStart_603999 baseEnd_603999 := by
    simpa [prefixWord, tailWord_603999, baseEnd_603999] using wordTrace_append hprefix tailTrace_603999
  have hstable : (prefixWord ++ tailWord_603999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603999).length < 2 ^ (prefixWord ++ tailWord_603999).sum := by decide
  have hdescent : baseEnd_603999 < baseStart_603999 := by decide
  rcases family_descends (prefixWord ++ tailWord_603999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604027 : List Nat := [1, 1, 1, 1, 1, 5, 1, 6, 3]
def baseStart_604027 : Nat := 118140960795 + 604027 * 2 ^ 59
def prefixEnd_604027 : Nat := 4983230072969 + 3 ^ 40 * 604027 * 2
def baseEnd_604027 : Nat := 275694381594145311364121

theorem tailTrace_604027 : CollatzResearch.WordTrace tailWord_604027 prefixEnd_604027 275694381594145311364121 := by
  unfold tailWord_604027
  simp only [CollatzResearch.WordTrace]
  refine ⟨22030674582720813443754335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14687116388480542295836223 22030674582720813443754335)
  ·
    refine ⟨33046011874081220165631503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22030674582720813443754335 33046011874081220165631503)
    ·
      refine ⟨49569017811121830248447255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33046011874081220165631503 49569017811121830248447255)
      ·
        refine ⟨74353526716682745372670883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49569017811121830248447255 74353526716682745372670883)
        ·
          refine ⟨111530290075024118059006325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74353526716682745372670883 111530290075024118059006325)
          ·
            refine ⟨10455964694533511068031843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111530290075024118059006325 10455964694533511068031843)
            ·
              refine ⟨15683947041800266602047765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10455964694533511068031843 15683947041800266602047765)
              ·
                refine ⟨735185017584387496970989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15683947041800266602047765 735185017584387496970989)
                ·
                  refine ⟨275694381594145311364121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 735185017584387496970989 275694381594145311364121)
                  ·
                    rfl

theorem cell20_604027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 3].length) (baseStart_604027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604027 prefixEnd_604027 := by exact prefixLift 604027
  have htrace : WordTrace (prefixWord ++ tailWord_604027) baseStart_604027 baseEnd_604027 := by
    simpa [prefixWord, tailWord_604027, baseEnd_604027] using wordTrace_append hprefix tailTrace_604027
  have hstable : (prefixWord ++ tailWord_604027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604027).length < 2 ^ (prefixWord ++ tailWord_604027).sum := by decide
  have hdescent : baseEnd_604027 < baseStart_604027 := by decide
  rcases family_descends (prefixWord ++ tailWord_604027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604040 : List Nat := [2, 1, 3, 3, 3, 2, 2, 1, 3]
def baseStart_604040 : Nat := 118140960795 + 604040 * 2 ^ 59
def prefixEnd_604040 : Nat := 4983230072969 + 3 ^ 40 * 604040 * 2
def baseEnd_604040 : Nat := 275700315148375043930735

theorem tailTrace_604040 : CollatzResearch.WordTrace tailWord_604040 prefixEnd_604040 275700315148375043930735 := by
  unfold tailWord_604040
  simp only [CollatzResearch.WordTrace]
  refine ⟨11015574365836858331988787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14687432487782477775985049 11015574365836858331988787)
  ·
    refine ⟨16523361548755287497983181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11015574365836858331988787 16523361548755287497983181)
    ·
      refine ⟨6196260580783232811743693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16523361548755287497983181 6196260580783232811743693)
      ·
        refine ⟨2323597717793712304403885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6196260580783232811743693 2323597717793712304403885)
        ·
          refine ⟨871349144172642114151457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2323597717793712304403885 871349144172642114151457)
          ·
            refine ⟨653511858129481585613593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 871349144172642114151457 653511858129481585613593)
            ·
              refine ⟨490133893597111189210195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653511858129481585613593 490133893597111189210195)
              ·
                refine ⟨735200840395666783815293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490133893597111189210195 735200840395666783815293)
                ·
                  refine ⟨275700315148375043930735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 735200840395666783815293 275700315148375043930735)
                  ·
                    rfl

theorem cell20_604040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_604040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604040 prefixEnd_604040 := by exact prefixLift 604040
  have htrace : WordTrace (prefixWord ++ tailWord_604040) baseStart_604040 baseEnd_604040 := by
    simpa [prefixWord, tailWord_604040, baseEnd_604040] using wordTrace_append hprefix tailTrace_604040
  have hstable : (prefixWord ++ tailWord_604040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604040).length < 2 ^ (prefixWord ++ tailWord_604040).sum := by decide
  have hdescent : baseEnd_604040 < baseStart_604040 := by decide
  rcases family_descends (prefixWord ++ tailWord_604040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604058 : List Nat := [3, 1, 1, 4, 2, 1, 2, 6]
def baseStart_604058 : Nat := 118140960795 + 604058 * 2 ^ 59
def prefixEnd_604058 : Nat := 4983230072969 + 3 ^ 40 * 604058 * 2
def baseEnd_604058 : Nat := 91902843612948993776887

theorem tailTrace_604058 : CollatzResearch.WordTrace tailWord_604058 prefixEnd_604058 91902843612948993776887 := by
  unfold tailWord_604058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5507951311402126434533207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14687870163739003825421885 5507951311402126434533207)
  ·
    refine ⟨8261926967103189651799811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5507951311402126434533207 8261926967103189651799811)
    ·
      refine ⟨12392890450654784477699717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8261926967103189651799811 12392890450654784477699717)
      ·
        refine ⟨2323666959497772089568697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12392890450654784477699717 2323666959497772089568697)
        ·
          refine ⟨1742750219623329067176523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2323666959497772089568697 1742750219623329067176523)
          ·
            refine ⟨2614125329434993600764785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1742750219623329067176523 2614125329434993600764785)
            ·
              refine ⟨1960593997076245200573589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2614125329434993600764785 1960593997076245200573589)
              ·
                refine ⟨91902843612948993776887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1960593997076245200573589 91902843612948993776887)
                ·
                  rfl

theorem cell20_604058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_604058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604058 prefixEnd_604058 := by exact prefixLift 604058
  have htrace : WordTrace (prefixWord ++ tailWord_604058) baseStart_604058 baseEnd_604058 := by
    simpa [prefixWord, tailWord_604058, baseEnd_604058] using wordTrace_append hprefix tailTrace_604058
  have hstable : (prefixWord ++ tailWord_604058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604058).length < 2 ^ (prefixWord ++ tailWord_604058).sum := by decide
  have hdescent : baseEnd_604058 < baseStart_604058 := by decide
  rcases family_descends (prefixWord ++ tailWord_604058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604085 : List Nat := [1, 3, 3, 2, 1, 2, 4, 2, 2]
def baseStart_604085 : Nat := 118140960795 + 604085 * 2 ^ 59
def prefixEnd_604085 : Nat := 4983230072969 + 3 ^ 40 * 604085 * 2
def baseEnd_604085 : Nat := 275720854374554887430551

theorem tailTrace_604085 : CollatzResearch.WordTrace tailWord_604085 prefixEnd_604085 275720854374554887430551 := by
  unfold tailWord_604085
  simp only [CollatzResearch.WordTrace]
  refine ⟨22032790016510689349365709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14688526677673792899577139 22032790016510689349365709)
  ·
    refine ⟨8262296256191508506012141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22032790016510689349365709 8262296256191508506012141)
    ·
      refine ⟨3098361096071815689754553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8262296256191508506012141 3098361096071815689754553)
      ·
        refine ⟨2323770822053861767315915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3098361096071815689754553 2323770822053861767315915)
        ·
          refine ⟨3485656233080792650973873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2323770822053861767315915 3485656233080792650973873)
          ·
            refine ⟨2614242174810594488230405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3485656233080792650973873 2614242174810594488230405)
            ·
              refine ⟨490170407776986466543201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2614242174810594488230405 490170407776986466543201)
              ·
                refine ⟨367627805832739849907401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490170407776986466543201 367627805832739849907401)
                ·
                  refine ⟨275720854374554887430551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367627805832739849907401 275720854374554887430551)
                  ·
                    rfl

theorem cell20_604085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_604085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604085 prefixEnd_604085 := by exact prefixLift 604085
  have htrace : WordTrace (prefixWord ++ tailWord_604085) baseStart_604085 baseEnd_604085 := by
    simpa [prefixWord, tailWord_604085, baseEnd_604085] using wordTrace_append hprefix tailTrace_604085
  have hstable : (prefixWord ++ tailWord_604085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604085).length < 2 ^ (prefixWord ++ tailWord_604085).sum := by decide
  have hdescent : baseEnd_604085 < baseStart_604085 := by decide
  rcases family_descends (prefixWord ++ tailWord_604085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604092 : List Nat := [2, 2, 2, 5, 1, 2, 1, 5]
def baseStart_604092 : Nat := 118140960795 + 604092 * 2 ^ 59
def prefixEnd_604092 : Nat := 4983230072969 + 3 ^ 40 * 604092 * 2
def baseEnd_604092 : Nat := 91908016455097991399063

theorem tailTrace_604092 : CollatzResearch.WordTrace tailWord_604092 prefixEnd_604092 91908016455097991399063 := by
  unfold tailWord_604092
  simp only [CollatzResearch.WordTrace]
  refine ⟨11016522663742664772435265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14688696884990219696580353 11016522663742664772435265)
  ·
    refine ⟨8262391997806998579326449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11016522663742664772435265 8262391997806998579326449)
    ·
      refine ⟨6196793998355248934494837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8262391997806998579326449 6196793998355248934494837)
      ·
        refine ⟨580949437345804587608891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6196793998355248934494837 580949437345804587608891)
        ·
          refine ⟨871424156018706881413337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580949437345804587608891 871424156018706881413337)
          ·
            refine ⟨653568117014030161060003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 871424156018706881413337 653568117014030161060003)
            ·
              refine ⟨980352175521045241590005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653568117014030161060003 980352175521045241590005)
              ·
                refine ⟨91908016455097991399063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 980352175521045241590005 91908016455097991399063)
                ·
                  rfl

theorem cell20_604092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_604092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604092 prefixEnd_604092 := by exact prefixLift 604092
  have htrace : WordTrace (prefixWord ++ tailWord_604092) baseStart_604092 baseEnd_604092 := by
    simpa [prefixWord, tailWord_604092, baseEnd_604092] using wordTrace_append hprefix tailTrace_604092
  have hstable : (prefixWord ++ tailWord_604092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604092).length < 2 ^ (prefixWord ++ tailWord_604092).sum := by decide
  have hdescent : baseEnd_604092 < baseStart_604092 := by decide
  rcases family_descends (prefixWord ++ tailWord_604092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604199 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 4]
def baseStart_604199 : Nat := 118140960795 + 604199 * 2 ^ 59
def prefixEnd_604199 : Nat := 4983230072969 + 3 ^ 40 * 604199 * 2
def baseEnd_604199 : Nat := 275772887080877157630085

theorem tailTrace_604199 : CollatzResearch.WordTrace tailWord_604199 prefixEnd_604199 275772887080877157630085 := by
  unfold tailWord_604199
  simp only [CollatzResearch.WordTrace]
  refine ⟨22036947938097686819015651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14691298625398457879343767 22036947938097686819015651)
  ·
    refine ⟨33055421907146530228523477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22036947938097686819015651 33055421907146530228523477)
    ·
      refine ⟨774736450948746802231019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 33055421907146530228523477 774736450948746802231019)
      ·
        refine ⟨1162104676423120203346529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774736450948746802231019 1162104676423120203346529)
        ·
          refine ⟨871578507317340152509897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1162104676423120203346529 871578507317340152509897)
          ·
            refine ⟨653683880488005114382423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 871578507317340152509897 653683880488005114382423)
            ·
              refine ⟨980525820732007671573635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653683880488005114382423 980525820732007671573635)
              ·
                refine ⟨1470788731098011507360453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 980525820732007671573635 1470788731098011507360453)
                ·
                  refine ⟨275772887080877157630085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1470788731098011507360453 275772887080877157630085)
                  ·
                    rfl

theorem cell20_604199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 4].length) (baseStart_604199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604199 prefixEnd_604199 := by exact prefixLift 604199
  have htrace : WordTrace (prefixWord ++ tailWord_604199) baseStart_604199 baseEnd_604199 := by
    simpa [prefixWord, tailWord_604199, baseEnd_604199] using wordTrace_append hprefix tailTrace_604199
  have hstable : (prefixWord ++ tailWord_604199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604199).length < 2 ^ (prefixWord ++ tailWord_604199).sum := by decide
  have hdescent : baseEnd_604199 < baseStart_604199 := by decide
  rcases family_descends (prefixWord ++ tailWord_604199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604210 : List Nat := [3, 2, 1, 1, 2, 4, 2, 5]
def baseStart_604210 : Nat := 118140960795 + 604210 * 2 ^ 59
def prefixEnd_604210 : Nat := 4983230072969 + 3 ^ 40 * 604210 * 2
def baseEnd_604210 : Nat := 91925969260203336087791

theorem tailTrace_604210 : CollatzResearch.WordTrace tailWord_604210 prefixEnd_604210 91925969260203336087791 := by
  unfold tailWord_604210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5509337285264458924416521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14691566094038557131777389 5509337285264458924416521)
  ·
    refine ⟨4132002963948344193312391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5509337285264458924416521 4132002963948344193312391)
    ·
      refine ⟨6198004445922516289968587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4132002963948344193312391 6198004445922516289968587)
      ·
        refine ⟨9297006668883774434952881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6198004445922516289968587 9297006668883774434952881)
        ·
          refine ⟨6972755001662830826214661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9297006668883774434952881 6972755001662830826214661)
          ·
            refine ⟨1307391562811780779915249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6972755001662830826214661 1307391562811780779915249)
            ·
              refine ⟨980543672108835584936437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1307391562811780779915249 980543672108835584936437)
              ·
                refine ⟨91925969260203336087791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 980543672108835584936437 91925969260203336087791)
                ·
                  rfl

theorem cell20_604210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_604210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604210 prefixEnd_604210 := by exact prefixLift 604210
  have htrace : WordTrace (prefixWord ++ tailWord_604210) baseStart_604210 baseEnd_604210 := by
    simpa [prefixWord, tailWord_604210, baseEnd_604210] using wordTrace_append hprefix tailTrace_604210
  have hstable : (prefixWord ++ tailWord_604210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604210).length < 2 ^ (prefixWord ++ tailWord_604210).sum := by decide
  have hdescent : baseEnd_604210 < baseStart_604210 := by decide
  rcases family_descends (prefixWord ++ tailWord_604210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604231 : List Nat := [1, 1, 4, 1, 3, 1, 1, 8]
def baseStart_604231 : Nat := 118140960795 + 604231 * 2 ^ 59
def prefixEnd_604231 : Nat := 4983230072969 + 3 ^ 40 * 604231 * 2
def baseEnd_604231 : Nat := 91929164250942422854429

theorem tailTrace_604231 : CollatzResearch.WordTrace tailWord_604231 prefixEnd_604231 91929164250942422854429 := by
  unfold tailWord_604231
  simp only [CollatzResearch.WordTrace]
  refine ⟨22038115073981756284180547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14692076715987837522787031 22038115073981756284180547)
  ·
    refine ⟨33057172610972634426270821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22038115073981756284180547 33057172610972634426270821)
    ·
      refine ⟨6198219864557368954925779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33057172610972634426270821 6198219864557368954925779)
      ·
        refine ⟨9297329796836053432388669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6198219864557368954925779 9297329796836053432388669)
        ·
          refine ⟨3486498673813520037145751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9297329796836053432388669 3486498673813520037145751)
          ·
            refine ⟨5229748010720280055718627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3486498673813520037145751 5229748010720280055718627)
            ·
              refine ⟨7844622016080420083577941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5229748010720280055718627 7844622016080420083577941)
              ·
                refine ⟨91929164250942422854429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7844622016080420083577941 91929164250942422854429)
                ·
                  rfl

theorem cell20_604231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_604231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604231 prefixEnd_604231 := by exact prefixLift 604231
  have htrace : WordTrace (prefixWord ++ tailWord_604231) baseStart_604231 baseEnd_604231 := by
    simpa [prefixWord, tailWord_604231, baseEnd_604231] using wordTrace_append hprefix tailTrace_604231
  have hstable : (prefixWord ++ tailWord_604231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604231).length < 2 ^ (prefixWord ++ tailWord_604231).sum := by decide
  have hdescent : baseEnd_604231 < baseStart_604231 := by decide
  rcases family_descends (prefixWord ++ tailWord_604231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604241 : List Nat := [1, 2, 2, 1, 3, 1, 1, 7, 2]
def baseStart_604241 : Nat := 118140960795 + 604241 * 2 ^ 59
def prefixEnd_604241 : Nat := 4983230072969 + 3 ^ 40 * 604241 * 2
def baseEnd_604241 : Nat := 275792057025311678229913

theorem tailTrace_604241 : CollatzResearch.WordTrace tailWord_604241 prefixEnd_604241 275792057025311678229913 := by
  unfold tailWord_604241
  simp only [CollatzResearch.WordTrace]
  refine ⟨22038479803945527992044577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14692319869297018661363051 22038479803945527992044577)
  ·
    refine ⟨16528859852959145994033433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22038479803945527992044577 16528859852959145994033433)
    ·
      refine ⟨12396644889719359495525075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16528859852959145994033433 12396644889719359495525075)
      ·
        refine ⟨18594967334579039243287613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12396644889719359495525075 18594967334579039243287613)
        ·
          refine ⟨6973112750467139716232855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18594967334579039243287613 6973112750467139716232855)
          ·
            refine ⟨10459669125700709574349283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6973112750467139716232855 10459669125700709574349283)
            ·
              refine ⟨15689503688551064361523925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10459669125700709574349283 15689503688551064361523925)
              ·
                refine ⟨367722742700415570973217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15689503688551064361523925 367722742700415570973217)
                ·
                  refine ⟨275792057025311678229913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367722742700415570973217 275792057025311678229913)
                  ·
                    rfl

theorem cell20_604241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 2].length) (baseStart_604241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604241 prefixEnd_604241 := by exact prefixLift 604241
  have htrace : WordTrace (prefixWord ++ tailWord_604241) baseStart_604241 baseEnd_604241 := by
    simpa [prefixWord, tailWord_604241, baseEnd_604241] using wordTrace_append hprefix tailTrace_604241
  have hstable : (prefixWord ++ tailWord_604241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604241).length < 2 ^ (prefixWord ++ tailWord_604241).sum := by decide
  have hdescent : baseEnd_604241 < baseStart_604241 := by decide
  rcases family_descends (prefixWord ++ tailWord_604241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604296 : List Nat := [2, 1, 3, 4, 1, 1, 1, 5, 2]
def baseStart_604296 : Nat := 118140960795 + 604296 * 2 ^ 59
def prefixEnd_604296 : Nat := 4983230072969 + 3 ^ 40 * 604296 * 2
def baseEnd_604296 : Nat := 275817160523975931396355

theorem tailTrace_604296 : CollatzResearch.WordTrace tailWord_604296 prefixEnd_604296 275817160523975931396355 := by
  unfold tailWord_604296
  simp only [CollatzResearch.WordTrace]
  refine ⟨11020242909373136192648371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14693657212497514923531161 11020242909373136192648371)
  ·
    refine ⟨16530364364059704288972557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11020242909373136192648371 16530364364059704288972557)
    ·
      refine ⟨6198886636522389108364709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16530364364059704288972557 6198886636522389108364709)
      ·
        refine ⟨1162291244347947957818383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6198886636522389108364709 1162291244347947957818383)
        ·
          refine ⟨1743436866521921936727575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162291244347947957818383 1743436866521921936727575)
          ·
            refine ⟨2615155299782882905091363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743436866521921936727575 2615155299782882905091363)
            ·
              refine ⟨3922732949674324357637045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615155299782882905091363 3922732949674324357637045)
              ·
                refine ⟨367756214031967908528473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3922732949674324357637045 367756214031967908528473)
                ·
                  refine ⟨275817160523975931396355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367756214031967908528473 275817160523975931396355)
                  ·
                    rfl

theorem cell20_604296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 2].length) (baseStart_604296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604296 prefixEnd_604296 := by exact prefixLift 604296
  have htrace : WordTrace (prefixWord ++ tailWord_604296) baseStart_604296 baseEnd_604296 := by
    simpa [prefixWord, tailWord_604296, baseEnd_604296] using wordTrace_append hprefix tailTrace_604296
  have hstable : (prefixWord ++ tailWord_604296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604296).length < 2 ^ (prefixWord ++ tailWord_604296).sum := by decide
  have hdescent : baseEnd_604296 < baseStart_604296 := by decide
  rcases family_descends (prefixWord ++ tailWord_604296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604317 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 4]
def baseStart_604317 : Nat := 118140960795 + 604317 * 2 ^ 59
def prefixEnd_604317 : Nat := 4983230072969 + 3 ^ 40 * 604317 * 2
def baseEnd_604317 : Nat := 275826745496193191696269

theorem tailTrace_604317 : CollatzResearch.WordTrace tailWord_604317 prefixEnd_604317 275826745496193191696269 := by
  unfold tailWord_604317
  simp only [CollatzResearch.WordTrace]
  refine ⟨22041251751670192971811205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14694167834446795314540803 22041251751670192971811205)
  ·
    refine ⟨4132734703438161182214601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22041251751670192971811205 4132734703438161182214601)
    ·
      refine ⟨3099551027578620886660951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4132734703438161182214601 3099551027578620886660951)
      ·
        refine ⟨4649326541367931329991427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3099551027578620886660951 4649326541367931329991427)
        ·
          refine ⟨6973989812051896994987141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4649326541367931329991427 6973989812051896994987141)
          ·
            refine ⟨1307623089759730686560089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6973989812051896994987141 1307623089759730686560089)
            ·
              refine ⟨980717317319798014920067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1307623089759730686560089 980717317319798014920067)
              ·
                refine ⟨1471075975979697022380101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 980717317319798014920067 1471075975979697022380101)
                ·
                  refine ⟨275826745496193191696269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1471075975979697022380101 275826745496193191696269)
                  ·
                    rfl

theorem cell20_604317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_604317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604317 prefixEnd_604317 := by exact prefixLift 604317
  have htrace : WordTrace (prefixWord ++ tailWord_604317) baseStart_604317 baseEnd_604317 := by
    simpa [prefixWord, tailWord_604317, baseEnd_604317] using wordTrace_append hprefix tailTrace_604317
  have hstable : (prefixWord ++ tailWord_604317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604317).length < 2 ^ (prefixWord ++ tailWord_604317).sum := by decide
  have hdescent : baseEnd_604317 < baseStart_604317 := by decide
  rcases family_descends (prefixWord ++ tailWord_604317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604338 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_604338 : Nat := 118140960795 + 604338 * 2 ^ 59
def prefixEnd_604338 : Nat := 4983230072969 + 3 ^ 40 * 604338 * 2
def baseEnd_604338 : Nat := 275836330468410451996183

theorem tailTrace_604338 : CollatzResearch.WordTrace tailWord_604338 prefixEnd_604338 275836330468410451996183 := by
  unfold tailWord_604338
  simp only [CollatzResearch.WordTrace]
  refine ⟨5510504421148528389581417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14694678456396075705550445 5510504421148528389581417)
  ·
    refine ⟨4132878315861396292186063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5510504421148528389581417 4132878315861396292186063)
    ·
      refine ⟨6199317473792094438279095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4132878315861396292186063 6199317473792094438279095)
      ·
        refine ⟨9298976210688141657418643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6199317473792094438279095 9298976210688141657418643)
        ·
          refine ⟨13948464316032212486127965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9298976210688141657418643 13948464316032212486127965)
          ·
            refine ⟨5230674118512079682297987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13948464316032212486127965 5230674118512079682297987)
            ·
              refine ⟨7846011177768119523446981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5230674118512079682297987 7846011177768119523446981)
              ·
                refine ⟨1471127095831522410646309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7846011177768119523446981 1471127095831522410646309)
                ·
                  refine ⟨275836330468410451996183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1471127095831522410646309 275836330468410451996183)
                  ·
                    rfl

theorem cell20_604338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_604338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604338 prefixEnd_604338 := by exact prefixLift 604338
  have htrace : WordTrace (prefixWord ++ tailWord_604338) baseStart_604338 baseEnd_604338 := by
    simpa [prefixWord, tailWord_604338, baseEnd_604338] using wordTrace_append hprefix tailTrace_604338
  have hstable : (prefixWord ++ tailWord_604338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604338).length < 2 ^ (prefixWord ++ tailWord_604338).sum := by decide
  have hdescent : baseEnd_604338 < baseStart_604338 := by decide
  rcases family_descends (prefixWord ++ tailWord_604338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604341 : List Nat := [1, 3, 3, 4, 1, 1, 1, 6]
def baseStart_604341 : Nat := 118140960795 + 604341 * 2 ^ 59
def prefixEnd_604341 : Nat := 4983230072969 + 3 ^ 40 * 604341 * 2
def baseEnd_604341 : Nat := 91945899916718591632057

theorem tailTrace_604341 : CollatzResearch.WordTrace tailWord_604341 prefixEnd_604341 91945899916718591632057 := by
  unfold tailWord_604341
  simp only [CollatzResearch.WordTrace]
  refine ⟨22042127103583245070684877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14694751402388830047123251 22042127103583245070684877)
  ·
    refine ⟨8265797663843716901506829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22042127103583245070684877 8265797663843716901506829)
    ·
      refine ⟨3099674123941393838065061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8265797663843716901506829 3099674123941393838065061)
      ·
        refine ⟨581188898239011344637199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3099674123941393838065061 581188898239011344637199)
        ·
          refine ⟨871783347358517016955799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581188898239011344637199 871783347358517016955799)
          ·
            refine ⟨1307675021037775525433699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871783347358517016955799 1307675021037775525433699)
            ·
              refine ⟨1961512531556663288150549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307675021037775525433699 1961512531556663288150549)
              ·
                refine ⟨91945899916718591632057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1961512531556663288150549 91945899916718591632057)
                ·
                  rfl

theorem cell20_604341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 6].length) (baseStart_604341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604341 prefixEnd_604341 := by exact prefixLift 604341
  have htrace : WordTrace (prefixWord ++ tailWord_604341) baseStart_604341 baseEnd_604341 := by
    simpa [prefixWord, tailWord_604341, baseEnd_604341] using wordTrace_append hprefix tailTrace_604341
  have hstable : (prefixWord ++ tailWord_604341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604341).length < 2 ^ (prefixWord ++ tailWord_604341).sum := by decide
  have hdescent : baseEnd_604341 < baseStart_604341 := by decide
  rcases family_descends (prefixWord ++ tailWord_604341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604345 : List Nat := [1, 2, 1, 4, 1, 2, 3, 6]
def baseStart_604345 : Nat := 118140960795 + 604345 * 2 ^ 59
def prefixEnd_604345 : Nat := 4983230072969 + 3 ^ 40 * 604345 * 2
def baseEnd_604345 : Nat := 91946508486383179587607

theorem tailTrace_604345 : CollatzResearch.WordTrace tailWord_604345 prefixEnd_604345 91946508486383179587607 := by
  unfold tailWord_604345
  simp only [CollatzResearch.WordTrace]
  refine ⟨22042272995568753753830489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14694848663712502502553659 22042272995568753753830489)
  ·
    refine ⟨16531704746676565315372867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22042272995568753753830489 16531704746676565315372867)
    ·
      refine ⟨24797557120014847973059301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16531704746676565315372867 24797557120014847973059301)
      ·
        refine ⟨4649541960002783994948619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24797557120014847973059301 4649541960002783994948619)
        ·
          refine ⟨6974312940004175992422929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4649541960002783994948619 6974312940004175992422929)
          ·
            refine ⟨5230734705003131994317197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6974312940004175992422929 5230734705003131994317197)
            ·
              refine ⟨1961525514376174497868949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5230734705003131994317197 1961525514376174497868949)
              ·
                refine ⟨91946508486383179587607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1961525514376174497868949 91946508486383179587607)
                ·
                  rfl

theorem cell20_604345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 6].length) (baseStart_604345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604345 prefixEnd_604345 := by exact prefixLift 604345
  have htrace : WordTrace (prefixWord ++ tailWord_604345) baseStart_604345 baseEnd_604345 := by
    simpa [prefixWord, tailWord_604345, baseEnd_604345] using wordTrace_append hprefix tailTrace_604345
  have hstable : (prefixWord ++ tailWord_604345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604345).length < 2 ^ (prefixWord ++ tailWord_604345).sum := by decide
  have hdescent : baseEnd_604345 < baseStart_604345 := by decide
  rcases family_descends (prefixWord ++ tailWord_604345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604423 : List Nat := [1, 1, 4, 5, 2, 1, 2, 2, 2]
def baseStart_604423 : Nat := 118140960795 + 604423 * 2 ^ 59
def prefixEnd_604423 : Nat := 4983230072969 + 3 ^ 40 * 604423 * 2
def baseEnd_604423 : Nat := 275875126784527934162503

theorem tailTrace_604423 : CollatzResearch.WordTrace tailWord_604423 prefixEnd_604423 275875126784527934162503 := by
  unfold tailWord_604423
  simp only [CollatzResearch.WordTrace]
  refine ⟨22045117889286173075169923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14696745259524115383446615 22045117889286173075169923)
  ·
    refine ⟨33067676833929259612754885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22045117889286173075169923 33067676833929259612754885)
    ·
      refine ⟨6200189406361736177391541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33067676833929259612754885 6200189406361736177391541)
      ·
        refine ⟨581267756846412766630457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6200189406361736177391541 581267756846412766630457)
        ·
          refine ⟨435950817634809574972843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 581267756846412766630457 435950817634809574972843)
          ·
            refine ⟨653926226452214362459265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435950817634809574972843 653926226452214362459265)
            ·
              refine ⟨490444669839160771844449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653926226452214362459265 490444669839160771844449)
              ·
                refine ⟨367833502379370578883337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490444669839160771844449 367833502379370578883337)
                ·
                  refine ⟨275875126784527934162503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367833502379370578883337 275875126784527934162503)
                  ·
                    rfl

theorem cell20_604423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 2].length) (baseStart_604423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604423 prefixEnd_604423 := by exact prefixLift 604423
  have htrace : WordTrace (prefixWord ++ tailWord_604423) baseStart_604423 baseEnd_604423 := by
    simpa [prefixWord, tailWord_604423, baseEnd_604423] using wordTrace_append hprefix tailTrace_604423
  have hstable : (prefixWord ++ tailWord_604423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604423).length < 2 ^ (prefixWord ++ tailWord_604423).sum := by decide
  have hdescent : baseEnd_604423 < baseStart_604423 := by decide
  rcases family_descends (prefixWord ++ tailWord_604423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604424 : List Nat := [2, 1, 3, 2, 3, 2, 2, 2, 3]
def baseStart_604424 : Nat := 118140960795 + 604424 * 2 ^ 59
def prefixEnd_604424 : Nat := 4983230072969 + 3 ^ 40 * 604424 * 2
def baseEnd_604424 : Nat := 275875583211776375129165

theorem tailTrace_604424 : CollatzResearch.WordTrace tailWord_604424 prefixEnd_604424 275875583211776375129165 := by
  unfold tailWord_604424
  simp only [CollatzResearch.WordTrace]
  refine ⟨11022577181141275122978163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14696769574855033497304217 11022577181141275122978163)
  ·
    refine ⟨16533865771711912684467245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11022577181141275122978163 16533865771711912684467245)
    ·
      refine ⟨6200199664391967256675217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16533865771711912684467245 6200199664391967256675217)
      ·
        refine ⟨4650149748293975442506413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6200199664391967256675217 4650149748293975442506413)
        ·
          refine ⟨1743806155610240790939905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4650149748293975442506413 1743806155610240790939905)
          ·
            refine ⟨1307854616707680593204929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1743806155610240790939905 1307854616707680593204929)
            ·
              refine ⟨980890962530760444903697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1307854616707680593204929 980890962530760444903697)
              ·
                refine ⟨735668221898070333677773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 980890962530760444903697 735668221898070333677773)
                ·
                  refine ⟨275875583211776375129165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 735668221898070333677773 275875583211776375129165)
                  ·
                    rfl

theorem cell20_604424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_604424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604424 prefixEnd_604424 := by exact prefixLift 604424
  have htrace : WordTrace (prefixWord ++ tailWord_604424) baseStart_604424 baseEnd_604424 := by
    simpa [prefixWord, tailWord_604424, baseEnd_604424] using wordTrace_append hprefix tailTrace_604424
  have hstable : (prefixWord ++ tailWord_604424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604424).length < 2 ^ (prefixWord ++ tailWord_604424).sum := by decide
  have hdescent : baseEnd_604424 < baseStart_604424 := by decide
  rcases family_descends (prefixWord ++ tailWord_604424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604435 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 8]
def baseStart_604435 : Nat := 118140960795 + 604435 * 2 ^ 59
def prefixEnd_604435 : Nat := 4983230072969 + 3 ^ 40 * 604435 * 2
def baseEnd_604435 : Nat := 275880603911509225762453

theorem tailTrace_604435 : CollatzResearch.WordTrace tailWord_604435 prefixEnd_604435 275880603911509225762453 := by
  unfold tailWord_604435
  simp only [CollatzResearch.WordTrace]
  refine ⟨22045555565242699124606759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14697037043495132749737839 22045555565242699124606759)
  ·
    refine ⟨33068333347864048686910139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22045555565242699124606759 33068333347864048686910139)
    ·
      refine ⟨49602500021796073030365209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33068333347864048686910139 49602500021796073030365209)
      ·
        refine ⟨37201875016347054772773907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49602500021796073030365209 37201875016347054772773907)
        ·
          refine ⟨55802812524520582159160861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37201875016347054772773907 55802812524520582159160861)
          ·
            refine ⟨20926054696695218309685323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55802812524520582159160861 20926054696695218309685323)
            ·
              refine ⟨31389082045042827464527985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20926054696695218309685323 31389082045042827464527985)
              ·
                refine ⟨23541811533782120598395989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31389082045042827464527985 23541811533782120598395989)
                ·
                  refine ⟨275880603911509225762453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23541811533782120598395989 275880603911509225762453)
                  ·
                    rfl

theorem cell20_604435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_604435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604435 prefixEnd_604435 := by exact prefixLift 604435
  have htrace : WordTrace (prefixWord ++ tailWord_604435) baseStart_604435 baseEnd_604435 := by
    simpa [prefixWord, tailWord_604435, baseEnd_604435] using wordTrace_append hprefix tailTrace_604435
  have hstable : (prefixWord ++ tailWord_604435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604435).length < 2 ^ (prefixWord ++ tailWord_604435).sum := by decide
  have hdescent : baseEnd_604435 < baseStart_604435 := by decide
  rcases family_descends (prefixWord ++ tailWord_604435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604452 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_604452 : Nat := 118140960795 + 604452 * 2 ^ 59
def prefixEnd_604452 : Nat := 4983230072969 + 3 ^ 40 * 604452 * 2
def baseEnd_604452 : Nat := 275888363174732722195717

theorem tailTrace_604452 : CollatzResearch.WordTrace tailWord_604452 prefixEnd_604452 275888363174732722195717 := by
  unfold tailWord_604452
  simp only [CollatzResearch.WordTrace]
  refine ⟨11023087803090555513987805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14697450404120740685317073 11023087803090555513987805)
  ·
    refine ⟨4133657926158958317745427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11023087803090555513987805 4133657926158958317745427)
    ·
      refine ⟨6200486889238437476618141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4133657926158958317745427 6200486889238437476618141)
      ·
        refine ⟨2325182583464414053731803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6200486889238437476618141 2325182583464414053731803)
        ·
          refine ⟨3487773875196621080597705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325182583464414053731803 3487773875196621080597705)
          ·
            refine ⟨2615830406397465810448279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3487773875196621080597705 2615830406397465810448279)
            ·
              refine ⟨3923745609596198715672419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615830406397465810448279 3923745609596198715672419)
              ·
                refine ⟨5885618414394298073508629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923745609596198715672419 5885618414394298073508629)
                ·
                  refine ⟨275888363174732722195717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5885618414394298073508629 275888363174732722195717)
                  ·
                    rfl

theorem cell20_604452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_604452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604452 prefixEnd_604452 := by exact prefixLift 604452
  have htrace : WordTrace (prefixWord ++ tailWord_604452) baseStart_604452 baseEnd_604452 := by
    simpa [prefixWord, tailWord_604452, baseEnd_604452] using wordTrace_append hprefix tailTrace_604452
  have hstable : (prefixWord ++ tailWord_604452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604452).length < 2 ^ (prefixWord ++ tailWord_604452).sum := by decide
  have hdescent : baseEnd_604452 < baseStart_604452 := by decide
  rcases family_descends (prefixWord ++ tailWord_604452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604483 : List Nat := [1, 1, 1, 3, 1, 3, 5, 2, 3]
def baseStart_604483 : Nat := 118140960795 + 604483 * 2 ^ 59
def prefixEnd_604483 : Nat := 4983230072969 + 3 ^ 40 * 604483 * 2
def baseEnd_604483 : Nat := 275902512419434392162257

theorem tailTrace_604483 : CollatzResearch.WordTrace tailWord_604483 prefixEnd_604483 275902512419434392162257 := by
  unfold tailWord_604483
  simp only [CollatzResearch.WordTrace]
  refine ⟨22047306269068803322354103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14698204179379202214902735 22047306269068803322354103)
  ·
    refine ⟨33070959403603204983531155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22047306269068803322354103 33070959403603204983531155)
    ·
      refine ⟨49606439105404807475296733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33070959403603204983531155 49606439105404807475296733)
      ·
        refine ⟨18602414664526802803236275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49606439105404807475296733 18602414664526802803236275)
        ·
          refine ⟨27903621996790204204854413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18602414664526802803236275 27903621996790204204854413)
          ·
            refine ⟨10463858248796326576820405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27903621996790204204854413 10463858248796326576820405)
            ·
              refine ⟨980986710824655616576913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10463858248796326576820405 980986710824655616576913)
              ·
                refine ⟨735740033118491712432685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 980986710824655616576913 735740033118491712432685)
                ·
                  refine ⟨275902512419434392162257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 735740033118491712432685 275902512419434392162257)
                  ·
                    rfl

theorem cell20_604483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 3].length) (baseStart_604483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604483 prefixEnd_604483 := by exact prefixLift 604483
  have htrace : WordTrace (prefixWord ++ tailWord_604483) baseStart_604483 baseEnd_604483 := by
    simpa [prefixWord, tailWord_604483, baseEnd_604483] using wordTrace_append hprefix tailTrace_604483
  have hstable : (prefixWord ++ tailWord_604483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604483).length < 2 ^ (prefixWord ++ tailWord_604483).sum := by decide
  have hdescent : baseEnd_604483 < baseStart_604483 := by decide
  rcases family_descends (prefixWord ++ tailWord_604483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604514 : List Nat := [3, 3, 2, 1, 1, 3, 1, 6]
def baseStart_604514 : Nat := 118140960795 + 604514 * 2 ^ 59
def prefixEnd_604514 : Nat := 4983230072969 + 3 ^ 40 * 604514 * 2
def baseEnd_604514 : Nat := 91972220554712020709599

theorem tailTrace_604514 : CollatzResearch.WordTrace tailWord_604514 prefixEnd_604514 91972220554712020709599 := by
  unfold tailWord_604514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5512109232989123904183149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14698957954637663744488397 5512109232989123904183149)
  ·
    refine ⟨2067040962370921464068681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5512109232989123904183149 2067040962370921464068681)
    ·
      refine ⟨1550280721778191098051511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2067040962370921464068681 1550280721778191098051511)
      ·
        refine ⟨2325421082667286647077267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550280721778191098051511 2325421082667286647077267)
        ·
          refine ⟨3488131624000929970615901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325421082667286647077267 3488131624000929970615901)
          ·
            refine ⟨1308049359000348738980963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3488131624000929970615901 1308049359000348738980963)
            ·
              refine ⟨1962074038500523108471445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308049359000348738980963 1962074038500523108471445)
              ·
                refine ⟨91972220554712020709599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1962074038500523108471445 91972220554712020709599)
                ·
                  rfl

theorem cell20_604514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_604514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604514 prefixEnd_604514 := by exact prefixLift 604514
  have htrace : WordTrace (prefixWord ++ tailWord_604514) baseStart_604514 baseEnd_604514 := by
    simpa [prefixWord, tailWord_604514, baseEnd_604514] using wordTrace_append hprefix tailTrace_604514
  have hstable : (prefixWord ++ tailWord_604514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604514).length < 2 ^ (prefixWord ++ tailWord_604514).sum := by decide
  have hdescent : baseEnd_604514 < baseStart_604514 := by decide
  rcases family_descends (prefixWord ++ tailWord_604514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604545 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 4]
def baseStart_604545 : Nat := 118140960795 + 604545 * 2 ^ 59
def prefixEnd_604545 : Nat := 4983230072969 + 3 ^ 40 * 604545 * 2
def baseEnd_604545 : Nat := 275930810908837732095337

theorem tailTrace_604545 : CollatzResearch.WordTrace tailWord_604545 prefixEnd_604545 275930810908837732095337 := by
  unfold tailWord_604545
  simp only [CollatzResearch.WordTrace]
  refine ⟨22049567594844187911111089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14699711729896125274074059 22049567594844187911111089)
  ·
    refine ⟨16537175696133140933333317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22049567594844187911111089 16537175696133140933333317)
    ·
      refine ⟨3100720443024963924999997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16537175696133140933333317 3100720443024963924999997)
      ·
        refine ⟨1162770166134361471874999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3100720443024963924999997 1162770166134361471874999)
        ·
          refine ⟨1744155249201542207812499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162770166134361471874999 1744155249201542207812499)
          ·
            refine ⟨2616232873802313311718749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1744155249201542207812499 2616232873802313311718749)
            ·
              refine ⟨981087327675867491894531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2616232873802313311718749 981087327675867491894531)
              ·
                refine ⟨1471630991513801237841797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981087327675867491894531 1471630991513801237841797)
                ·
                  refine ⟨275930810908837732095337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1471630991513801237841797 275930810908837732095337)
                  ·
                    rfl

theorem cell20_604545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_604545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604545 prefixEnd_604545 := by exact prefixLift 604545
  have htrace : WordTrace (prefixWord ++ tailWord_604545) baseStart_604545 baseEnd_604545 := by
    simpa [prefixWord, tailWord_604545, baseEnd_604545] using wordTrace_append hprefix tailTrace_604545
  have hstable : (prefixWord ++ tailWord_604545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604545).length < 2 ^ (prefixWord ++ tailWord_604545).sum := by decide
  have hdescent : baseEnd_604545 < baseStart_604545 := by decide
  rcases family_descends (prefixWord ++ tailWord_604545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604580 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_604580 : Nat := 118140960795 + 604580 * 2 ^ 59
def prefixEnd_604580 : Nat := 4983230072969 + 3 ^ 40 * 604580 * 2
def baseEnd_604580 : Nat := 275946785862533165928527

theorem tailTrace_604580 : CollatzResearch.WordTrace tailWord_604580 prefixEnd_604580 275946785862533165928527 := by
  unfold tailWord_604580
  simp only [CollatzResearch.WordTrace]
  refine ⟨11025422074858694444317597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14700562766478259259090129 11025422074858694444317597)
  ·
    refine ⟨4134533278072010416619099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11025422074858694444317597 4134533278072010416619099)
    ·
      refine ⟨6201799917108015624928649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4134533278072010416619099 6201799917108015624928649)
      ·
        refine ⟨4651349937831011718696487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6201799917108015624928649 4651349937831011718696487)
        ·
          refine ⟨6977024906746517578044731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4651349937831011718696487 6977024906746517578044731)
          ·
            refine ⟨10465537360119776367067097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6977024906746517578044731 10465537360119776367067097)
            ·
              refine ⟨7849153020089832275300323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10465537360119776367067097 7849153020089832275300323)
              ·
                refine ⟨11773729530134748412950485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7849153020089832275300323 11773729530134748412950485)
                ·
                  refine ⟨275946785862533165928527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11773729530134748412950485 275946785862533165928527)
                  ·
                    rfl

theorem cell20_604580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_604580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604580 prefixEnd_604580 := by exact prefixLift 604580
  have htrace : WordTrace (prefixWord ++ tailWord_604580) baseStart_604580 baseEnd_604580 := by
    simpa [prefixWord, tailWord_604580, baseEnd_604580] using wordTrace_append hprefix tailTrace_604580
  have hstable : (prefixWord ++ tailWord_604580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604580).length < 2 ^ (prefixWord ++ tailWord_604580).sum := by decide
  have hdescent : baseEnd_604580 < baseStart_604580 := by decide
  rcases family_descends (prefixWord ++ tailWord_604580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604586 : List Nat := [3, 1, 6, 1, 2, 7]
def baseStart_604586 : Nat := 118140960795 + 604586 * 2 ^ 59
def prefixEnd_604586 : Nat := 4983230072969 + 3 ^ 40 * 604586 * 2
def baseEnd_604586 : Nat := 10220352756519400434389

theorem tailTrace_604586 : CollatzResearch.WordTrace tailWord_604586 prefixEnd_604586 10220352756519400434389 := by
  unfold tailWord_604586
  simp only [CollatzResearch.WordTrace]
  refine ⟨5512765746923912978338403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14700708658463767942235741 5512765746923912978338403)
  ·
    refine ⟨8269148620385869467507605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5512765746923912978338403 8269148620385869467507605)
    ·
      refine ⟨387616341580587631289419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8269148620385869467507605 387616341580587631289419)
      ·
        refine ⟨581424512370881446934129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387616341580587631289419 581424512370881446934129)
        ·
          refine ⟨436068384278161085200597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 581424512370881446934129 436068384278161085200597)
          ·
            refine ⟨10220352756519400434389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 436068384278161085200597 10220352756519400434389)
            ·
              rfl

theorem cell20_604586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 7].length) (baseStart_604586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604586 prefixEnd_604586 := by exact prefixLift 604586
  have htrace : WordTrace (prefixWord ++ tailWord_604586) baseStart_604586 baseEnd_604586 := by
    simpa [prefixWord, tailWord_604586, baseEnd_604586] using wordTrace_append hprefix tailTrace_604586
  have hstable : (prefixWord ++ tailWord_604586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604586).length < 2 ^ (prefixWord ++ tailWord_604586).sum := by decide
  have hdescent : baseEnd_604586 < baseStart_604586 := by decide
  rcases family_descends (prefixWord ++ tailWord_604586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604596 : List Nat := [2, 5, 2, 2, 1, 1, 1, 4, 2]
def baseStart_604596 : Nat := 118140960795 + 604596 * 2 ^ 59
def prefixEnd_604596 : Nat := 4983230072969 + 3 ^ 40 * 604596 * 2
def baseEnd_604596 : Nat := 275954088698508221395129

theorem tailTrace_604596 : CollatzResearch.WordTrace tailWord_604596 prefixEnd_604596 275954088698508221395129 := by
  unfold tailWord_604596
  simp only [CollatzResearch.WordTrace]
  refine ⟨11025713858829711810608821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14700951811772949080811761 11025713858829711810608821)
  ·
    refine ⟨1033660674265285482244577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11025713858829711810608821 1033660674265285482244577)
    ·
      refine ⟨775245505698964111683433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1033660674265285482244577 775245505698964111683433)
      ·
        refine ⟨581434129274223083762575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 775245505698964111683433 581434129274223083762575)
        ·
          refine ⟨872151193911334625643863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581434129274223083762575 872151193911334625643863)
          ·
            refine ⟨1308226790867001938465795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872151193911334625643863 1308226790867001938465795)
            ·
              refine ⟨1962340186300502907698693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308226790867001938465795 1962340186300502907698693)
              ·
                refine ⟨367938784931344295193505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1962340186300502907698693 367938784931344295193505)
                ·
                  refine ⟨275954088698508221395129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367938784931344295193505 275954088698508221395129)
                  ·
                    rfl

theorem cell20_604596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_604596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604596 prefixEnd_604596 := by exact prefixLift 604596
  have htrace : WordTrace (prefixWord ++ tailWord_604596) baseStart_604596 baseEnd_604596 := by
    simpa [prefixWord, tailWord_604596, baseEnd_604596] using wordTrace_append hprefix tailTrace_604596
  have hstable : (prefixWord ++ tailWord_604596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604596).length < 2 ^ (prefixWord ++ tailWord_604596).sum := by decide
  have hdescent : baseEnd_604596 < baseStart_604596 := by decide
  rcases family_descends (prefixWord ++ tailWord_604596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604656 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_604656 : Nat := 118140960795 + 604656 * 2 ^ 59
def prefixEnd_604656 : Nat := 4983230072969 + 3 ^ 40 * 604656 * 2
def baseEnd_604656 : Nat := 275981474333414679394883

theorem tailTrace_604656 : CollatzResearch.WordTrace tailWord_604656 prefixEnd_604656 275981474333414679394883 := by
  unfold tailWord_604656
  simp only [CollatzResearch.WordTrace]
  refine ⟨11026808048721026934200911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14702410731628035912267881 11026808048721026934200911)
  ·
    refine ⟨16540212073081540401301367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11026808048721026934200911 16540212073081540401301367)
    ·
      refine ⟨24810318109622310601952051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16540212073081540401301367 24810318109622310601952051)
      ·
        refine ⟨37215477164433465902928077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24810318109622310601952051 37215477164433465902928077)
        ·
          refine ⟨13955803936662549713598029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37215477164433465902928077 13955803936662549713598029)
          ·
            refine ⟨5233426476248456142599261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13955803936662549713598029 5233426476248456142599261)
            ·
              refine ⟨1962534928593171053474723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5233426476248456142599261 1962534928593171053474723)
              ·
                refine ⟨2943802392889756580212085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1962534928593171053474723 2943802392889756580212085)
                ·
                  refine ⟨275981474333414679394883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2943802392889756580212085 275981474333414679394883)
                  ·
                    rfl

theorem cell20_604656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_604656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604656 prefixEnd_604656 := by exact prefixLift 604656
  have htrace : WordTrace (prefixWord ++ tailWord_604656) baseStart_604656 baseEnd_604656 := by
    simpa [prefixWord, tailWord_604656, baseEnd_604656] using wordTrace_append hprefix tailTrace_604656
  have hstable : (prefixWord ++ tailWord_604656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604656).length < 2 ^ (prefixWord ++ tailWord_604656).sum := by decide
  have hdescent : baseEnd_604656 < baseStart_604656 := by decide
  rcases family_descends (prefixWord ++ tailWord_604656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604704 : List Nat := [2, 1, 1, 6, 2, 2, 6]
def baseStart_604704 : Nat := 118140960795 + 604704 * 2 ^ 59
def prefixEnd_604704 : Nat := 4983230072969 + 3 ^ 40 * 604704 * 2
def baseEnd_604704 : Nat := 30667042537926649532743

theorem tailTrace_604704 : CollatzResearch.WordTrace tailWord_604704 prefixEnd_604704 30667042537926649532743 := by
  unfold tailWord_604704
  simp only [CollatzResearch.WordTrace]
  refine ⟨11027683400634079033074583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14703577867512105377432777 11027683400634079033074583)
  ·
    refine ⟨16541525100951118549611875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11027683400634079033074583 16541525100951118549611875)
    ·
      refine ⟨24812287651426677824417813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16541525100951118549611875 24812287651426677824417813)
      ·
        refine ⟨1163075983660625523019585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24812287651426677824417813 1163075983660625523019585)
        ·
          refine ⟨872306987745469142264689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1163075983660625523019585 872306987745469142264689)
          ·
            refine ⟨654230240809101856698517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 872306987745469142264689 654230240809101856698517)
            ·
              refine ⟨30667042537926649532743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 654230240809101856698517 30667042537926649532743)
              ·
                rfl

theorem cell20_604704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 6].length) (baseStart_604704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604704 prefixEnd_604704 := by exact prefixLift 604704
  have htrace : WordTrace (prefixWord ++ tailWord_604704) baseStart_604704 baseEnd_604704 := by
    simpa [prefixWord, tailWord_604704, baseEnd_604704] using wordTrace_append hprefix tailTrace_604704
  have hstable : (prefixWord ++ tailWord_604704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604704).length < 2 ^ (prefixWord ++ tailWord_604704).sum := by decide
  have hdescent : baseEnd_604704 < baseStart_604704 := by decide
  rcases family_descends (prefixWord ++ tailWord_604704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604725 : List Nat := [1, 3, 3, 1, 1, 2, 4, 5]
def baseStart_604725 : Nat := 118140960795 + 604725 * 2 ^ 59
def prefixEnd_604725 : Nat := 4983230072969 + 3 ^ 40 * 604725 * 2
def baseEnd_604725 : Nat := 92004322604519035364867

theorem tailTrace_604725 : CollatzResearch.WordTrace tailWord_604725 prefixEnd_604725 92004322604519035364867 := by
  unfold tailWord_604725
  simp only [CollatzResearch.WordTrace]
  refine ⟨22056132734192078652663629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14704088489461385768442419 22056132734192078652663629)
  ·
    refine ⟨8271049775322029494748861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22056132734192078652663629 8271049775322029494748861)
    ·
      refine ⟨3101643665745761060530823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8271049775322029494748861 3101643665745761060530823)
      ·
        refine ⟨4652465498618641590796235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101643665745761060530823 4652465498618641590796235)
        ·
          refine ⟨6978698247927962386194353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4652465498618641590796235 6978698247927962386194353)
          ·
            refine ⟨5234023685945971789645765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6978698247927962386194353 5234023685945971789645765)
            ·
              refine ⟨981379441114869710558581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5234023685945971789645765 981379441114869710558581)
              ·
                refine ⟨92004322604519035364867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 981379441114869710558581 92004322604519035364867)
                ·
                  rfl

theorem cell20_604725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 5].length) (baseStart_604725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604725 prefixEnd_604725 := by exact prefixLift 604725
  have htrace : WordTrace (prefixWord ++ tailWord_604725) baseStart_604725 baseEnd_604725 := by
    simpa [prefixWord, tailWord_604725, baseEnd_604725] using wordTrace_append hprefix tailTrace_604725
  have hstable : (prefixWord ++ tailWord_604725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604725).length < 2 ^ (prefixWord ++ tailWord_604725).sum := by decide
  have hdescent : baseEnd_604725 < baseStart_604725 := by decide
  rcases family_descends (prefixWord ++ tailWord_604725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604739 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 4]
def baseStart_604739 : Nat := 118140960795 + 604739 * 2 ^ 59
def prefixEnd_604739 : Nat := 4983230072969 + 3 ^ 40 * 604739 * 2
def baseEnd_604739 : Nat := 276019357795035279627877

theorem tailTrace_604739 : CollatzResearch.WordTrace tailWord_604739 prefixEnd_604739 276019357795035279627877 := by
  unfold tailWord_604739
  simp only [CollatzResearch.WordTrace]
  refine ⟨22056643356141359043673271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14704428904094239362448847 22056643356141359043673271)
  ·
    refine ⟨33084965034212038565509907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22056643356141359043673271 33084965034212038565509907)
    ·
      refine ⟨49627447551318057848264861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33084965034212038565509907 49627447551318057848264861)
      ·
        refine ⟨18610292831744271693099323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49627447551318057848264861 18610292831744271693099323)
        ·
          refine ⟨27915439247616407539648985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18610292831744271693099323 27915439247616407539648985)
          ·
            refine ⟨20936579435712305654736739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27915439247616407539648985 20936579435712305654736739)
            ·
              refine ⟨31404869153568458482105109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20936579435712305654736739 31404869153568458482105109)
              ·
                refine ⟨1472103241573521491348677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31404869153568458482105109 1472103241573521491348677)
                ·
                  refine ⟨276019357795035279627877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1472103241573521491348677 276019357795035279627877)
                  ·
                    rfl

theorem cell20_604739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_604739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604739 prefixEnd_604739 := by exact prefixLift 604739
  have htrace : WordTrace (prefixWord ++ tailWord_604739) baseStart_604739 baseEnd_604739 := by
    simpa [prefixWord, tailWord_604739, baseEnd_604739] using wordTrace_append hprefix tailTrace_604739
  have hstable : (prefixWord ++ tailWord_604739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604739).length < 2 ^ (prefixWord ++ tailWord_604739).sum := by decide
  have hdescent : baseEnd_604739 < baseStart_604739 := by decide
  rcases family_descends (prefixWord ++ tailWord_604739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604777 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 4]
def baseStart_604777 : Nat := 118140960795 + 604777 * 2 ^ 59
def prefixEnd_604777 : Nat := 4983230072969 + 3 ^ 40 * 604777 * 2
def baseEnd_604777 : Nat := 276036702030476036361055

theorem tailTrace_604777 : CollatzResearch.WordTrace tailWord_604777 prefixEnd_604777 276036702030476036361055 := by
  unfold tailWord_604777
  simp only [CollatzResearch.WordTrace]
  refine ⟨22058029330003691533556585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14705352886669127689037723 22058029330003691533556585)
  ·
    refine ⟨16543521997502768650167439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22058029330003691533556585 16543521997502768650167439)
    ·
      refine ⟨24815282996254152975251159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16543521997502768650167439 24815282996254152975251159)
      ·
        refine ⟨37222924494381229462876739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24815282996254152975251159 37222924494381229462876739)
        ·
          refine ⟨55834386741571844194315109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37222924494381229462876739 55834386741571844194315109)
          ·
            refine ⟨10468947514044720786434083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55834386741571844194315109 10468947514044720786434083)
            ·
              refine ⟨15703421271067081179651125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10468947514044720786434083 15703421271067081179651125)
              ·
                refine ⟨1472195744162538860592293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15703421271067081179651125 1472195744162538860592293)
                ·
                  refine ⟨276036702030476036361055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1472195744162538860592293 276036702030476036361055)
                  ·
                    rfl

theorem cell20_604777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_604777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604777 prefixEnd_604777 := by exact prefixLift 604777
  have htrace : WordTrace (prefixWord ++ tailWord_604777) baseStart_604777 baseEnd_604777 := by
    simpa [prefixWord, tailWord_604777, baseEnd_604777] using wordTrace_append hprefix tailTrace_604777
  have hstable : (prefixWord ++ tailWord_604777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604777).length < 2 ^ (prefixWord ++ tailWord_604777).sum := by decide
  have hdescent : baseEnd_604777 < baseStart_604777 := by decide
  rcases family_descends (prefixWord ++ tailWord_604777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604901 : List Nat := [1, 3, 1, 4, 1, 3, 1, 3, 3]
def baseStart_604901 : Nat := 118140960795 + 604901 * 2 ^ 59
def prefixEnd_604901 : Nat := 4983230072969 + 3 ^ 40 * 604901 * 2
def baseEnd_604901 : Nat := 276093299009282716227215

theorem tailTrace_604901 : CollatzResearch.WordTrace tailWord_604901 prefixEnd_604901 276093299009282716227215 := by
  unfold tailWord_604901
  simp only [CollatzResearch.WordTrace]
  refine ⟨22062551981554460711070557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14708367987702973807380371 22062551981554460711070557)
  ·
    refine ⟨8273456993082922766651459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22062551981554460711070557 8273456993082922766651459)
    ·
      refine ⟨12410185489624384149977189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8273456993082922766651459 12410185489624384149977189)
      ·
        refine ⟨2326909779304572028120723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12410185489624384149977189 2326909779304572028120723)
        ·
          refine ⟨3490364668956858042181085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326909779304572028120723 3490364668956858042181085)
          ·
            refine ⟨1308886750858821765817907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3490364668956858042181085 1308886750858821765817907)
            ·
              refine ⟨1963330126288232648726861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308886750858821765817907 1963330126288232648726861)
              ·
                refine ⟨736248797358087243272573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1963330126288232648726861 736248797358087243272573)
                ·
                  refine ⟨276093299009282716227215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 736248797358087243272573 276093299009282716227215)
                  ·
                    rfl

theorem cell20_604901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_604901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604901 prefixEnd_604901 := by exact prefixLift 604901
  have htrace : WordTrace (prefixWord ++ tailWord_604901) baseStart_604901 baseEnd_604901 := by
    simpa [prefixWord, tailWord_604901, baseEnd_604901] using wordTrace_append hprefix tailTrace_604901
  have hstable : (prefixWord ++ tailWord_604901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604901).length < 2 ^ (prefixWord ++ tailWord_604901).sum := by decide
  have hdescent : baseEnd_604901 < baseStart_604901 := by decide
  rcases family_descends (prefixWord ++ tailWord_604901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604936 : List Nat := [2, 1, 3, 2, 2, 10]
def baseStart_604936 : Nat := 118140960795 + 604936 * 2 ^ 59
def prefixEnd_604936 : Nat := 4983230072969 + 3 ^ 40 * 604936 * 2
def baseEnd_604936 : Nat := 10226269406036227780015

theorem tailTrace_604936 : CollatzResearch.WordTrace tailWord_604936 prefixEnd_604936 10226269406036227780015 := by
  unfold tailWord_604936
  simp only [CollatzResearch.WordTrace]
  refine ⟨11031914268213830844297331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14709219024285107792396441 11031914268213830844297331)
  ·
    refine ⟨16547871402320746266445997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11031914268213830844297331 16547871402320746266445997)
    ·
      refine ⟨6205451775870279849917249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16547871402320746266445997 6205451775870279849917249)
      ·
        refine ⟨4654088831902709887437937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6205451775870279849917249 4654088831902709887437937)
        ·
          refine ⟨3490566623927032415578453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4654088831902709887437937 3490566623927032415578453)
          ·
            refine ⟨10226269406036227780015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3490566623927032415578453 10226269406036227780015)
            ·
              rfl

theorem cell20_604936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 10].length) (baseStart_604936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_604936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_604936 prefixEnd_604936 := by exact prefixLift 604936
  have htrace : WordTrace (prefixWord ++ tailWord_604936) baseStart_604936 baseEnd_604936 := by
    simpa [prefixWord, tailWord_604936, baseEnd_604936] using wordTrace_append hprefix tailTrace_604936
  have hstable : (prefixWord ++ tailWord_604936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604936).length < 2 ^ (prefixWord ++ tailWord_604936).sum := by decide
  have hdescent : baseEnd_604936 < baseStart_604936 := by decide
  rcases family_descends (prefixWord ++ tailWord_604936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605029 : List Nat := [1, 3, 1, 3, 1, 1, 6, 4]
def baseStart_605029 : Nat := 118140960795 + 605029 * 2 ^ 59
def prefixEnd_605029 : Nat := 4983230072969 + 3 ^ 40 * 605029 * 2
def baseEnd_605029 : Nat := 92050573899027719986675

theorem tailTrace_605029 : CollatzResearch.WordTrace tailWord_605029 prefixEnd_605029 92050573899027719986675 := by
  unfold tailWord_605029
  simp only [CollatzResearch.WordTrace]
  refine ⟨22067220525090738571730141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14711480350060492381153427 22067220525090738571730141)
  ·
    refine ⟨8275207696909026964398803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22067220525090738571730141 8275207696909026964398803)
    ·
      refine ⟨12412811545363540446598205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8275207696909026964398803 12412811545363540446598205)
      ·
        refine ⟨4654804329511327667474327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12412811545363540446598205 4654804329511327667474327)
        ·
          refine ⟨6982206494266991501211491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4654804329511327667474327 6982206494266991501211491)
          ·
            refine ⟨10473309741400487251817237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6982206494266991501211491 10473309741400487251817237)
            ·
              refine ⟨490936394128147839928933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10473309741400487251817237 490936394128147839928933)
              ·
                refine ⟨92050573899027719986675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 490936394128147839928933 92050573899027719986675)
                ·
                  rfl

theorem cell20_605029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 4].length) (baseStart_605029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605029 prefixEnd_605029 := by exact prefixLift 605029
  have htrace : WordTrace (prefixWord ++ tailWord_605029) baseStart_605029 baseEnd_605029 := by
    simpa [prefixWord, tailWord_605029, baseEnd_605029] using wordTrace_append hprefix tailTrace_605029
  have hstable : (prefixWord ++ tailWord_605029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605029).length < 2 ^ (prefixWord ++ tailWord_605029).sum := by decide
  have hdescent : baseEnd_605029 < baseStart_605029 := by decide
  rcases family_descends (prefixWord ++ tailWord_605029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605046 : List Nat := [5, 1, 1, 3, 1, 3, 6]
def baseStart_605046 : Nat := 118140960795 + 605046 * 2 ^ 59
def prefixEnd_605046 : Nat := 4983230072969 + 3 ^ 40 * 605046 * 2
def baseEnd_605046 : Nat := 30684386773367406265921

theorem tailTrace_605046 : CollatzResearch.WordTrace tailWord_605046 prefixEnd_605046 30684386773367406265921 := by
  unfold tailWord_605046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1379240035376821904693687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14711893710686100316732661 1379240035376821904693687)
  ·
    refine ⟨2068860053065232857040531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1379240035376821904693687 2068860053065232857040531)
    ·
      refine ⟨3103290079597849285560797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2068860053065232857040531 3103290079597849285560797)
      ·
        refine ⟨1163733779849193482085299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3103290079597849285560797 1163733779849193482085299)
        ·
          refine ⟨1745600669773790223127949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1163733779849193482085299 1745600669773790223127949)
          ·
            refine ⟨654600251165171333672981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1745600669773790223127949 654600251165171333672981)
            ·
              refine ⟨30684386773367406265921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 654600251165171333672981 30684386773367406265921)
              ·
                rfl

theorem cell20_605046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 6].length) (baseStart_605046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605046 prefixEnd_605046 := by exact prefixLift 605046
  have htrace : WordTrace (prefixWord ++ tailWord_605046) baseStart_605046 baseEnd_605046 := by
    simpa [prefixWord, tailWord_605046, baseEnd_605046] using wordTrace_append hprefix tailTrace_605046
  have hstable : (prefixWord ++ tailWord_605046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605046).length < 2 ^ (prefixWord ++ tailWord_605046).sum := by decide
  have hdescent : baseEnd_605046 < baseStart_605046 := by decide
  rcases family_descends (prefixWord ++ tailWord_605046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605088 : List Nat := [2, 1, 1, 4, 1, 1, 4, 6]
def baseStart_605088 : Nat := 118140960795 + 605088 * 2 ^ 59
def prefixEnd_605088 : Nat := 4983230072969 + 3 ^ 40 * 605088 * 2
def baseEnd_605088 : Nat := 92059550301580392331039

theorem tailTrace_605088 : CollatzResearch.WordTrace tailWord_605088 prefixEnd_605088 92059550301580392331039 := by
  unfold tailWord_605088
  simp only [CollatzResearch.WordTrace]
  refine ⟨11034686215938495824063959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14712914954584661098751945 11034686215938495824063959)
  ·
    refine ⟨16552029323907743736095939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11034686215938495824063959 16552029323907743736095939)
    ·
      refine ⟨24828043985861615604143909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16552029323907743736095939 24828043985861615604143909)
      ·
        refine ⟨4655258247349052925776983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24828043985861615604143909 4655258247349052925776983)
        ·
          refine ⟨6982887371023579388665475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4655258247349052925776983 6982887371023579388665475)
          ·
            refine ⟨10474331056535369082998213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6982887371023579388665475 10474331056535369082998213)
            ·
              refine ⟨1963937073100381703062165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10474331056535369082998213 1963937073100381703062165)
              ·
                refine ⟨92059550301580392331039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1963937073100381703062165 92059550301580392331039)
                ·
                  rfl

theorem cell20_605088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_605088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605088 prefixEnd_605088 := by exact prefixLift 605088
  have htrace : WordTrace (prefixWord ++ tailWord_605088) baseStart_605088 baseEnd_605088 := by
    simpa [prefixWord, tailWord_605088, baseEnd_605088] using wordTrace_append hprefix tailTrace_605088
  have hstable : (prefixWord ++ tailWord_605088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605088).length < 2 ^ (prefixWord ++ tailWord_605088).sum := by decide
  have hdescent : baseEnd_605088 < baseStart_605088 := by decide
  rcases family_descends (prefixWord ++ tailWord_605088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605105 : List Nat := [1, 2, 2, 4, 4, 7]
def baseStart_605105 : Nat := 118140960795 + 605105 * 2 ^ 59
def prefixEnd_605105 : Nat := 4983230072969 + 3 ^ 40 * 605105 * 2
def baseEnd_605105 : Nat := 10229126302517210126903

theorem tailTrace_605105 : CollatzResearch.WordTrace tailWord_605105 prefixEnd_605105 10229126302517210126903 := by
  unfold tailWord_605105
  simp only [CollatzResearch.WordTrace]
  refine ⟨22069992472815403551496769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14713328315210269034331179 22069992472815403551496769)
  ·
    refine ⟨16552494354611552663622577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22069992472815403551496769 16552494354611552663622577)
    ·
      refine ⟨12414370765958664497716933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16552494354611552663622577 12414370765958664497716933)
      ·
        refine ⟨2327694518617249593321925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12414370765958664497716933 2327694518617249593321925)
        ·
          refine ⟨436442722240734298747861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2327694518617249593321925 436442722240734298747861)
          ·
            refine ⟨10229126302517210126903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 436442722240734298747861 10229126302517210126903)
            ·
              rfl

theorem cell20_605105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 7].length) (baseStart_605105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605105 prefixEnd_605105 := by exact prefixLift 605105
  have htrace : WordTrace (prefixWord ++ tailWord_605105) baseStart_605105 baseEnd_605105 := by
    simpa [prefixWord, tailWord_605105, baseEnd_605105] using wordTrace_append hprefix tailTrace_605105
  have hstable : (prefixWord ++ tailWord_605105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605105).length < 2 ^ (prefixWord ++ tailWord_605105).sum := by decide
  have hdescent : baseEnd_605105 < baseStart_605105 := by decide
  rcases family_descends (prefixWord ++ tailWord_605105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605108 : List Nat := [2, 5, 2, 1, 1, 1, 1, 4, 3]
def baseStart_605108 : Nat := 118140960795 + 605108 * 2 ^ 59
def prefixEnd_605108 : Nat := 4983230072969 + 3 ^ 40 * 605108 * 2
def baseEnd_605108 : Nat := 276187779449709996326369

theorem tailTrace_605108 : CollatzResearch.WordTrace tailWord_605108 prefixEnd_605108 276187779449709996326369 := by
  unfold tailWord_605108
  simp only [CollatzResearch.WordTrace]
  refine ⟨11035050945902267531927989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14713401261203023375903985 11035050945902267531927989)
  ·
    refine ⟨1034536026178337581118249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11035050945902267531927989 1034536026178337581118249)
    ·
      refine ⟨775902019633753185838687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1034536026178337581118249 775902019633753185838687)
      ·
        refine ⟨1163853029450629778758031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 775902019633753185838687 1163853029450629778758031)
        ·
          refine ⟨1745779544175944668137047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1163853029450629778758031 1745779544175944668137047)
          ·
            refine ⟨2618669316263917002205571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1745779544175944668137047 2618669316263917002205571)
            ·
              refine ⟨3928003974395875503308357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2618669316263917002205571 3928003974395875503308357)
              ·
                refine ⟨736500745199226656870317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3928003974395875503308357 736500745199226656870317)
                ·
                  refine ⟨276187779449709996326369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 736500745199226656870317 276187779449709996326369)
                  ·
                    rfl

theorem cell20_605108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_605108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605108 prefixEnd_605108 := by exact prefixLift 605108
  have htrace : WordTrace (prefixWord ++ tailWord_605108) baseStart_605108 baseEnd_605108 := by
    simpa [prefixWord, tailWord_605108, baseEnd_605108] using wordTrace_append hprefix tailTrace_605108
  have hstable : (prefixWord ++ tailWord_605108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605108).length < 2 ^ (prefixWord ++ tailWord_605108).sum := by decide
  have hdescent : baseEnd_605108 < baseStart_605108 := by decide
  rcases family_descends (prefixWord ++ tailWord_605108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605112 : List Nat := [2, 1, 2, 1, 2, 4, 1, 4, 3]
def baseStart_605112 : Nat := 118140960795 + 605112 * 2 ^ 59
def prefixEnd_605112 : Nat := 4983230072969 + 3 ^ 40 * 605112 * 2
def baseEnd_605112 : Nat := 276189605158703760193019

theorem tailTrace_605112 : CollatzResearch.WordTrace tailWord_605112 prefixEnd_605112 276189605158703760193019 := by
  unfold tailWord_605112
  simp only [CollatzResearch.WordTrace]
  refine ⟨11035123891895021873500795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14713498522526695831334393 11035123891895021873500795)
  ·
    refine ⟨16552685837842532810251193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11035123891895021873500795 16552685837842532810251193)
    ·
      refine ⟨12414514378381899607688395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16552685837842532810251193 12414514378381899607688395)
      ·
        refine ⟨18621771567572849411532593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12414514378381899607688395 18621771567572849411532593)
        ·
          refine ⟨13966328675679637058649445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18621771567572849411532593 13966328675679637058649445)
          ·
            refine ⟨2618686626689931948496771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13966328675679637058649445 2618686626689931948496771)
            ·
              refine ⟨3928029940034897922745157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2618686626689931948496771 3928029940034897922745157)
              ·
                refine ⟨736505613756543360514717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3928029940034897922745157 736505613756543360514717)
                ·
                  refine ⟨276189605158703760193019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 736505613756543360514717 276189605158703760193019)
                  ·
                    rfl

theorem cell20_605112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_605112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605112 prefixEnd_605112 := by exact prefixLift 605112
  have htrace : WordTrace (prefixWord ++ tailWord_605112) baseStart_605112 baseEnd_605112 := by
    simpa [prefixWord, tailWord_605112, baseEnd_605112] using wordTrace_append hprefix tailTrace_605112
  have hstable : (prefixWord ++ tailWord_605112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605112).length < 2 ^ (prefixWord ++ tailWord_605112).sum := by decide
  have hdescent : baseEnd_605112 < baseStart_605112 := by decide
  rcases family_descends (prefixWord ++ tailWord_605112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605167 : List Nat := [1, 1, 2, 1, 4, 5, 1, 2, 3]
def baseStart_605167 : Nat := 118140960795 + 605167 * 2 ^ 59
def prefixEnd_605167 : Nat := 4983230072969 + 3 ^ 40 * 605167 * 2
def baseEnd_605167 : Nat := 276214708657368013359461

theorem tailTrace_605167 : CollatzResearch.WordTrace tailWord_605167 prefixEnd_605167 276214708657368013359461 := by
  unfold tailWord_605167
  simp only [CollatzResearch.WordTrace]
  refine ⟨22072253798590788140253755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14714835865727192093502503 22072253798590788140253755)
  ·
    refine ⟨33108380697886182210380633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22072253798590788140253755 33108380697886182210380633)
    ·
      refine ⟨24831285523414636657785475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33108380697886182210380633 24831285523414636657785475)
      ·
        refine ⟨37246928285121954986678213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24831285523414636657785475 37246928285121954986678213)
        ·
          refine ⟨6983799053460366560002165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37246928285121954986678213 6983799053460366560002165)
          ·
            refine ⟨654731161261909365000203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6983799053460366560002165 654731161261909365000203)
            ·
              refine ⟨982096741892864047500305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654731161261909365000203 982096741892864047500305)
              ·
                refine ⟨736572556419648035625229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982096741892864047500305 736572556419648035625229)
                ·
                  refine ⟨276214708657368013359461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 736572556419648035625229 276214708657368013359461)
                  ·
                    rfl

theorem cell20_605167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 3].length) (baseStart_605167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605167 prefixEnd_605167 := by exact prefixLift 605167
  have htrace : WordTrace (prefixWord ++ tailWord_605167) baseStart_605167 baseEnd_605167 := by
    simpa [prefixWord, tailWord_605167, baseEnd_605167] using wordTrace_append hprefix tailTrace_605167
  have hstable : (prefixWord ++ tailWord_605167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605167).length < 2 ^ (prefixWord ++ tailWord_605167).sum := by decide
  have hdescent : baseEnd_605167 < baseStart_605167 := by decide
  rcases family_descends (prefixWord ++ tailWord_605167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605174 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_605174 : Nat := 118140960795 + 605174 * 2 ^ 59
def prefixEnd_605174 : Nat := 4983230072969 + 3 ^ 40 * 605174 * 2
def baseEnd_605174 : Nat := 276217903648107100126099

theorem tailTrace_605174 : CollatzResearch.WordTrace tailWord_605174 prefixEnd_605174 276217903648107100126099 := by
  unfold tailWord_605174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1379531819347839270984911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14715006073043618890505717 1379531819347839270984911)
  ·
    refine ⟨2069297729021758906477367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1379531819347839270984911 2069297729021758906477367)
    ·
      refine ⟨3103946593532638359716051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2069297729021758906477367 3103946593532638359716051)
      ·
        refine ⟨4655919890298957539574077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3103946593532638359716051 4655919890298957539574077)
        ·
          refine ⟨1745969958862109077340279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4655919890298957539574077 1745969958862109077340279)
          ·
            refine ⟨2618954938293163616010419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1745969958862109077340279 2618954938293163616010419)
            ·
              refine ⟨3928432407439745424015629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2618954938293163616010419 3928432407439745424015629)
              ·
                refine ⟨1473162152789904534005861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3928432407439745424015629 1473162152789904534005861)
                ·
                  refine ⟨276217903648107100126099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1473162152789904534005861 276217903648107100126099)
                  ·
                    rfl

theorem cell20_605174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_605174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605174 prefixEnd_605174 := by exact prefixLift 605174
  have htrace : WordTrace (prefixWord ++ tailWord_605174) baseStart_605174 baseEnd_605174 := by
    simpa [prefixWord, tailWord_605174, baseEnd_605174] using wordTrace_append hprefix tailTrace_605174
  have hstable : (prefixWord ++ tailWord_605174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605174).length < 2 ^ (prefixWord ++ tailWord_605174).sum := by decide
  have hdescent : baseEnd_605174 < baseStart_605174 := by decide
  rcases family_descends (prefixWord ++ tailWord_605174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605195 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 4]
def baseStart_605195 : Nat := 118140960795 + 605195 * 2 ^ 59
def prefixEnd_605195 : Nat := 4983230072969 + 3 ^ 40 * 605195 * 2
def baseEnd_605195 : Nat := 276227488620324360426013

theorem tailTrace_605195 : CollatzResearch.WordTrace tailWord_605195 prefixEnd_605195 276227488620324360426013 := by
  unfold tailWord_605195
  simp only [CollatzResearch.WordTrace]
  refine ⟨22073275042489348922273039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14715516694992899281515359 22073275042489348922273039)
  ·
    refine ⟨33109912563734023383409559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22073275042489348922273039 33109912563734023383409559)
    ·
      refine ⟨49664868845601035075114339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33109912563734023383409559 49664868845601035075114339)
      ·
        refine ⟨74497303268401552612671509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49664868845601035075114339 74497303268401552612671509)
        ·
          refine ⟨3492061090706322778718977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74497303268401552612671509 3492061090706322778718977)
          ·
            refine ⟨2619045818029742084039233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3492061090706322778718977 2619045818029742084039233)
            ·
              refine ⟨1964284363522306563029425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2619045818029742084039233 1964284363522306563029425)
              ·
                refine ⟨1473213272641729922272069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1964284363522306563029425 1473213272641729922272069)
                ·
                  refine ⟨276227488620324360426013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1473213272641729922272069 276227488620324360426013)
                  ·
                    rfl

theorem cell20_605195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_605195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605195 prefixEnd_605195 := by exact prefixLift 605195
  have htrace : WordTrace (prefixWord ++ tailWord_605195) baseStart_605195 baseEnd_605195 := by
    simpa [prefixWord, tailWord_605195, baseEnd_605195] using wordTrace_append hprefix tailTrace_605195
  have hstable : (prefixWord ++ tailWord_605195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605195).length < 2 ^ (prefixWord ++ tailWord_605195).sum := by decide
  have hdescent : baseEnd_605195 < baseStart_605195 := by decide
  rcases family_descends (prefixWord ++ tailWord_605195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605198 : List Nat := [4, 1, 1, 2, 2, 4, 2, 4]
def baseStart_605198 : Nat := 118140960795 + 605198 * 2 ^ 59
def prefixEnd_605198 : Nat := 4983230072969 + 3 ^ 40 * 605198 * 2
def baseEnd_605198 : Nat := 92076285967356561108667

theorem tailTrace_605198 : CollatzResearch.WordTrace tailWord_605198 prefixEnd_605198 92076285967356561108667 := by
  unfold tailWord_605198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2759173057684810054329031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14715589640985653623088165 2759173057684810054329031)
  ·
    refine ⟨4138759586527215081493547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2759173057684810054329031 4138759586527215081493547)
    ·
      refine ⟨6208139379790822622240321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4138759586527215081493547 6208139379790822622240321)
      ·
        refine ⟨4656104534843116966680241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6208139379790822622240321 4656104534843116966680241)
        ·
          refine ⟨3492078401132337725010181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4656104534843116966680241 3492078401132337725010181)
          ·
            refine ⟨654764700212313323439409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3492078401132337725010181 654764700212313323439409)
            ·
              refine ⟨491073525159234992579557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 654764700212313323439409 491073525159234992579557)
              ·
                refine ⟨92076285967356561108667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 491073525159234992579557 92076285967356561108667)
                ·
                  rfl

theorem cell20_605198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_605198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605198 prefixEnd_605198 := by exact prefixLift 605198
  have htrace : WordTrace (prefixWord ++ tailWord_605198) baseStart_605198 baseEnd_605198 := by
    simpa [prefixWord, tailWord_605198, baseEnd_605198] using wordTrace_append hprefix tailTrace_605198
  have hstable : (prefixWord ++ tailWord_605198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605198).length < 2 ^ (prefixWord ++ tailWord_605198).sum := by decide
  have hdescent : baseEnd_605198 < baseStart_605198 := by decide
  rcases family_descends (prefixWord ++ tailWord_605198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605209 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 5]
def baseStart_605209 : Nat := 118140960795 + 605209 * 2 ^ 59
def prefixEnd_605209 : Nat := 4983230072969 + 3 ^ 40 * 605209 * 2
def baseEnd_605209 : Nat := 276233878601802533959289

theorem tailTrace_605209 : CollatzResearch.WordTrace tailWord_605209 prefixEnd_605209 276233878601802533959289 := by
  unfold tailWord_605209
  simp only [CollatzResearch.WordTrace]
  refine ⟨22073785664438629313282681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14715857109625752875521787 22073785664438629313282681)
  ·
    refine ⟨16555339248328971984962011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22073785664438629313282681 16555339248328971984962011)
    ·
      refine ⟨24833008872493457977443017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16555339248328971984962011 24833008872493457977443017)
      ·
        refine ⟨18624756654370093483082263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24833008872493457977443017 18624756654370093483082263)
        ·
          refine ⟨27937134981555140224623395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18624756654370093483082263 27937134981555140224623395)
          ·
            refine ⟨41905702472332710336935093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27937134981555140224623395 41905702472332710336935093)
            ·
              refine ⟨3928659606781191594087665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41905702472332710336935093 3928659606781191594087665)
              ·
                refine ⟨2946494705085893695565749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3928659606781191594087665 2946494705085893695565749)
                ·
                  refine ⟨276233878601802533959289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2946494705085893695565749 276233878601802533959289)
                  ·
                    rfl

theorem cell20_605209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_605209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605209 prefixEnd_605209 := by exact prefixLift 605209
  have htrace : WordTrace (prefixWord ++ tailWord_605209) baseStart_605209 baseEnd_605209 := by
    simpa [prefixWord, tailWord_605209, baseEnd_605209] using wordTrace_append hprefix tailTrace_605209
  have hstable : (prefixWord ++ tailWord_605209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605209).length < 2 ^ (prefixWord ++ tailWord_605209).sum := by decide
  have hdescent : baseEnd_605209 < baseStart_605209 := by decide
  rcases family_descends (prefixWord ++ tailWord_605209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605236 : List Nat := [2, 5, 1, 2, 1, 2, 2, 5]
def baseStart_605236 : Nat := 118140960795 + 605236 * 2 ^ 59
def prefixEnd_605236 : Nat := 4983230072969 + 3 ^ 40 * 605236 * 2
def baseEnd_605236 : Nat := 92082067379170146686393

theorem tailTrace_605236 : CollatzResearch.WordTrace tailWord_605236 prefixEnd_605236 92082067379170146686393 := by
  unfold tailWord_605236
  simp only [CollatzResearch.WordTrace]
  refine ⟨11037385217670406462257781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14716513623560541949677041 11037385217670406462257781)
  ·
    refine ⟨1034754864156600605836667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11037385217670406462257781 1034754864156600605836667)
    ·
      refine ⟨1552132296234900908755001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1034754864156600605836667 1552132296234900908755001)
      ·
        refine ⟨1164099222176175681566251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1552132296234900908755001 1164099222176175681566251)
        ·
          refine ⟨1746148833264263522349377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164099222176175681566251 1746148833264263522349377)
          ·
            refine ⟨1309611624948197641762033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1746148833264263522349377 1309611624948197641762033)
            ·
              refine ⟨982208718711148231321525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1309611624948197641762033 982208718711148231321525)
              ·
                refine ⟨92082067379170146686393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 982208718711148231321525 92082067379170146686393)
                ·
                  rfl

theorem cell20_605236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_605236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605236 prefixEnd_605236 := by exact prefixLift 605236
  have htrace : WordTrace (prefixWord ++ tailWord_605236) baseStart_605236 baseEnd_605236 := by
    simpa [prefixWord, tailWord_605236, baseEnd_605236] using wordTrace_append hprefix tailTrace_605236
  have hstable : (prefixWord ++ tailWord_605236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605236).length < 2 ^ (prefixWord ++ tailWord_605236).sum := by decide
  have hdescent : baseEnd_605236 < baseStart_605236 := by decide
  rcases family_descends (prefixWord ++ tailWord_605236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605240 : List Nat := [2, 1, 2, 1, 5, 1, 1, 7]
def baseStart_605240 : Nat := 118140960795 + 605240 * 2 ^ 59
def prefixEnd_605240 : Nat := 4983230072969 + 3 ^ 40 * 605240 * 2
def baseEnd_605240 : Nat := 92082675948834734641943

theorem tailTrace_605240 : CollatzResearch.WordTrace tailWord_605240 prefixEnd_605240 92082675948834734641943 := by
  unfold tailWord_605240
  simp only [CollatzResearch.WordTrace]
  refine ⟨11037458163663160803830587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14716610884884214405107449 11037458163663160803830587)
  ·
    refine ⟨16556187245494741205745881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11037458163663160803830587 16556187245494741205745881)
    ·
      refine ⟨12417140434121055904309411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16556187245494741205745881 12417140434121055904309411)
      ·
        refine ⟨18625710651181583856464117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12417140434121055904309411 18625710651181583856464117)
        ·
          refine ⟨1746160373548273486543511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18625710651181583856464117 1746160373548273486543511)
          ·
            refine ⟨2619240560322410229815267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746160373548273486543511 2619240560322410229815267)
            ·
              refine ⟨3928860840483615344722901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2619240560322410229815267 3928860840483615344722901)
              ·
                refine ⟨92082675948834734641943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3928860840483615344722901 92082675948834734641943)
                ·
                  rfl

theorem cell20_605240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_605240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605240 prefixEnd_605240 := by exact prefixLift 605240
  have htrace : WordTrace (prefixWord ++ tailWord_605240) baseStart_605240 baseEnd_605240 := by
    simpa [prefixWord, tailWord_605240, baseEnd_605240] using wordTrace_append hprefix tailTrace_605240
  have hstable : (prefixWord ++ tailWord_605240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605240).length < 2 ^ (prefixWord ++ tailWord_605240).sum := by decide
  have hdescent : baseEnd_605240 < baseStart_605240 := by decide
  rcases family_descends (prefixWord ++ tailWord_605240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605309 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 4]
def baseStart_605309 : Nat := 118140960795 + 605309 * 2 ^ 59
def prefixEnd_605309 : Nat := 4983230072969 + 3 ^ 40 * 605309 * 2
def baseEnd_605309 : Nat := 276279521326646630625547

theorem tailTrace_605309 : CollatzResearch.WordTrace tailWord_605309 prefixEnd_605309 276279521326646630625547 := by
  unfold tailWord_605309
  simp only [CollatzResearch.WordTrace]
  refine ⟨22077432964076346391922981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14718288642717564261281987 22077432964076346391922981)
  ·
    refine ⟨4139518680764314948485559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22077432964076346391922981 4139518680764314948485559)
    ·
      refine ⟨6209278021146472422728339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4139518680764314948485559 6209278021146472422728339)
      ·
        refine ⟨9313917031719708634092509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6209278021146472422728339 9313917031719708634092509)
        ·
          refine ⟨3492718886894890737784691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9313917031719708634092509 3492718886894890737784691)
          ·
            refine ⟨5239078330342336106677037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3492718886894890737784691 5239078330342336106677037)
            ·
              refine ⟨1964654373878376040003889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5239078330342336106677037 1964654373878376040003889)
              ·
                refine ⟨1473490780408782030002917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1964654373878376040003889 1473490780408782030002917)
                ·
                  refine ⟨276279521326646630625547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1473490780408782030002917 276279521326646630625547)
                  ·
                    rfl

theorem cell20_605309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_605309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605309 prefixEnd_605309 := by exact prefixLift 605309
  have htrace : WordTrace (prefixWord ++ tailWord_605309) baseStart_605309 baseEnd_605309 := by
    simpa [prefixWord, tailWord_605309, baseEnd_605309] using wordTrace_append hprefix tailTrace_605309
  have hstable : (prefixWord ++ tailWord_605309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605309).length < 2 ^ (prefixWord ++ tailWord_605309).sum := by decide
  have hdescent : baseEnd_605309 < baseStart_605309 := by decide
  rcases family_descends (prefixWord ++ tailWord_605309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605340 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 5]
def baseStart_605340 : Nat := 118140960795 + 605340 * 2 ^ 59
def prefixEnd_605340 : Nat := 4983230072969 + 3 ^ 40 * 605340 * 2
def baseEnd_605340 : Nat := 276293670571348300592087

theorem tailTrace_605340 : CollatzResearch.WordTrace tailWord_605340 prefixEnd_605340 276293670571348300592087 := by
  unfold tailWord_605340
  simp only [CollatzResearch.WordTrace]
  refine ⟨11039281813482019343150737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14719042417976025790867649 11039281813482019343150737)
  ·
    refine ⟨8279461360111514507363053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11039281813482019343150737 8279461360111514507363053)
    ·
      refine ⟨3104798010041817940261145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8279461360111514507363053 3104798010041817940261145)
      ·
        refine ⟨2328598507531363455195859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3104798010041817940261145 2328598507531363455195859)
        ·
          refine ⟨3492897761297045182793789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2328598507531363455195859 3492897761297045182793789)
          ·
            refine ⟨1309836660486391943547671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3492897761297045182793789 1309836660486391943547671)
            ·
              refine ⟨1964754990729587915321507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1309836660486391943547671 1964754990729587915321507)
              ·
                refine ⟨2947132486094381872982261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1964754990729587915321507 2947132486094381872982261)
                ·
                  refine ⟨276293670571348300592087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2947132486094381872982261 276293670571348300592087)
                  ·
                    rfl

theorem cell20_605340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_605340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605340 prefixEnd_605340 := by exact prefixLift 605340
  have htrace : WordTrace (prefixWord ++ tailWord_605340) baseStart_605340 baseEnd_605340 := by
    simpa [prefixWord, tailWord_605340, baseEnd_605340] using wordTrace_append hprefix tailTrace_605340
  have hstable : (prefixWord ++ tailWord_605340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605340).length < 2 ^ (prefixWord ++ tailWord_605340).sum := by decide
  have hdescent : baseEnd_605340 < baseStart_605340 := by decide
  rcases family_descends (prefixWord ++ tailWord_605340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605368 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_605368 : Nat := 118140960795 + 605368 * 2 ^ 59
def prefixEnd_605368 : Nat := 4983230072969 + 3 ^ 40 * 605368 * 2
def baseEnd_605368 : Nat := 276306450534304647658639

theorem tailTrace_605368 : CollatzResearch.WordTrace tailWord_605368 prefixEnd_605368 276306450534304647658639 := by
  unfold tailWord_605368
  simp only [CollatzResearch.WordTrace]
  refine ⟨11039792435431299734160379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14719723247241732978880505 11039792435431299734160379)
  ·
    refine ⟨16559688653146949601240569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11039792435431299734160379 16559688653146949601240569)
    ·
      refine ⟨12419766489860212200930427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16559688653146949601240569 12419766489860212200930427)
      ·
        refine ⟨18629649734790318301395641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12419766489860212200930427 18629649734790318301395641)
        ·
          refine ⟨13972237301092738726046731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18629649734790318301395641 13972237301092738726046731)
          ·
            refine ⟨20958355951639108089070097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13972237301092738726046731 20958355951639108089070097)
            ·
              refine ⟨15718766963729331066802573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20958355951639108089070097 15718766963729331066802573)
              ·
                refine ⟨5894537611398499150050965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15718766963729331066802573 5894537611398499150050965)
                ·
                  refine ⟨276306450534304647658639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5894537611398499150050965 276306450534304647658639)
                  ·
                    rfl

theorem cell20_605368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_605368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605368 prefixEnd_605368 := by exact prefixLift 605368
  have htrace : WordTrace (prefixWord ++ tailWord_605368) baseStart_605368 baseEnd_605368 := by
    simpa [prefixWord, tailWord_605368, baseEnd_605368] using wordTrace_append hprefix tailTrace_605368
  have hstable : (prefixWord ++ tailWord_605368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605368).length < 2 ^ (prefixWord ++ tailWord_605368).sum := by decide
  have hdescent : baseEnd_605368 < baseStart_605368 := by decide
  rcases family_descends (prefixWord ++ tailWord_605368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605398 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_605398 : Nat := 118140960795 + 605398 * 2 ^ 59
def prefixEnd_605398 : Nat := 4983230072969 + 3 ^ 40 * 605398 * 2
def baseEnd_605398 : Nat := 276320143351757876658517

theorem tailTrace_605398 : CollatzResearch.WordTrace tailWord_605398 prefixEnd_605398 276320143351757876658517 := by
  unfold tailWord_605398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380042441297119661994553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14720452707169276394608565 1380042441297119661994553)
  ·
    refine ⟨1035031830972839746495915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1380042441297119661994553 1035031830972839746495915)
    ·
      refine ⟨1552547746459259619743873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1035031830972839746495915 1552547746459259619743873)
      ·
        refine ⟨1164410809844444714807905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1552547746459259619743873 1164410809844444714807905)
        ·
          refine ⟨873308107383333536105929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1164410809844444714807905 873308107383333536105929)
          ·
            refine ⟨654981080537500152079447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 873308107383333536105929 654981080537500152079447)
            ·
              refine ⟨982471620806250228119171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654981080537500152079447 982471620806250228119171)
              ·
                refine ⟨1473707431209375342178757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982471620806250228119171 1473707431209375342178757)
                ·
                  refine ⟨276320143351757876658517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1473707431209375342178757 276320143351757876658517)
                  ·
                    rfl

theorem cell20_605398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_605398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605398 prefixEnd_605398 := by exact prefixLift 605398
  have htrace : WordTrace (prefixWord ++ tailWord_605398) baseStart_605398 baseEnd_605398 := by
    simpa [prefixWord, tailWord_605398, baseEnd_605398] using wordTrace_append hprefix tailTrace_605398
  have hstable : (prefixWord ++ tailWord_605398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605398).length < 2 ^ (prefixWord ++ tailWord_605398).sum := by decide
  have hdescent : baseEnd_605398 < baseStart_605398 := by decide
  rcases family_descends (prefixWord ++ tailWord_605398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605399 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 5]
def baseStart_605399 : Nat := 118140960795 + 605399 * 2 ^ 59
def prefixEnd_605399 : Nat := 4983230072969 + 3 ^ 40 * 605399 * 2
def baseEnd_605399 : Nat := 276320599779006317625179

theorem tailTrace_605399 : CollatzResearch.WordTrace tailWord_605399 prefixEnd_605399 276320599779006317625179 := by
  unfold tailWord_605399
  simp only [CollatzResearch.WordTrace]
  refine ⟨22080715533750291762699251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14720477022500194508466167 22080715533750291762699251)
  ·
    refine ⟨33121073300625437644048877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22080715533750291762699251 33121073300625437644048877)
    ·
      refine ⟨12420402487734539116518329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33121073300625437644048877 12420402487734539116518329)
      ·
        refine ⟨9315301865800904337388747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12420402487734539116518329 9315301865800904337388747)
        ·
          refine ⟨13972952798701356506083121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9315301865800904337388747 13972952798701356506083121)
          ·
            refine ⟨10479714599026017379562341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13972952798701356506083121 10479714599026017379562341)
            ·
              refine ⟨1964946487317378258667939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10479714599026017379562341 1964946487317378258667939)
              ·
                refine ⟨2947419730976067388001909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1964946487317378258667939 2947419730976067388001909)
                ·
                  refine ⟨276320599779006317625179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2947419730976067388001909 276320599779006317625179)
                  ·
                    rfl

theorem cell20_605399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_605399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605399 prefixEnd_605399 := by exact prefixLift 605399
  have htrace : WordTrace (prefixWord ++ tailWord_605399) baseStart_605399 baseEnd_605399 := by
    simpa [prefixWord, tailWord_605399, baseEnd_605399] using wordTrace_append hprefix tailTrace_605399
  have hstable : (prefixWord ++ tailWord_605399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605399).length < 2 ^ (prefixWord ++ tailWord_605399).sum := by decide
  have hdescent : baseEnd_605399 < baseStart_605399 := by decide
  rcases family_descends (prefixWord ++ tailWord_605399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605416 : List Nat := [2, 1, 4, 1, 2, 1, 3, 3, 3]
def baseStart_605416 : Nat := 118140960795 + 605416 * 2 ^ 59
def prefixEnd_605416 : Nat := 4983230072969 + 3 ^ 40 * 605416 * 2
def baseEnd_605416 : Nat := 276328359042229814058443

theorem tailTrace_605416 : CollatzResearch.WordTrace tailWord_605416 prefixEnd_605416 276328359042229814058443 := by
  unfold tailWord_605416
  simp only [CollatzResearch.WordTrace]
  refine ⟨11040667787344351833034051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14720890383125802444045401 11040667787344351833034051)
  ·
    refine ⟨16561001681016527749551077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11040667787344351833034051 16561001681016527749551077)
    ·
      refine ⟨3105187815190598953040827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16561001681016527749551077 3105187815190598953040827)
      ·
        refine ⟨4657781722785898429561241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3105187815190598953040827 4657781722785898429561241)
        ·
          refine ⟨3493336292089423822170931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4657781722785898429561241 3493336292089423822170931)
          ·
            refine ⟨5240004438134135733256397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3493336292089423822170931 5240004438134135733256397)
            ·
              refine ⟨1965001664300300899971149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5240004438134135733256397 1965001664300300899971149)
              ·
                refine ⟨736875624112612837489181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1965001664300300899971149 736875624112612837489181)
                ·
                  refine ⟨276328359042229814058443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 736875624112612837489181 276328359042229814058443)
                  ·
                    rfl

theorem cell20_605416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_605416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605416 prefixEnd_605416 := by exact prefixLift 605416
  have htrace : WordTrace (prefixWord ++ tailWord_605416) baseStart_605416 baseEnd_605416 := by
    simpa [prefixWord, tailWord_605416, baseEnd_605416] using wordTrace_append hprefix tailTrace_605416
  have hstable : (prefixWord ++ tailWord_605416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605416).length < 2 ^ (prefixWord ++ tailWord_605416).sum := by decide
  have hdescent : baseEnd_605416 < baseStart_605416 := by decide
  rcases family_descends (prefixWord ++ tailWord_605416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605451 : List Nat := [1, 1, 1, 1, 5, 11]
def baseStart_605451 : Nat := 118140960795 + 605451 * 2 ^ 59
def prefixEnd_605451 : Nat := 4983230072969 + 3 ^ 40 * 605451 * 2
def baseEnd_605451 : Nat := 10234975333182416588579

theorem tailTrace_605451 : CollatzResearch.WordTrace tailWord_605451 prefixEnd_605451 10234975333182416588579 := by
  unfold tailWord_605451
  simp only [CollatzResearch.WordTrace]
  refine ⟨22082612129561904643592207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14721741419707936429061471 22082612129561904643592207)
  ·
    refine ⟨33123918194342856965388311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22082612129561904643592207 33123918194342856965388311)
    ·
      refine ⟨49685877291514285448082467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33123918194342856965388311 49685877291514285448082467)
      ·
        refine ⟨74528815937271428172123701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49685877291514285448082467 74528815937271428172123701)
        ·
          refine ⟨6987076494119196391136597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74528815937271428172123701 6987076494119196391136597)
          ·
            refine ⟨10234975333182416588579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6987076494119196391136597 10234975333182416588579)
            ·
              rfl

theorem cell20_605451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 11].length) (baseStart_605451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605451 prefixEnd_605451 := by exact prefixLift 605451
  have htrace : WordTrace (prefixWord ++ tailWord_605451) baseStart_605451 baseEnd_605451 := by
    simpa [prefixWord, tailWord_605451, baseEnd_605451] using wordTrace_append hprefix tailTrace_605451
  have hstable : (prefixWord ++ tailWord_605451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605451).length < 2 ^ (prefixWord ++ tailWord_605451).sum := by decide
  have hdescent : baseEnd_605451 < baseStart_605451 := by decide
  rcases family_descends (prefixWord ++ tailWord_605451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605454 : List Nat := [4, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_605454 : Nat := 118140960795 + 605454 * 2 ^ 59
def prefixEnd_605454 : Nat := 4983230072969 + 3 ^ 40 * 605454 * 2
def baseEnd_605454 : Nat := 276345703277670570791621

theorem tailTrace_605454 : CollatzResearch.WordTrace tailWord_605454 prefixEnd_605454 276345703277670570791621 := by
  unfold tailWord_605454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2760340193568879519493927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14721814365700690770634277 2760340193568879519493927)
  ·
    refine ⟨4140510290353319279240891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2760340193568879519493927 4140510290353319279240891)
    ·
      refine ⟨6210765435529978918861337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4140510290353319279240891 6210765435529978918861337)
      ·
        refine ⟨4658074076647484189146003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6210765435529978918861337 4658074076647484189146003)
        ·
          refine ⟨6987111114971226283719005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4658074076647484189146003 6987111114971226283719005)
          ·
            refine ⟨2620166668114209856394627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6987111114971226283719005 2620166668114209856394627)
            ·
              refine ⟨3930250002171314784591941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620166668114209856394627 3930250002171314784591941)
              ·
                refine ⟨736921875407121522110989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3930250002171314784591941 736921875407121522110989)
                ·
                  refine ⟨276345703277670570791621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 736921875407121522110989 276345703277670570791621)
                  ·
                    rfl

theorem cell20_605454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_605454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605454 prefixEnd_605454 := by exact prefixLift 605454
  have htrace : WordTrace (prefixWord ++ tailWord_605454) baseStart_605454 baseEnd_605454 := by
    simpa [prefixWord, tailWord_605454, baseEnd_605454] using wordTrace_append hprefix tailTrace_605454
  have hstable : (prefixWord ++ tailWord_605454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605454).length < 2 ^ (prefixWord ++ tailWord_605454).sum := by decide
  have hdescent : baseEnd_605454 < baseStart_605454 := by decide
  rcases family_descends (prefixWord ++ tailWord_605454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605468 : List Nat := [2, 2, 3, 1, 1, 1, 5, 5]
def baseStart_605468 : Nat := 118140960795 + 605468 * 2 ^ 59
def prefixEnd_605468 : Nat := 4983230072969 + 3 ^ 40 * 605468 * 2
def baseEnd_605468 : Nat := 92117364419716248108299

theorem tailTrace_605468 : CollatzResearch.WordTrace tailWord_605468 prefixEnd_605468 92117364419716248108299 := by
  unfold tailWord_605468
  simp only [CollatzResearch.WordTrace]
  refine ⟨11041616085250158273480529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14722154780333544364640705 11041616085250158273480529)
  ·
    refine ⟨8281212063937618705110397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11041616085250158273480529 8281212063937618705110397)
    ·
      refine ⟨3105454523976607014416399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8281212063937618705110397 3105454523976607014416399)
      ·
        refine ⟨4658181785964910521624599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3105454523976607014416399 4658181785964910521624599)
        ·
          refine ⟨6987272678947365782436899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4658181785964910521624599 6987272678947365782436899)
          ·
            refine ⟨10480909018421048673655349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6987272678947365782436899 10480909018421048673655349)
            ·
              refine ⟨982585220476973313155189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10480909018421048673655349 982585220476973313155189)
              ·
                refine ⟨92117364419716248108299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 982585220476973313155189 92117364419716248108299)
                ·
                  rfl

theorem cell20_605468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_605468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605468 prefixEnd_605468 := by exact prefixLift 605468
  have htrace : WordTrace (prefixWord ++ tailWord_605468) baseStart_605468 baseEnd_605468 := by
    simpa [prefixWord, tailWord_605468, baseEnd_605468] using wordTrace_append hprefix tailTrace_605468
  have hstable : (prefixWord ++ tailWord_605468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605468).length < 2 ^ (prefixWord ++ tailWord_605468).sum := by decide
  have hdescent : baseEnd_605468 < baseStart_605468 := by decide
  rcases family_descends (prefixWord ++ tailWord_605468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605492 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 5]
def baseStart_605492 : Nat := 118140960795 + 605492 * 2 ^ 59
def prefixEnd_605492 : Nat := 4983230072969 + 3 ^ 40 * 605492 * 2
def baseEnd_605492 : Nat := 276363047513111327524799

theorem tailTrace_605492 : CollatzResearch.WordTrace tailWord_605492 prefixEnd_605492 276363047513111327524799 := by
  unfold tailWord_605492
  simp only [CollatzResearch.WordTrace]
  refine ⟨11042053761206684322917365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14722738348275579097223153 11042053761206684322917365)
  ·
    refine ⟨1035192540113126655273503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11042053761206684322917365 1035192540113126655273503)
    ·
      refine ⟨1552788810169689982910255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1035192540113126655273503 1552788810169689982910255)
      ·
        refine ⟨2329183215254534974365383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1552788810169689982910255 2329183215254534974365383)
        ·
          refine ⟨3493774822881802461548075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2329183215254534974365383 3493774822881802461548075)
          ·
            refine ⟨5240662234322703692322113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3493774822881802461548075 5240662234322703692322113)
            ·
              refine ⟨3930496675742027769241585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5240662234322703692322113 3930496675742027769241585)
              ·
                refine ⟨2947872506806520826931189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3930496675742027769241585 2947872506806520826931189)
                ·
                  refine ⟨276363047513111327524799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2947872506806520826931189 276363047513111327524799)
                  ·
                    rfl

theorem cell20_605492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_605492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605492 prefixEnd_605492 := by exact prefixLift 605492
  have htrace : WordTrace (prefixWord ++ tailWord_605492) baseStart_605492 baseEnd_605492 := by
    simpa [prefixWord, tailWord_605492, baseEnd_605492] using wordTrace_append hprefix tailTrace_605492
  have hstable : (prefixWord ++ tailWord_605492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605492).length < 2 ^ (prefixWord ++ tailWord_605492).sum := by decide
  have hdescent : baseEnd_605492 < baseStart_605492 := by decide
  rcases family_descends (prefixWord ++ tailWord_605492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605516 : List Nat := [2, 2, 1, 3, 2, 2, 2, 4, 2]
def baseStart_605516 : Nat := 118140960795 + 605516 * 2 ^ 59
def prefixEnd_605516 : Nat := 4983230072969 + 3 ^ 40 * 605516 * 2
def baseEnd_605516 : Nat := 276374001767073910724701

theorem tailTrace_605516 : CollatzResearch.WordTrace tailWord_605516 prefixEnd_605516 276374001767073910724701 := by
  unfold tailWord_605516
  simp only [CollatzResearch.WordTrace]
  refine ⟨11042491437163210372354201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14723321916217613829805601 11042491437163210372354201)
  ·
    refine ⟨8281868577872407779265651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11042491437163210372354201 8281868577872407779265651)
    ·
      refine ⟨12422802866808611668898477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8281868577872407779265651 12422802866808611668898477)
      ·
        refine ⟨4658551075053229375836929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12422802866808611668898477 4658551075053229375836929)
        ·
          refine ⟨3493913306289922031877697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4658551075053229375836929 3493913306289922031877697)
          ·
            refine ⟨2620434979717441523908273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3493913306289922031877697 2620434979717441523908273)
            ·
              refine ⟨1965326234788081142931205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2620434979717441523908273 1965326234788081142931205)
              ·
                refine ⟨368498669022765214299601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1965326234788081142931205 368498669022765214299601)
                ·
                  refine ⟨276374001767073910724701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368498669022765214299601 276374001767073910724701)
                  ·
                    rfl

theorem cell20_605516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_605516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605516 prefixEnd_605516 := by exact prefixLift 605516
  have htrace : WordTrace (prefixWord ++ tailWord_605516) baseStart_605516 baseEnd_605516 := by
    simpa [prefixWord, tailWord_605516, baseEnd_605516] using wordTrace_append hprefix tailTrace_605516
  have hstable : (prefixWord ++ tailWord_605516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605516).length < 2 ^ (prefixWord ++ tailWord_605516).sum := by decide
  have hdescent : baseEnd_605516 < baseStart_605516 := by decide
  rcases family_descends (prefixWord ++ tailWord_605516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605571 : List Nat := [1, 1, 1, 3, 5, 2, 3, 2, 2]
def baseStart_605571 : Nat := 118140960795 + 605571 * 2 ^ 59
def prefixEnd_605571 : Nat := 4983230072969 + 3 ^ 40 * 605571 * 2
def baseEnd_605571 : Nat := 276399105265738163891143

theorem tailTrace_605571 : CollatzResearch.WordTrace tailWord_605571 prefixEnd_605571 276399105265738163891143 := by
  unfold tailWord_605571
  simp only [CollatzResearch.WordTrace]
  refine ⟨22086988889127165137960567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14724659259418110091973711 22086988889127165137960567)
  ·
    refine ⟨33130483333690747706940851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22086988889127165137960567 33130483333690747706940851)
    ·
      refine ⟨49695725000536121560411277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33130483333690747706940851 49695725000536121560411277)
      ·
        refine ⟨18635896875201045585154229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49695725000536121560411277 18635896875201045585154229)
        ·
          refine ⟨1747115332050098023608209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18635896875201045585154229 1747115332050098023608209)
          ·
            refine ⟨1310336499037573517706157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1747115332050098023608209 1310336499037573517706157)
            ·
              refine ⟨491376187139090069139809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1310336499037573517706157 491376187139090069139809)
              ·
                refine ⟨368532140354317551854857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491376187139090069139809 368532140354317551854857)
                ·
                  refine ⟨276399105265738163891143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368532140354317551854857 276399105265738163891143)
                  ·
                    rfl

theorem cell20_605571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 2].length) (baseStart_605571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605571 prefixEnd_605571 := by exact prefixLift 605571
  have htrace : WordTrace (prefixWord ++ tailWord_605571) baseStart_605571 baseEnd_605571 := by
    simpa [prefixWord, tailWord_605571, baseEnd_605571] using wordTrace_append hprefix tailTrace_605571
  have hstable : (prefixWord ++ tailWord_605571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605571).length < 2 ^ (prefixWord ++ tailWord_605571).sum := by decide
  have hdescent : baseEnd_605571 < baseStart_605571 := by decide
  rcases family_descends (prefixWord ++ tailWord_605571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605575 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 4]
def baseStart_605575 : Nat := 118140960795 + 605575 * 2 ^ 59
def prefixEnd_605575 : Nat := 4983230072969 + 3 ^ 40 * 605575 * 2
def baseEnd_605575 : Nat := 276400930974731927757793

theorem tailTrace_605575 : CollatzResearch.WordTrace tailWord_605575 prefixEnd_605575 276400930974731927757793 := by
  unfold tailWord_605575
  simp only [CollatzResearch.WordTrace]
  refine ⟨22087134781112673821106179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14724756520741782547404119 22087134781112673821106179)
  ·
    refine ⟨33130702171669010731659269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22087134781112673821106179 33130702171669010731659269)
    ·
      refine ⟨6212006657187939512186113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33130702171669010731659269 6212006657187939512186113)
      ·
        refine ⟨4659004992890954634139585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6212006657187939512186113 4659004992890954634139585)
        ·
          refine ⟨3494253744668215975604689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4659004992890954634139585 3494253744668215975604689)
          ·
            refine ⟨2620690308501161981703517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3494253744668215975604689 2620690308501161981703517)
            ·
              refine ⟨982758865687935743138819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2620690308501161981703517 982758865687935743138819)
              ·
                refine ⟨1474138298531903614708229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982758865687935743138819 1474138298531903614708229)
                ·
                  refine ⟨276400930974731927757793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1474138298531903614708229 276400930974731927757793)
                  ·
                    rfl

theorem cell20_605575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_605575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605575 prefixEnd_605575 := by exact prefixLift 605575
  have htrace : WordTrace (prefixWord ++ tailWord_605575) baseStart_605575 baseEnd_605575 := by
    simpa [prefixWord, tailWord_605575, baseEnd_605575] using wordTrace_append hprefix tailTrace_605575
  have hstable : (prefixWord ++ tailWord_605575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605575).length < 2 ^ (prefixWord ++ tailWord_605575).sum := by decide
  have hdescent : baseEnd_605575 < baseStart_605575 := by decide
  rcases family_descends (prefixWord ++ tailWord_605575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605603 : List Nat := [1, 1, 1, 4, 1, 3, 1, 8]
def baseStart_605603 : Nat := 118140960795 + 605603 * 2 ^ 59
def prefixEnd_605603 : Nat := 4983230072969 + 3 ^ 40 * 605603 * 2
def baseEnd_605603 : Nat := 92137903645896091608115

theorem tailTrace_605603 : CollatzResearch.WordTrace tailWord_605603 prefixEnd_605603 92137903645896091608115 := by
  unfold tailWord_605603
  simp only [CollatzResearch.WordTrace]
  refine ⟨22088156025011234603125463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14725437350007489735416975 22088156025011234603125463)
  ·
    refine ⟨33132234037516851904688195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22088156025011234603125463 33132234037516851904688195)
    ·
      refine ⟨49698351056275277857032293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33132234037516851904688195 49698351056275277857032293)
      ·
        refine ⟨9318440823051614598193555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49698351056275277857032293 9318440823051614598193555)
        ·
          refine ⟨13977661234577421897290333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9318440823051614598193555 13977661234577421897290333)
          ·
            refine ⟨5241622962966533211483875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13977661234577421897290333 5241622962966533211483875)
            ·
              refine ⟨7862434444449799817225813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5241622962966533211483875 7862434444449799817225813)
              ·
                refine ⟨92137903645896091608115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7862434444449799817225813 92137903645896091608115)
                ·
                  rfl

theorem cell20_605603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_605603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605603 prefixEnd_605603 := by exact prefixLift 605603
  have htrace : WordTrace (prefixWord ++ tailWord_605603) baseStart_605603 baseEnd_605603 := by
    simpa [prefixWord, tailWord_605603, baseEnd_605603] using wordTrace_append hprefix tailTrace_605603
  have hstable : (prefixWord ++ tailWord_605603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605603).length < 2 ^ (prefixWord ++ tailWord_605603).sum := by decide
  have hdescent : baseEnd_605603 < baseStart_605603 := by decide
  rcases family_descends (prefixWord ++ tailWord_605603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605620 : List Nat := [2, 5, 2, 11]
def baseStart_605620 : Nat := 118140960795 + 605620 * 2 ^ 59
def prefixEnd_605620 : Nat := 4983230072969 + 3 ^ 40 * 605620 * 2
def baseEnd_605620 : Nat := 1137536914407044326163

theorem tailTrace_605620 : CollatzResearch.WordTrace tailWord_605620 prefixEnd_605620 1137536914407044326163 := by
  unfold tailWord_605620
  simp only [CollatzResearch.WordTrace]
  refine ⟨11044388032974823253247157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14725850710633097670996209 11044388032974823253247157)
  ·
    refine ⟨1035411378091389679991921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11044388032974823253247157 1035411378091389679991921)
    ·
      refine ⟨776558533568542259993941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1035411378091389679991921 776558533568542259993941)
      ·
        refine ⟨1137536914407044326163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 776558533568542259993941 1137536914407044326163)
        ·
          rfl

theorem cell20_605620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 11].length) (baseStart_605620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605620 prefixEnd_605620 := by exact prefixLift 605620
  have htrace : WordTrace (prefixWord ++ tailWord_605620) baseStart_605620 baseEnd_605620 := by
    simpa [prefixWord, tailWord_605620, baseEnd_605620] using wordTrace_append hprefix tailTrace_605620
  have hstable : (prefixWord ++ tailWord_605620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605620).length < 2 ^ (prefixWord ++ tailWord_605620).sum := by decide
  have hdescent : baseEnd_605620 < baseStart_605620 := by decide
  rcases family_descends (prefixWord ++ tailWord_605620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605644 : List Nat := [2, 2, 1, 4, 2, 1, 2, 3, 3]
def baseStart_605644 : Nat := 118140960795 + 605644 * 2 ^ 59
def prefixEnd_605644 : Nat := 4983230072969 + 3 ^ 40 * 605644 * 2
def baseEnd_605644 : Nat := 276432424454874354457511

theorem tailTrace_605644 : CollatzResearch.WordTrace tailWord_605644 prefixEnd_605644 276432424454874354457511 := by
  unfold tailWord_605644
  simp only [CollatzResearch.WordTrace]
  refine ⟨11044825708931349302683993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14726434278575132403578657 11044825708931349302683993)
  ·
    refine ⟨8283619281698511977012995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11044825708931349302683993 8283619281698511977012995)
    ·
      refine ⟨12425428922547767965519493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8283619281698511977012995 12425428922547767965519493)
      ·
        refine ⟨2329767922977706493534905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12425428922547767965519493 2329767922977706493534905)
        ·
          refine ⟨1747325942233279870151179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2329767922977706493534905 1747325942233279870151179)
          ·
            refine ⟨2620988913349919805226769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1747325942233279870151179 2620988913349919805226769)
            ·
              refine ⟨1965741685012439853920077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2620988913349919805226769 1965741685012439853920077)
              ·
                refine ⟨737153131879664945220029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1965741685012439853920077 737153131879664945220029)
                ·
                  refine ⟨276432424454874354457511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737153131879664945220029 276432424454874354457511)
                  ·
                    rfl

theorem cell20_605644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_605644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605644 prefixEnd_605644 := by exact prefixLift 605644
  have htrace : WordTrace (prefixWord ++ tailWord_605644) baseStart_605644 baseEnd_605644 := by
    simpa [prefixWord, tailWord_605644, baseEnd_605644] using wordTrace_append hprefix tailTrace_605644
  have hstable : (prefixWord ++ tailWord_605644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605644).length < 2 ^ (prefixWord ++ tailWord_605644).sum := by decide
  have hdescent : baseEnd_605644 < baseStart_605644 := by decide
  rcases family_descends (prefixWord ++ tailWord_605644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605654 : List Nat := [5, 2, 1, 1, 1, 3, 3, 4]
def baseStart_605654 : Nat := 118140960795 + 605654 * 2 ^ 59
def prefixEnd_605654 : Nat := 4983230072969 + 3 ^ 40 * 605654 * 2
def baseEnd_605654 : Nat := 92145662909119588041379

theorem tailTrace_605654 : CollatzResearch.WordTrace tailWord_605654 prefixEnd_605654 92145662909119588041379 := by
  unfold tailWord_605654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380626009239154394577001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14726677431884313542154677 1380626009239154394577001)
  ·
    refine ⟨1035469506929365795932751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1380626009239154394577001 1035469506929365795932751)
    ·
      refine ⟨1553204260394048693899127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1035469506929365795932751 1553204260394048693899127)
      ·
        refine ⟨2329806390591073040848691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1553204260394048693899127 2329806390591073040848691)
        ·
          refine ⟨3494709585886609561273037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2329806390591073040848691 3494709585886609561273037)
          ·
            refine ⟨1310516094707478585477389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3494709585886609561273037 1310516094707478585477389)
            ·
              refine ⟨491443535515304469554021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1310516094707478585477389 491443535515304469554021)
              ·
                refine ⟨92145662909119588041379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 491443535515304469554021 92145662909119588041379)
                ·
                  rfl

theorem cell20_605654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_605654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605654 prefixEnd_605654 := by exact prefixLift 605654
  have htrace : WordTrace (prefixWord ++ tailWord_605654) baseStart_605654 baseEnd_605654 := by
    simpa [prefixWord, tailWord_605654, baseEnd_605654] using wordTrace_append hprefix tailTrace_605654
  have hstable : (prefixWord ++ tailWord_605654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605654).length < 2 ^ (prefixWord ++ tailWord_605654).sum := by decide
  have hdescent : baseEnd_605654 < baseStart_605654 := by decide
  rcases family_descends (prefixWord ++ tailWord_605654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605672 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_605672 : Nat := 118140960795 + 605672 * 2 ^ 59
def prefixEnd_605672 : Nat := 4983230072969 + 3 ^ 40 * 605672 * 2
def baseEnd_605672 : Nat := 276445204417830701524063

theorem tailTrace_605672 : CollatzResearch.WordTrace tailWord_605672 prefixEnd_605672 276445204417830701524063 := by
  unfold tailWord_605672
  simp only [CollatzResearch.WordTrace]
  refine ⟨11045336330880629693693635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14727115107840839591591513 11045336330880629693693635)
  ·
    refine ⟨16568004496320944540540453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11045336330880629693693635 16568004496320944540540453)
    ·
      refine ⟨3106500843060177101351335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16568004496320944540540453 3106500843060177101351335)
      ·
        refine ⟨4659751264590265652027003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3106500843060177101351335 4659751264590265652027003)
        ·
          refine ⟨6989626896885398478040505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4659751264590265652027003 6989626896885398478040505)
          ·
            refine ⟨5242220172664048858530379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6989626896885398478040505 5242220172664048858530379)
            ·
              refine ⟨7863330258996073287795569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5242220172664048858530379 7863330258996073287795569)
              ·
                refine ⟨5897497694247054965846677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7863330258996073287795569 5897497694247054965846677)
                ·
                  refine ⟨276445204417830701524063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5897497694247054965846677 276445204417830701524063)
                  ·
                    rfl

theorem cell20_605672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_605672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605672 prefixEnd_605672 := by exact prefixLift 605672
  have htrace : WordTrace (prefixWord ++ tailWord_605672) baseStart_605672 baseEnd_605672 := by
    simpa [prefixWord, tailWord_605672, baseEnd_605672] using wordTrace_append hprefix tailTrace_605672
  have hstable : (prefixWord ++ tailWord_605672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605672).length < 2 ^ (prefixWord ++ tailWord_605672).sum := by decide
  have hdescent : baseEnd_605672 < baseStart_605672 := by decide
  rcases family_descends (prefixWord ++ tailWord_605672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605682 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_605682 : Nat := 118140960795 + 605682 * 2 ^ 59
def prefixEnd_605682 : Nat := 4983230072969 + 3 ^ 40 * 605682 * 2
def baseEnd_605682 : Nat := 276449768690315111190689

theorem tailTrace_605682 : CollatzResearch.WordTrace tailWord_605682 prefixEnd_605682 276449768690315111190689 := by
  unfold tailWord_605682
  simp only [CollatzResearch.WordTrace]
  refine ⟨5522759347931257773812825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14727358261150020730167533 5522759347931257773812825)
  ·
    refine ⟨4142069510948443330359619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5522759347931257773812825 4142069510948443330359619)
    ·
      refine ⟨6213104266422664995539429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4142069510948443330359619 6213104266422664995539429)
      ·
        refine ⟨1164957049954249686663643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6213104266422664995539429 1164957049954249686663643)
        ·
          refine ⟨1747435574931374529995465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164957049954249686663643 1747435574931374529995465)
          ·
            refine ⟨1310576681198530897496599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1747435574931374529995465 1310576681198530897496599)
            ·
              refine ⟨1965865021797796346244899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310576681198530897496599 1965865021797796346244899)
              ·
                refine ⟨2948797532696694519367349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1965865021797796346244899 2948797532696694519367349)
                ·
                  refine ⟨276449768690315111190689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2948797532696694519367349 276449768690315111190689)
                  ·
                    rfl

theorem cell20_605682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_605682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605682 prefixEnd_605682 := by exact prefixLift 605682
  have htrace : WordTrace (prefixWord ++ tailWord_605682) baseStart_605682 baseEnd_605682 := by
    simpa [prefixWord, tailWord_605682, baseEnd_605682] using wordTrace_append hprefix tailTrace_605682
  have hstable : (prefixWord ++ tailWord_605682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605682).length < 2 ^ (prefixWord ++ tailWord_605682).sum := by decide
  have hdescent : baseEnd_605682 < baseStart_605682 := by decide
  rcases family_descends (prefixWord ++ tailWord_605682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605685 : List Nat := [1, 3, 5, 1, 1, 1, 2, 4, 2]
def baseStart_605685 : Nat := 118140960795 + 605685 * 2 ^ 59
def prefixEnd_605685 : Nat := 4983230072969 + 3 ^ 40 * 605685 * 2
def baseEnd_605685 : Nat := 276451137972060434090677

theorem tailTrace_605685 : CollatzResearch.WordTrace tailWord_605685 prefixEnd_605685 276451137972060434090677 := by
  unfold tailWord_605685
  simp only [CollatzResearch.WordTrace]
  refine ⟨22091146810714162607610509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14727431207142775071740339 22091146810714162607610509)
  ·
    refine ⟨8284180054017810977853941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22091146810714162607610509 8284180054017810977853941)
    ·
      refine ⟨776641880064169779173807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8284180054017810977853941 776641880064169779173807)
      ·
        refine ⟨1164962820096254668760711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776641880064169779173807 1164962820096254668760711)
        ·
          refine ⟨1747444230144382003141067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164962820096254668760711 1747444230144382003141067)
          ·
            refine ⟨2621166345216573004711601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1747444230144382003141067 2621166345216573004711601)
            ·
              refine ⟨1965874758912429753533701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2621166345216573004711601 1965874758912429753533701)
              ·
                refine ⟨368601517296080578787569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1965874758912429753533701 368601517296080578787569)
                ·
                  refine ⟨276451137972060434090677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368601517296080578787569 276451137972060434090677)
                  ·
                    rfl

theorem cell20_605685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_605685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605685 prefixEnd_605685 := by exact prefixLift 605685
  have htrace : WordTrace (prefixWord ++ tailWord_605685) baseStart_605685 baseEnd_605685 := by
    simpa [prefixWord, tailWord_605685, baseEnd_605685] using wordTrace_append hprefix tailTrace_605685
  have hstable : (prefixWord ++ tailWord_605685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605685).length < 2 ^ (prefixWord ++ tailWord_605685).sum := by decide
  have hdescent : baseEnd_605685 < baseStart_605685 := by decide
  rcases family_descends (prefixWord ++ tailWord_605685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605726 : List Nat := [4, 3, 3, 1, 2, 1, 6]
def baseStart_605726 : Nat := 118140960795 + 605726 * 2 ^ 59
def prefixEnd_605726 : Nat := 4983230072969 + 3 ^ 40 * 605726 * 2
def baseEnd_605726 : Nat := 30718872387694057080427

theorem tailTrace_605726 : CollatzResearch.WordTrace tailWord_605726 prefixEnd_605726 30718872387694057080427 := by
  unfold tailWord_605726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2761580275445703326231629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14728428135710417739902021 2761580275445703326231629)
  ·
    refine ⟨1035592603292138747336861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2761580275445703326231629 1035592603292138747336861)
    ·
      refine ⟨388347226234552030251323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1035592603292138747336861 388347226234552030251323)
      ·
        refine ⟨582520839351828045376985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388347226234552030251323 582520839351828045376985)
        ·
          refine ⟨436890629513871034032739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582520839351828045376985 436890629513871034032739)
          ·
            refine ⟨655335944270806551049109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436890629513871034032739 655335944270806551049109)
            ·
              refine ⟨30718872387694057080427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 655335944270806551049109 30718872387694057080427)
              ·
                rfl

theorem cell20_605726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 6].length) (baseStart_605726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605726 prefixEnd_605726 := by exact prefixLift 605726
  have htrace : WordTrace (prefixWord ++ tailWord_605726) baseStart_605726 baseEnd_605726 := by
    simpa [prefixWord, tailWord_605726, baseEnd_605726] using wordTrace_append hprefix tailTrace_605726
  have hstable : (prefixWord ++ tailWord_605726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605726).length < 2 ^ (prefixWord ++ tailWord_605726).sum := by decide
  have hdescent : baseEnd_605726 < baseStart_605726 := by decide
  rcases family_descends (prefixWord ++ tailWord_605726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605789 : List Nat := [1, 4, 4, 2, 1, 8]
def baseStart_605789 : Nat := 118140960795 + 605789 * 2 ^ 59
def prefixEnd_605789 : Nat := 4983230072969 + 3 ^ 40 * 605789 * 2
def baseEnd_605789 : Nat := 10240689126144381282355

theorem tailTrace_605789 : CollatzResearch.WordTrace tailWord_605789 prefixEnd_605789 10240689126144381282355 := by
  unfold tailWord_605789
  simp only [CollatzResearch.WordTrace]
  refine ⟨22094940002337388369396421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14729960001558258912930947 22094940002337388369396421)
  ·
    refine ⟨4142801250438260319261829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22094940002337388369396421 4142801250438260319261829)
    ·
      refine ⟨776775234457173809861593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4142801250438260319261829 776775234457173809861593)
      ·
        refine ⟨582581425842880357396195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 776775234457173809861593 582581425842880357396195)
        ·
          refine ⟨873872138764320536094293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582581425842880357396195 873872138764320536094293)
          ·
            refine ⟨10240689126144381282355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 873872138764320536094293 10240689126144381282355)
            ·
              rfl

theorem cell20_605789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 8].length) (baseStart_605789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605789 prefixEnd_605789 := by exact prefixLift 605789
  have htrace : WordTrace (prefixWord ++ tailWord_605789) baseStart_605789 baseEnd_605789 := by
    simpa [prefixWord, tailWord_605789, baseEnd_605789] using wordTrace_append hprefix tailTrace_605789
  have hstable : (prefixWord ++ tailWord_605789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605789).length < 2 ^ (prefixWord ++ tailWord_605789).sum := by decide
  have hdescent : baseEnd_605789 < baseStart_605789 := by decide
  rcases family_descends (prefixWord ++ tailWord_605789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605796 : List Nat := [2, 3, 1, 1, 2, 4, 2, 2, 3]
def baseStart_605796 : Nat := 118140960795 + 605796 * 2 ^ 59
def prefixEnd_605796 : Nat := 4983230072969 + 3 ^ 40 * 605796 * 2
def baseEnd_605796 : Nat := 276501801396637381390223

theorem tailTrace_605796 : CollatzResearch.WordTrace tailWord_605796 prefixEnd_605796 276501801396637381390223 := by
  unfold tailWord_605796
  simp only [CollatzResearch.WordTrace]
  refine ⟨11047597656656014282450621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14730130208874685709934161 11047597656656014282450621)
  ·
    refine ⟨4142849121246005355918983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11047597656656014282450621 4142849121246005355918983)
    ·
      refine ⟨6214273681869008033878475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4142849121246005355918983 6214273681869008033878475)
      ·
        refine ⟨9321410522803512050817713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6214273681869008033878475 9321410522803512050817713)
        ·
          refine ⟨6991057892102634038113285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9321410522803512050817713 6991057892102634038113285)
          ·
            refine ⟨1310823354769243882146241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6991057892102634038113285 1310823354769243882146241)
            ·
              refine ⟨983117516076932911609681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1310823354769243882146241 983117516076932911609681)
              ·
                refine ⟨737338137057699683707261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983117516076932911609681 737338137057699683707261)
                ·
                  refine ⟨276501801396637381390223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737338137057699683707261 276501801396637381390223)
                  ·
                    rfl

theorem cell20_605796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_605796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605796 prefixEnd_605796 := by exact prefixLift 605796
  have htrace : WordTrace (prefixWord ++ tailWord_605796) baseStart_605796 baseEnd_605796 := by
    simpa [prefixWord, tailWord_605796, baseEnd_605796] using wordTrace_append hprefix tailTrace_605796
  have hstable : (prefixWord ++ tailWord_605796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605796).length < 2 ^ (prefixWord ++ tailWord_605796).sum := by decide
  have hdescent : baseEnd_605796 < baseStart_605796 := by decide
  rcases family_descends (prefixWord ++ tailWord_605796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605806 : List Nat := [4, 1, 2, 2, 4, 1, 1, 5]
def baseStart_605806 : Nat := 118140960795 + 605806 * 2 ^ 59
def prefixEnd_605806 : Nat := 4983230072969 + 3 ^ 40 * 605806 * 2
def baseEnd_605806 : Nat := 92168788556373930352283

theorem tailTrace_605806 : CollatzResearch.WordTrace tailWord_605806 prefixEnd_605806 92168788556373930352283 := by
  unfold tailWord_605806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2761945005409475034095659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14730373362183866848510181 2761945005409475034095659)
  ·
    refine ⟨4142917508114212551143489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2761945005409475034095659 4142917508114212551143489)
    ·
      refine ⟨3107188131085659413357617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4142917508114212551143489 3107188131085659413357617)
      ·
        refine ⟨2330391098314244560018213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3107188131085659413357617 2330391098314244560018213)
        ·
          refine ⟨436948330933920855003415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2330391098314244560018213 436948330933920855003415)
          ·
            refine ⟨655422496400881282505123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436948330933920855003415 655422496400881282505123)
            ·
              refine ⟨983133744601321923757685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655422496400881282505123 983133744601321923757685)
              ·
                refine ⟨92168788556373930352283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 983133744601321923757685 92168788556373930352283)
                ·
                  rfl

theorem cell20_605806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_605806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605806 prefixEnd_605806 := by exact prefixLift 605806
  have htrace : WordTrace (prefixWord ++ tailWord_605806) baseStart_605806 baseEnd_605806 := by
    simpa [prefixWord, tailWord_605806, baseEnd_605806] using wordTrace_append hprefix tailTrace_605806
  have hstable : (prefixWord ++ tailWord_605806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605806).length < 2 ^ (prefixWord ++ tailWord_605806).sum := by decide
  have hdescent : baseEnd_605806 < baseStart_605806 := by decide
  rcases family_descends (prefixWord ++ tailWord_605806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605810 : List Nat := [3, 2, 1, 2, 3, 1, 3, 5]
def baseStart_605810 : Nat := 118140960795 + 605810 * 2 ^ 59
def prefixEnd_605810 : Nat := 4983230072969 + 3 ^ 40 * 605810 * 2
def baseEnd_605810 : Nat := 92169397126038518307833

theorem tailTrace_605810 : CollatzResearch.WordTrace tailWord_605810 prefixEnd_605810 92169397126038518307833 := by
  unfold tailWord_605810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5523926483815327238977721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14730470623507539303940589 5523926483815327238977721)
  ·
    refine ⟨4142944862861495429233291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5523926483815327238977721 4142944862861495429233291)
    ·
      refine ⟨6214417294292243143849937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4142944862861495429233291 6214417294292243143849937)
      ·
        refine ⟨4660812970719182357887453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6214417294292243143849937 4660812970719182357887453)
        ·
          refine ⟨1747804864019693384207795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4660812970719182357887453 1747804864019693384207795)
          ·
            refine ⟨2621707296029540076311693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1747804864019693384207795 2621707296029540076311693)
            ·
              refine ⟨983140236011077528616885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2621707296029540076311693 983140236011077528616885)
              ·
                refine ⟨92169397126038518307833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 983140236011077528616885 92169397126038518307833)
                ·
                  rfl

theorem cell20_605810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_605810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605810 prefixEnd_605810 := by exact prefixLift 605810
  have htrace : WordTrace (prefixWord ++ tailWord_605810) baseStart_605810 baseEnd_605810 := by
    simpa [prefixWord, tailWord_605810, baseEnd_605810] using wordTrace_append hprefix tailTrace_605810
  have hstable : (prefixWord ++ tailWord_605810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605810).length < 2 ^ (prefixWord ++ tailWord_605810).sum := by decide
  have hdescent : baseEnd_605810 < baseStart_605810 := by decide
  rcases family_descends (prefixWord ++ tailWord_605810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605817 : List Nat := [1, 2, 1, 3, 3, 1, 1, 5, 3]
def baseStart_605817 : Nat := 118140960795 + 605817 * 2 ^ 59
def prefixEnd_605817 : Nat := 4983230072969 + 3 ^ 40 * 605817 * 2
def baseEnd_605817 : Nat := 276511386368854641690137

theorem tailTrace_605817 : CollatzResearch.WordTrace tailWord_605817 prefixEnd_605817 276511386368854641690137 := by
  unfold tailWord_605817
  simp only [CollatzResearch.WordTrace]
  refine ⟨22095961246235949151415705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14730640830823966100943803 22095961246235949151415705)
  ·
    refine ⟨16571970934676961863561779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22095961246235949151415705 16571970934676961863561779)
    ·
      refine ⟨24857956402015442795342669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16571970934676961863561779 24857956402015442795342669)
      ·
        refine ⟨9321733650755791048253501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24857956402015442795342669 9321733650755791048253501)
        ·
          refine ⟨3495650119033421643095063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9321733650755791048253501 3495650119033421643095063)
          ·
            refine ⟨5243475178550132464642595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3495650119033421643095063 5243475178550132464642595)
            ·
              refine ⟨7865212767825198696963893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5243475178550132464642595 7865212767825198696963893)
              ·
                refine ⟨737363696983612377840365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7865212767825198696963893 737363696983612377840365)
                ·
                  refine ⟨276511386368854641690137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737363696983612377840365 276511386368854641690137)
                  ·
                    rfl

theorem cell20_605817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_605817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605817 prefixEnd_605817 := by exact prefixLift 605817
  have htrace : WordTrace (prefixWord ++ tailWord_605817) baseStart_605817 baseEnd_605817 := by
    simpa [prefixWord, tailWord_605817, baseEnd_605817] using wordTrace_append hprefix tailTrace_605817
  have hstable : (prefixWord ++ tailWord_605817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605817).length < 2 ^ (prefixWord ++ tailWord_605817).sum := by decide
  have hdescent : baseEnd_605817 < baseStart_605817 := by decide
  rcases family_descends (prefixWord ++ tailWord_605817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605824 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_605824 : Nat := 118140960795 + 605824 * 2 ^ 59
def prefixEnd_605824 : Nat := 4983230072969 + 3 ^ 40 * 605824 * 2
def baseEnd_605824 : Nat := 276514581359593728456775

theorem tailTrace_605824 : CollatzResearch.WordTrace tailWord_605824 prefixEnd_605824 276514581359593728456775 := by
  unfold tailWord_605824
  simp only [CollatzResearch.WordTrace]
  refine ⟨11048108278605294673460263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14730811038140392897947017 11048108278605294673460263)
  ·
    refine ⟨16572162417907942010190395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11048108278605294673460263 16572162417907942010190395)
    ·
      refine ⟨24858243626861913015285593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16572162417907942010190395 24858243626861913015285593)
      ·
        refine ⟨18643682720146434761464195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24858243626861913015285593 18643682720146434761464195)
        ·
          refine ⟨27965524080219652142196293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18643682720146434761464195 27965524080219652142196293)
          ·
            refine ⟨5243535765041184776661805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27965524080219652142196293 5243535765041184776661805)
            ·
              refine ⟨1966325911890444291248177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5243535765041184776661805 1966325911890444291248177)
              ·
                refine ⟨1474744433917833218436133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1966325911890444291248177 1474744433917833218436133)
                ·
                  refine ⟨276514581359593728456775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1474744433917833218436133 276514581359593728456775)
                  ·
                    rfl

theorem cell20_605824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_605824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605824 prefixEnd_605824 := by exact prefixLift 605824
  have htrace : WordTrace (prefixWord ++ tailWord_605824) baseStart_605824 baseEnd_605824 := by
    simpa [prefixWord, tailWord_605824, baseEnd_605824] using wordTrace_append hprefix tailTrace_605824
  have hstable : (prefixWord ++ tailWord_605824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605824).length < 2 ^ (prefixWord ++ tailWord_605824).sum := by decide
  have hdescent : baseEnd_605824 < baseStart_605824 := by decide
  rcases family_descends (prefixWord ++ tailWord_605824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605886 : List Nat := [4, 2, 1, 1, 2, 3, 1, 6]
def baseStart_605886 : Nat := 118140960795 + 605886 * 2 ^ 59
def prefixEnd_605886 : Nat := 4983230072969 + 3 ^ 40 * 605886 * 2
def baseEnd_605886 : Nat := 92180959949665689463285

theorem tailTrace_605886 : CollatzResearch.WordTrace tailWord_605886 prefixEnd_605886 92180959949665689463285 := by
  unfold tailWord_605886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2762309735373246741959689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14732318588657315957118341 2762309735373246741959689)
  ·
    refine ⟨2071732301529935056469767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2762309735373246741959689 2071732301529935056469767)
    ·
      refine ⟨3107598452294902584704651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2071732301529935056469767 3107598452294902584704651)
      ·
        refine ⟨4661397678442353877056977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3107598452294902584704651 4661397678442353877056977)
        ·
          refine ⟨3496048258831765407792733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4661397678442353877056977 3496048258831765407792733)
          ·
            refine ⟨1311018097061912027922275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3496048258831765407792733 1311018097061912027922275)
            ·
              refine ⟨1966527145592868041883413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1311018097061912027922275 1966527145592868041883413)
              ·
                refine ⟨92180959949665689463285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1966527145592868041883413 92180959949665689463285)
                ·
                  rfl

theorem cell20_605886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_605886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605886 prefixEnd_605886 := by exact prefixLift 605886
  have htrace : WordTrace (prefixWord ++ tailWord_605886) baseStart_605886 baseEnd_605886 := by
    simpa [prefixWord, tailWord_605886, baseEnd_605886] using wordTrace_append hprefix tailTrace_605886
  have hstable : (prefixWord ++ tailWord_605886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605886).length < 2 ^ (prefixWord ++ tailWord_605886).sum := by decide
  have hdescent : baseEnd_605886 < baseStart_605886 := by decide
  rcases family_descends (prefixWord ++ tailWord_605886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605927 : List Nat := [1, 1, 5, 4, 1, 1, 1, 3, 3]
def baseStart_605927 : Nat := 118140960795 + 605927 * 2 ^ 59
def prefixEnd_605927 : Nat := 4983230072969 + 3 ^ 40 * 605927 * 2
def baseEnd_605927 : Nat := 276561593366183148023021

theorem tailTrace_605927 : CollatzResearch.WordTrace tailWord_605927 prefixEnd_605927 276561593366183148023021 := by
  unfold tailWord_605927
  simp only [CollatzResearch.WordTrace]
  refine ⟨22099973275837437937920035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14733315517224958625280023 22099973275837437937920035)
  ·
    refine ⟨33149959913756156906880053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22099973275837437937920035 33149959913756156906880053)
    ·
      refine ⟨3107808741914639710020005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33149959913756156906880053 3107808741914639710020005)
      ·
        refine ⟨582714139108994945628751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3107808741914639710020005 582714139108994945628751)
        ·
          refine ⟨874071208663492418443127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582714139108994945628751 874071208663492418443127)
          ·
            refine ⟨1311106812995238627664691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874071208663492418443127 1311106812995238627664691)
            ·
              refine ⟨1966660219492857941497037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1311106812995238627664691 1966660219492857941497037)
              ·
                refine ⟨737497582309821728061389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1966660219492857941497037 737497582309821728061389)
                ·
                  refine ⟨276561593366183148023021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737497582309821728061389 276561593366183148023021)
                  ·
                    rfl

theorem cell20_605927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 3].length) (baseStart_605927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605927 prefixEnd_605927 := by exact prefixLift 605927
  have htrace : WordTrace (prefixWord ++ tailWord_605927) baseStart_605927 baseEnd_605927 := by
    simpa [prefixWord, tailWord_605927, baseEnd_605927] using wordTrace_append hprefix tailTrace_605927
  have hstable : (prefixWord ++ tailWord_605927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605927).length < 2 ^ (prefixWord ++ tailWord_605927).sum := by decide
  have hdescent : baseEnd_605927 < baseStart_605927 := by decide
  rcases family_descends (prefixWord ++ tailWord_605927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605938 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_605938 : Nat := 118140960795 + 605938 * 2 ^ 59
def prefixEnd_605938 : Nat := 4983230072969 + 3 ^ 40 * 605938 * 2
def baseEnd_605938 : Nat := 276566614065915998656309

theorem tailTrace_605938 : CollatzResearch.WordTrace tailWord_605938 prefixEnd_605938 276566614065915998656309 := by
  unfold tailWord_605938
  simp only [CollatzResearch.WordTrace]
  refine ⟨5525093619699396704142617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14733582985865057877713645 5525093619699396704142617)
  ·
    refine ⟨4143820214774547528106963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5525093619699396704142617 4143820214774547528106963)
    ·
      refine ⟨6215730322161821292160445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4143820214774547528106963 6215730322161821292160445)
      ·
        refine ⟨2330898870810682984560167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6215730322161821292160445 2330898870810682984560167)
        ·
          refine ⟨3496348306216024476840251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2330898870810682984560167 3496348306216024476840251)
          ·
            refine ⟨5244522459324036715260377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3496348306216024476840251 5244522459324036715260377)
            ·
              refine ⟨3933391844493027536445283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5244522459324036715260377 3933391844493027536445283)
              ·
                refine ⟨5900087766739541304667925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3933391844493027536445283 5900087766739541304667925)
                ·
                  refine ⟨276566614065915998656309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5900087766739541304667925 276566614065915998656309)
                  ·
                    rfl

theorem cell20_605938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_605938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_605938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_605938 prefixEnd_605938 := by exact prefixLift 605938
  have htrace : WordTrace (prefixWord ++ tailWord_605938) baseStart_605938 baseEnd_605938 := by
    simpa [prefixWord, tailWord_605938, baseEnd_605938] using wordTrace_append hprefix tailTrace_605938
  have hstable : (prefixWord ++ tailWord_605938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605938).length < 2 ^ (prefixWord ++ tailWord_605938).sum := by decide
  have hdescent : baseEnd_605938 < baseStart_605938 := by decide
  rcases family_descends (prefixWord ++ tailWord_605938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606010 : List Nat := [3, 1, 1, 1, 5, 2, 2, 3, 2]
def baseStart_606010 : Nat := 118140960795 + 606010 * 2 ^ 59
def prefixEnd_606010 : Nat := 4983230072969 + 3 ^ 40 * 606010 * 2
def baseEnd_606010 : Nat := 276599476827803748256015

theorem tailTrace_606010 : CollatzResearch.WordTrace tailWord_606010 prefixEnd_606010 276599476827803748256015 := by
  unfold tailWord_606010
  simp only [CollatzResearch.WordTrace]
  refine ⟨5525750133634185778297871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14735333689691162075460989 5525750133634185778297871)
  ·
    refine ⟨8288625200451278667446807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5525750133634185778297871 8288625200451278667446807)
    ·
      refine ⟨12432937800676918001170211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8288625200451278667446807 12432937800676918001170211)
      ·
        refine ⟨18649406701015377001755317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12432937800676918001170211 18649406701015377001755317)
        ·
          refine ⟨1748381878220191593914561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18649406701015377001755317 1748381878220191593914561)
          ·
            refine ⟨1311286408665143695435921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1748381878220191593914561 1311286408665143695435921)
            ·
              refine ⟨983464806498857771576941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1311286408665143695435921 983464806498857771576941)
              ·
                refine ⟨368799302437071664341353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 983464806498857771576941 368799302437071664341353)
                ·
                  refine ⟨276599476827803748256015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368799302437071664341353 276599476827803748256015)
                  ·
                    rfl

theorem cell20_606010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_606010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606010 prefixEnd_606010 := by exact prefixLift 606010
  have htrace : WordTrace (prefixWord ++ tailWord_606010) baseStart_606010 baseEnd_606010 := by
    simpa [prefixWord, tailWord_606010, baseEnd_606010] using wordTrace_append hprefix tailTrace_606010
  have hstable : (prefixWord ++ tailWord_606010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606010).length < 2 ^ (prefixWord ++ tailWord_606010).sum := by decide
  have hdescent : baseEnd_606010 < baseStart_606010 := by decide
  rcases family_descends (prefixWord ++ tailWord_606010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606024 : List Nat := [2, 1, 3, 1, 1, 6, 1, 2, 3]
def baseStart_606024 : Nat := 118140960795 + 606024 * 2 ^ 59
def prefixEnd_606024 : Nat := 4983230072969 + 3 ^ 40 * 606024 * 2
def baseEnd_606024 : Nat := 276605866809281921789291

theorem tailTrace_606024 : CollatzResearch.WordTrace tailWord_606024 prefixEnd_606024 276605866809281921789291 := by
  unfold tailWord_606024
  simp only [CollatzResearch.WordTrace]
  refine ⟨11051755578243011752100563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14735674104324015669467417 11051755578243011752100563)
  ·
    refine ⟨16577633367364517628150845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11051755578243011752100563 16577633367364517628150845)
    ·
      refine ⟨6216612512761694110556567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16577633367364517628150845 6216612512761694110556567)
      ·
        refine ⟨9324918769142541165834851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6216612512761694110556567 9324918769142541165834851)
        ·
          refine ⟨13987378153713811748752277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9324918769142541165834851 13987378153713811748752277)
          ·
            refine ⟨655658350955334925722763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13987378153713811748752277 655658350955334925722763)
            ·
              refine ⟨983487526433002388584145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655658350955334925722763 983487526433002388584145)
              ·
                refine ⟨737615644824751791438109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983487526433002388584145 737615644824751791438109)
                ·
                  refine ⟨276605866809281921789291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737615644824751791438109 276605866809281921789291)
                  ·
                    rfl

theorem cell20_606024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_606024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606024 prefixEnd_606024 := by exact prefixLift 606024
  have htrace : WordTrace (prefixWord ++ tailWord_606024) baseStart_606024 baseEnd_606024 := by
    simpa [prefixWord, tailWord_606024, baseEnd_606024] using wordTrace_append hprefix tailTrace_606024
  have hstable : (prefixWord ++ tailWord_606024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606024).length < 2 ^ (prefixWord ++ tailWord_606024).sum := by decide
  have hdescent : baseEnd_606024 < baseStart_606024 := by decide
  rcases family_descends (prefixWord ++ tailWord_606024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606100 : List Nat := [2, 4, 2, 1, 1, 3, 1, 3, 3]
def baseStart_606100 : Nat := 118140960795 + 606100 * 2 ^ 59
def prefixEnd_606100 : Nat := 4983230072969 + 3 ^ 40 * 606100 * 2
def baseEnd_606100 : Nat := 276640555280163435255647

theorem tailTrace_606100 : CollatzResearch.WordTrace tailWord_606100 prefixEnd_606100 276640555280163435255647 := by
  unfold tailWord_606100
  simp only [CollatzResearch.WordTrace]
  refine ⟨11053141552105344241983877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14737522069473792322645169 11053141552105344241983877)
  ·
    refine ⟨2072464041019752045371977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11053141552105344241983877 2072464041019752045371977)
    ·
      refine ⟨1554348030764814034028983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2072464041019752045371977 1554348030764814034028983)
      ·
        refine ⟨2331522046147221051043475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1554348030764814034028983 2331522046147221051043475)
        ·
          refine ⟨3497283069220831576565213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2331522046147221051043475 3497283069220831576565213)
          ·
            refine ⟨1311481150957811841211955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3497283069220831576565213 1311481150957811841211955)
            ·
              refine ⟨1967221726436717761817933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1311481150957811841211955 1967221726436717761817933)
              ·
                refine ⟨737708147413769160681725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1967221726436717761817933 737708147413769160681725)
                ·
                  refine ⟨276640555280163435255647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737708147413769160681725 276640555280163435255647)
                  ·
                    rfl

theorem cell20_606100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_606100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606100 prefixEnd_606100 := by exact prefixLift 606100
  have htrace : WordTrace (prefixWord ++ tailWord_606100) baseStart_606100 baseEnd_606100 := by
    simpa [prefixWord, tailWord_606100, baseEnd_606100] using wordTrace_append hprefix tailTrace_606100
  have hstable : (prefixWord ++ tailWord_606100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606100).length < 2 ^ (prefixWord ++ tailWord_606100).sum := by decide
  have hdescent : baseEnd_606100 < baseStart_606100 := by decide
  rcases family_descends (prefixWord ++ tailWord_606100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606141 : List Nat := [1, 4, 1, 2, 3, 3, 2, 2, 2]
def baseStart_606141 : Nat := 118140960795 + 606141 * 2 ^ 59
def prefixEnd_606141 : Nat := 4983230072969 + 3 ^ 40 * 606141 * 2
def baseEnd_606141 : Nat := 276659268797349514888813

theorem tailTrace_606141 : CollatzResearch.WordTrace tailWord_606141 prefixEnd_606141 276659268797349514888813 := by
  unfold tailWord_606141
  simp only [CollatzResearch.WordTrace]
  refine ⟨22107778497062152486210277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14738518998041434990806851 22107778497062152486210277)
  ·
    refine ⟨4145208468199153591164427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22107778497062152486210277 4145208468199153591164427)
    ·
      refine ⟨6217812702298730386746641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4145208468199153591164427 6217812702298730386746641)
      ·
        refine ⟨4663359526724047790059981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6217812702298730386746641 4663359526724047790059981)
        ·
          refine ⟨1748759822521517921272493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4663359526724047790059981 1748759822521517921272493)
          ·
            refine ⟨655784933445569220477185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1748759822521517921272493 655784933445569220477185)
            ·
              refine ⟨491838700084176915357889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655784933445569220477185 491838700084176915357889)
              ·
                refine ⟨368879025063132686518417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491838700084176915357889 368879025063132686518417)
                ·
                  refine ⟨276659268797349514888813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368879025063132686518417 276659268797349514888813)
                  ·
                    rfl

theorem cell20_606141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_606141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606141 prefixEnd_606141 := by exact prefixLift 606141
  have htrace : WordTrace (prefixWord ++ tailWord_606141) baseStart_606141 baseEnd_606141 := by
    simpa [prefixWord, tailWord_606141, baseEnd_606141] using wordTrace_append hprefix tailTrace_606141
  have hstable : (prefixWord ++ tailWord_606141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606141).length < 2 ^ (prefixWord ++ tailWord_606141).sum := by decide
  have hdescent : baseEnd_606141 < baseStart_606141 := by decide
  rcases family_descends (prefixWord ++ tailWord_606141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606152 : List Nat := [2, 1, 3, 1, 4, 3, 1, 5]
def baseStart_606152 : Nat := 118140960795 + 606152 * 2 ^ 59
def prefixEnd_606152 : Nat := 4983230072969 + 3 ^ 40 * 606152 * 2
def baseEnd_606152 : Nat := 92221429832360788507367

theorem tailTrace_606152 : CollatzResearch.WordTrace tailWord_606152 prefixEnd_606152 92221429832360788507367 := by
  unfold tailWord_606152
  simp only [CollatzResearch.WordTrace]
  refine ⟨11054089850011150682430355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14738786466681534243240473 11054089850011150682430355)
  ·
    refine ⟨16581134775016726023645533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11054089850011150682430355 16581134775016726023645533)
    ·
      refine ⟨6217925540631272258867075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16581134775016726023645533 6217925540631272258867075)
      ·
        refine ⟨9326888310946908388300613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6217925540631272258867075 9326888310946908388300613)
        ·
          refine ⟨1748791558302545322806365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9326888310946908388300613 1748791558302545322806365)
          ·
            refine ⟨655796834363454496052387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1748791558302545322806365 655796834363454496052387)
            ·
              refine ⟨983695251545181744078581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655796834363454496052387 983695251545181744078581)
              ·
                refine ⟨92221429832360788507367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 983695251545181744078581 92221429832360788507367)
                ·
                  rfl

theorem cell20_606152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_606152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606152 prefixEnd_606152 := by exact prefixLift 606152
  have htrace : WordTrace (prefixWord ++ tailWord_606152) baseStart_606152 baseEnd_606152 := by
    simpa [prefixWord, tailWord_606152, baseEnd_606152] using wordTrace_append hprefix tailTrace_606152
  have hstable : (prefixWord ++ tailWord_606152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606152).length < 2 ^ (prefixWord ++ tailWord_606152).sum := by decide
  have hdescent : baseEnd_606152 < baseStart_606152 := by decide
  rcases family_descends (prefixWord ++ tailWord_606152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606180 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_606180 : Nat := 118140960795 + 606180 * 2 ^ 59
def prefixEnd_606180 : Nat := 4983230072969 + 3 ^ 40 * 606180 * 2
def baseEnd_606180 : Nat := 276677069460038712588653

theorem tailTrace_606180 : CollatzResearch.WordTrace tailWord_606180 prefixEnd_606180 276677069460038712588653 := by
  unfold tailWord_606180
  simp only [CollatzResearch.WordTrace]
  refine ⟨11054600471960431073439997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14739467295947241431253329 11054600471960431073439997)
  ·
    refine ⟨4145475176985161652539999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11054600471960431073439997 4145475176985161652539999)
    ·
      refine ⟨6218212765477742478809999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4145475176985161652539999 6218212765477742478809999)
      ·
        refine ⟨9327319148216613718214999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6218212765477742478809999 9327319148216613718214999)
        ·
          refine ⟨13990978722324920577322499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9327319148216613718214999 13990978722324920577322499)
          ·
            refine ⟨20986468083487380865983749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13990978722324920577322499 20986468083487380865983749)
            ·
              refine ⟨3934962765653883912371953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20986468083487380865983749 3934962765653883912371953)
              ·
                refine ⟨2951222074240412934278965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3934962765653883912371953 2951222074240412934278965)
                ·
                  refine ⟨276677069460038712588653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2951222074240412934278965 276677069460038712588653)
                  ·
                    rfl

theorem cell20_606180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_606180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606180 prefixEnd_606180 := by exact prefixLift 606180
  have htrace : WordTrace (prefixWord ++ tailWord_606180) baseStart_606180 baseEnd_606180 := by
    simpa [prefixWord, tailWord_606180, baseEnd_606180] using wordTrace_append hprefix tailTrace_606180
  have hstable : (prefixWord ++ tailWord_606180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606180).length < 2 ^ (prefixWord ++ tailWord_606180).sum := by decide
  have hdescent : baseEnd_606180 < baseStart_606180 := by decide
  rcases family_descends (prefixWord ++ tailWord_606180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606193 : List Nat := [1, 2, 2, 2, 6, 1, 1, 2, 3]
def baseStart_606193 : Nat := 118140960795 + 606193 * 2 ^ 59
def prefixEnd_606193 : Nat := 4983230072969 + 3 ^ 40 * 606193 * 2
def baseEnd_606193 : Nat := 276683003014268445155267

theorem tailTrace_606193 : CollatzResearch.WordTrace tailWord_606193 prefixEnd_606193 276683003014268445155267 := by
  unfold tailWord_606193
  simp only [CollatzResearch.WordTrace]
  refine ⟨22109675092873765367103233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14739783395249176911402155 22109675092873765367103233)
  ·
    refine ⟨16582256319655324025327425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22109675092873765367103233 16582256319655324025327425)
    ·
      refine ⟨12436692239741493018995569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16582256319655324025327425 12436692239741493018995569)
      ·
        refine ⟨9327519179806119764246677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12436692239741493018995569 9327519179806119764246677)
        ·
          refine ⟨437227461553411863949063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9327519179806119764246677 437227461553411863949063)
          ·
            refine ⟨655841192330117795923595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437227461553411863949063 655841192330117795923595)
            ·
              refine ⟨983761788495176693885393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655841192330117795923595 983761788495176693885393)
              ·
                refine ⟨737821341371382520414045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983761788495176693885393 737821341371382520414045)
                ·
                  refine ⟨276683003014268445155267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737821341371382520414045 276683003014268445155267)
                  ·
                    rfl

theorem cell20_606193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 3].length) (baseStart_606193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606193 prefixEnd_606193 := by exact prefixLift 606193
  have htrace : WordTrace (prefixWord ++ tailWord_606193) baseStart_606193 baseEnd_606193 := by
    simpa [prefixWord, tailWord_606193, baseEnd_606193] using wordTrace_append hprefix tailTrace_606193
  have hstable : (prefixWord ++ tailWord_606193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606193).length < 2 ^ (prefixWord ++ tailWord_606193).sum := by decide
  have hdescent : baseEnd_606193 < baseStart_606193 := by decide
  rcases family_descends (prefixWord ++ tailWord_606193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606204 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 4]
def baseStart_606204 : Nat := 118140960795 + 606204 * 2 ^ 59
def prefixEnd_606204 : Nat := 4983230072969 + 3 ^ 40 * 606204 * 2
def baseEnd_606204 : Nat := 276688023714001295788555

theorem tailTrace_606204 : CollatzResearch.WordTrace tailWord_606204 prefixEnd_606204 276688023714001295788555 := by
  unfold tailWord_606204
  simp only [CollatzResearch.WordTrace]
  refine ⟨11055038147916957122876833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14740050863889276163835777 11055038147916957122876833)
  ·
    refine ⟨8291278610937717842157625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11055038147916957122876833 8291278610937717842157625)
    ·
      refine ⟨6218458958203288381618219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8291278610937717842157625 6218458958203288381618219)
      ·
        refine ⟨9327688437304932572427329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6218458958203288381618219 9327688437304932572427329)
        ·
          refine ⟨6995766327978699429320497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9327688437304932572427329 6995766327978699429320497)
          ·
            refine ⟨5246824745984024571990373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6995766327978699429320497 5246824745984024571990373)
            ·
              refine ⟨983779639872004607248195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5246824745984024571990373 983779639872004607248195)
              ·
                refine ⟨1475669459808006910872293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983779639872004607248195 1475669459808006910872293)
                ·
                  refine ⟨276688023714001295788555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1475669459808006910872293 276688023714001295788555)
                  ·
                    rfl

theorem cell20_606204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_606204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606204 prefixEnd_606204 := by exact prefixLift 606204
  have htrace : WordTrace (prefixWord ++ tailWord_606204) baseStart_606204 baseEnd_606204 := by
    simpa [prefixWord, tailWord_606204, baseEnd_606204] using wordTrace_append hprefix tailTrace_606204
  have hstable : (prefixWord ++ tailWord_606204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606204).length < 2 ^ (prefixWord ++ tailWord_606204).sum := by decide
  have hdescent : baseEnd_606204 < baseStart_606204 := by decide
  rcases family_descends (prefixWord ++ tailWord_606204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606256 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_606256 : Nat := 118140960795 + 606256 * 2 ^ 59
def prefixEnd_606256 : Nat := 4983230072969 + 3 ^ 40 * 606256 * 2
def baseEnd_606256 : Nat := 276711757930920226055009

theorem tailTrace_606256 : CollatzResearch.WordTrace tailWord_606256 prefixEnd_606256 276711757930920226055009 := by
  unfold tailWord_606256
  simp only [CollatzResearch.WordTrace]
  refine ⟨11055986445822763563323311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14741315261097018084431081 11055986445822763563323311)
  ·
    refine ⟨16583979668734145344984967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11055986445822763563323311 16583979668734145344984967)
    ·
      refine ⟨24875969503101218017477451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16583979668734145344984967 24875969503101218017477451)
      ·
        refine ⟨37313954254651827026216177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24875969503101218017477451 37313954254651827026216177)
        ·
          refine ⟨27985465690988870269662133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37313954254651827026216177 27985465690988870269662133)
          ·
            refine ⟨2623637408530206587780825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27985465690988870269662133 2623637408530206587780825)
            ·
              refine ⟨1967728056397654940835619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2623637408530206587780825 1967728056397654940835619)
              ·
                refine ⟨2951592084596482411253429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1967728056397654940835619 2951592084596482411253429)
                ·
                  refine ⟨276711757930920226055009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2951592084596482411253429 276711757930920226055009)
                  ·
                    rfl

theorem cell20_606256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_606256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606256 prefixEnd_606256 := by exact prefixLift 606256
  have htrace : WordTrace (prefixWord ++ tailWord_606256) baseStart_606256 baseEnd_606256 := by
    simpa [prefixWord, tailWord_606256, baseEnd_606256] using wordTrace_append hprefix tailTrace_606256
  have hstable : (prefixWord ++ tailWord_606256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606256).length < 2 ^ (prefixWord ++ tailWord_606256).sum := by decide
  have hdescent : baseEnd_606256 < baseStart_606256 := by decide
  rcases family_descends (prefixWord ++ tailWord_606256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606311 : List Nat := [1, 1, 5, 1, 1, 2, 4, 2, 3]
def baseStart_606311 : Nat := 118140960795 + 606311 * 2 ^ 59
def prefixEnd_606311 : Nat := 4983230072969 + 3 ^ 40 * 606311 * 2
def baseEnd_606311 : Nat := 276736861429584479221451

theorem tailTrace_606311 : CollatzResearch.WordTrace tailWord_606311 prefixEnd_606311 276736861429584479221451 := by
  unfold tailWord_606311
  simp only [CollatzResearch.WordTrace]
  refine ⟨22113978906446271519898787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14742652604297514346599191 22113978906446271519898787)
  ·
    refine ⟨33170968359669407279848181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22113978906446271519898787 33170968359669407279848181)
    ·
      refine ⟨3109778283719006932485767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33170968359669407279848181 3109778283719006932485767)
      ·
        refine ⟨4664667425578510398728651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3109778283719006932485767 4664667425578510398728651)
        ·
          refine ⟨6997001138367765598092977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664667425578510398728651 6997001138367765598092977)
          ·
            refine ⟨5247750853775824198569733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6997001138367765598092977 5247750853775824198569733)
            ·
              refine ⟨983953285082967037231825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5247750853775824198569733 983953285082967037231825)
              ·
                refine ⟨737964963812225277923869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983953285082967037231825 737964963812225277923869)
                ·
                  refine ⟨276736861429584479221451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737964963812225277923869 276736861429584479221451)
                  ·
                    rfl

theorem cell20_606311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 3].length) (baseStart_606311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606311 prefixEnd_606311 := by exact prefixLift 606311
  have htrace : WordTrace (prefixWord ++ tailWord_606311) baseStart_606311 baseEnd_606311 := by
    simpa [prefixWord, tailWord_606311, baseEnd_606311] using wordTrace_append hprefix tailTrace_606311
  have hstable : (prefixWord ++ tailWord_606311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606311).length < 2 ^ (prefixWord ++ tailWord_606311).sum := by decide
  have hdescent : baseEnd_606311 < baseStart_606311 := by decide
  rcases family_descends (prefixWord ++ tailWord_606311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606314 : List Nat := [3, 1, 3, 2, 3, 1, 1, 4, 2]
def baseStart_606314 : Nat := 118140960795 + 606314 * 2 ^ 59
def prefixEnd_606314 : Nat := 4983230072969 + 3 ^ 40 * 606314 * 2
def baseEnd_606314 : Nat := 276738230711329802121439

theorem tailTrace_606314 : CollatzResearch.WordTrace tailWord_606314 prefixEnd_606314 276738230711329802121439 := by
  unfold tailWord_606314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528522081358850758064499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14742725550290268688171997 5528522081358850758064499)
  ·
    refine ⟨8292783122038276137096749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5528522081358850758064499 8292783122038276137096749)
    ·
      refine ⟨3109793670764353551411281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8292783122038276137096749 3109793670764353551411281)
      ·
        refine ⟨2332345253073265163558461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3109793670764353551411281 2332345253073265163558461)
        ·
          refine ⟨874629469902474436334423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2332345253073265163558461 874629469902474436334423)
          ·
            refine ⟨1311944204853711654501635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874629469902474436334423 1311944204853711654501635)
            ·
              refine ⟨1967916307280567481752453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1311944204853711654501635 1967916307280567481752453)
              ·
                refine ⟨368984307615106402828585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1967916307280567481752453 368984307615106402828585)
                ·
                  refine ⟨276738230711329802121439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368984307615106402828585 276738230711329802121439)
                  ·
                    rfl

theorem cell20_606314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_606314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606314 prefixEnd_606314 := by exact prefixLift 606314
  have htrace : WordTrace (prefixWord ++ tailWord_606314) baseStart_606314 baseEnd_606314 := by
    simpa [prefixWord, tailWord_606314, baseEnd_606314] using wordTrace_append hprefix tailTrace_606314
  have hstable : (prefixWord ++ tailWord_606314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606314).length < 2 ^ (prefixWord ++ tailWord_606314).sum := by decide
  have hdescent : baseEnd_606314 < baseStart_606314 := by decide
  rcases family_descends (prefixWord ++ tailWord_606314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606318 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_606318 : Nat := 118140960795 + 606318 * 2 ^ 59
def prefixEnd_606318 : Nat := 4983230072969 + 3 ^ 40 * 606318 * 2
def baseEnd_606318 : Nat := 276740056420323565988089

theorem tailTrace_606318 : CollatzResearch.WordTrace tailWord_606318 prefixEnd_606318 276740056420323565988089 := by
  unfold tailWord_606318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2764279277177613964425451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14742822811613941143602405 2764279277177613964425451)
  ·
    refine ⟨4146418915766420946638177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2764279277177613964425451 4146418915766420946638177)
    ·
      refine ⟨3109814186824815709978633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4146418915766420946638177 3109814186824815709978633)
      ·
        refine ⟨2332360640118611782483975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3109814186824815709978633 2332360640118611782483975)
        ·
          refine ⟨3498540960177917673725963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2332360640118611782483975 3498540960177917673725963)
          ·
            refine ⟨5247811440266876510588945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3498540960177917673725963 5247811440266876510588945)
            ·
              refine ⟨3935858580200157382941709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5247811440266876510588945 3935858580200157382941709)
              ·
                refine ⟨1475946967575059018603141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3935858580200157382941709 1475946967575059018603141)
                ·
                  refine ⟨276740056420323565988089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1475946967575059018603141 276740056420323565988089)
                  ·
                    rfl

theorem cell20_606318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_606318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606318 prefixEnd_606318 := by exact prefixLift 606318
  have htrace : WordTrace (prefixWord ++ tailWord_606318) baseStart_606318 baseEnd_606318 := by
    simpa [prefixWord, tailWord_606318, baseEnd_606318] using wordTrace_append hprefix tailTrace_606318
  have hstable : (prefixWord ++ tailWord_606318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606318).length < 2 ^ (prefixWord ++ tailWord_606318).sum := by decide
  have hdescent : baseEnd_606318 < baseStart_606318 := by decide
  rcases family_descends (prefixWord ++ tailWord_606318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606339 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 6]
def baseStart_606339 : Nat := 118140960795 + 606339 * 2 ^ 59
def prefixEnd_606339 : Nat := 4983230072969 + 3 ^ 40 * 606339 * 2
def baseEnd_606339 : Nat := 276749641392540826288003

theorem tailTrace_606339 : CollatzResearch.WordTrace tailWord_606339 prefixEnd_606339 276749641392540826288003 := by
  unfold tailWord_606339
  simp only [CollatzResearch.WordTrace]
  refine ⟨22115000150344832301918071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14743333433563221534612047 22115000150344832301918071)
  ·
    refine ⟨33172500225517248452877107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22115000150344832301918071 33172500225517248452877107)
    ·
      refine ⟨49758750338275872679315661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33172500225517248452877107 49758750338275872679315661)
      ·
        refine ⟨18659531376853452254743373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49758750338275872679315661 18659531376853452254743373)
        ·
          refine ⟨6997324266320044595528765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18659531376853452254743373 6997324266320044595528765)
          ·
            refine ⟨2623996599870016723323287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6997324266320044595528765 2623996599870016723323287)
            ·
              refine ⟨3935994899805025084984931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2623996599870016723323287 3935994899805025084984931)
              ·
                refine ⟨5903992349707537627477397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3935994899805025084984931 5903992349707537627477397)
                ·
                  refine ⟨276749641392540826288003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5903992349707537627477397 276749641392540826288003)
                  ·
                    rfl

theorem cell20_606339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_606339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606339 prefixEnd_606339 := by exact prefixLift 606339
  have htrace : WordTrace (prefixWord ++ tailWord_606339) baseStart_606339 baseEnd_606339 := by
    simpa [prefixWord, tailWord_606339, baseEnd_606339] using wordTrace_append hprefix tailTrace_606339
  have hstable : (prefixWord ++ tailWord_606339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606339).length < 2 ^ (prefixWord ++ tailWord_606339).sum := by decide
  have hdescent : baseEnd_606339 < baseStart_606339 := by decide
  rcases family_descends (prefixWord ++ tailWord_606339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606358 : List Nat := [5, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_606358 : Nat := 118140960795 + 606358 * 2 ^ 59
def prefixEnd_606358 : Nat := 4983230072969 + 3 ^ 40 * 606358 * 2
def baseEnd_606358 : Nat := 276758313510261204654593

theorem tailTrace_606358 : CollatzResearch.WordTrace tailWord_606358 prefixEnd_606358 276758313510261204654593 := by
  unfold tailWord_606358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1382230821079749909178733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14743795424850665697906485 1382230821079749909178733)
  ·
    refine ⟨518336557904906215942025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1382230821079749909178733 518336557904906215942025)
    ·
      refine ⟨388752418428679661956519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 518336557904906215942025 388752418428679661956519)
      ·
        refine ⟨583128627643019492934779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388752418428679661956519 583128627643019492934779)
        ·
          refine ⟨874692941464529239402169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583128627643019492934779 874692941464529239402169)
          ·
            refine ⟨656019706098396929551627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 874692941464529239402169 656019706098396929551627)
            ·
              refine ⟨984029559147595394327441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656019706098396929551627 984029559147595394327441)
              ·
                refine ⟨738022169360696545745581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 984029559147595394327441 738022169360696545745581)
                ·
                  refine ⟨276758313510261204654593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 738022169360696545745581 276758313510261204654593)
                  ·
                    rfl

theorem cell20_606358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_606358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606358 prefixEnd_606358 := by exact prefixLift 606358
  have htrace : WordTrace (prefixWord ++ tailWord_606358) baseStart_606358 baseEnd_606358 := by
    simpa [prefixWord, tailWord_606358, baseEnd_606358] using wordTrace_append hprefix tailTrace_606358
  have hstable : (prefixWord ++ tailWord_606358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606358).length < 2 ^ (prefixWord ++ tailWord_606358).sum := by decide
  have hdescent : baseEnd_606358 < baseStart_606358 := by decide
  rcases family_descends (prefixWord ++ tailWord_606358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606366 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_606366 : Nat := 118140960795 + 606366 * 2 ^ 59
def prefixEnd_606366 : Nat := 4983230072969 + 3 ^ 40 * 606366 * 2
def baseEnd_606366 : Nat := 276761964928248732387893

theorem tailTrace_606366 : CollatzResearch.WordTrace tailWord_606366 prefixEnd_606366 276761964928248732387893 := by
  unfold tailWord_606366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2764498115155876989143869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14743989947498010608767301 2764498115155876989143869)
  ·
    refine ⟨1036686793183453870928951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2764498115155876989143869 1036686793183453870928951)
    ·
      refine ⟨1555030189775180806393427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1036686793183453870928951 1555030189775180806393427)
      ·
        refine ⟨2332545284662771209590141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1555030189775180806393427 2332545284662771209590141)
        ·
          refine ⟨874704481748539203596303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2332545284662771209590141 874704481748539203596303)
          ·
            refine ⟨1312056722622808805394455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874704481748539203596303 1312056722622808805394455)
            ·
              refine ⟨1968085083934213208091683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1312056722622808805394455 1968085083934213208091683)
              ·
                refine ⟨2952127625901319812137525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1968085083934213208091683 2952127625901319812137525)
                ·
                  refine ⟨276761964928248732387893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2952127625901319812137525 276761964928248732387893)
                  ·
                    rfl

theorem cell20_606366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_606366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606366 prefixEnd_606366 := by exact prefixLift 606366
  have htrace : WordTrace (prefixWord ++ tailWord_606366) baseStart_606366 baseEnd_606366 := by
    simpa [prefixWord, tailWord_606366, baseEnd_606366] using wordTrace_append hprefix tailTrace_606366
  have hstable : (prefixWord ++ tailWord_606366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606366).length < 2 ^ (prefixWord ++ tailWord_606366).sum := by decide
  have hdescent : baseEnd_606366 < baseStart_606366 := by decide
  rcases family_descends (prefixWord ++ tailWord_606366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606434 : List Nat := [3, 3, 4, 1, 2, 1, 2, 1, 3]
def baseStart_606434 : Nat := 118140960795 + 606434 * 2 ^ 59
def prefixEnd_606434 : Nat := 4983230072969 + 3 ^ 40 * 606434 * 2
def baseEnd_606434 : Nat := 276793001981142718120949

theorem tailTrace_606434 : CollatzResearch.WordTrace tailWord_606434 prefixEnd_606434 276793001981142718120949 := by
  unfold tailWord_606434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5529616271250165881656589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14745643390000442351084237 5529616271250165881656589)
  ·
    refine ⟨2073606101718812205621221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5529616271250165881656589 2073606101718812205621221)
    ·
      refine ⟨388801144072277288553979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2073606101718812205621221 388801144072277288553979)
      ·
        refine ⟨583201716108415932830969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388801144072277288553979 583201716108415932830969)
        ·
          refine ⟨437401287081311949623227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 583201716108415932830969 437401287081311949623227)
          ·
            refine ⟨656101930621967924434841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437401287081311949623227 656101930621967924434841)
            ·
              refine ⟨492076447966475943326131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 656101930621967924434841 492076447966475943326131)
              ·
                refine ⟨738114671949713914989197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492076447966475943326131 738114671949713914989197)
                ·
                  refine ⟨276793001981142718120949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 738114671949713914989197 276793001981142718120949)
                  ·
                    rfl

theorem cell20_606434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_606434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606434 prefixEnd_606434 := by exact prefixLift 606434
  have htrace : WordTrace (prefixWord ++ tailWord_606434) baseStart_606434 baseEnd_606434 := by
    simpa [prefixWord, tailWord_606434, baseEnd_606434] using wordTrace_append hprefix tailTrace_606434
  have hstable : (prefixWord ++ tailWord_606434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606434).length < 2 ^ (prefixWord ++ tailWord_606434).sum := by decide
  have hdescent : baseEnd_606434 < baseStart_606434 := by decide
  rcases family_descends (prefixWord ++ tailWord_606434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606439 : List Nat := [1, 1, 5, 3, 1, 1, 1, 7]
def baseStart_606439 : Nat := 118140960795 + 606439 * 2 ^ 59
def prefixEnd_606439 : Nat := 4983230072969 + 3 ^ 40 * 606439 * 2
def baseEnd_606439 : Nat := 92265094705794974318087

theorem tailTrace_606439 : CollatzResearch.WordTrace tailWord_606439 prefixEnd_606439 92265094705794974318087 := by
  unfold tailWord_606439
  simp only [CollatzResearch.WordTrace]
  refine ⟨22118647449982549380558371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14745764966655032920372247 22118647449982549380558371)
  ·
    refine ⟨33177971174973824070837557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22118647449982549380558371 33177971174973824070837557)
    ·
      refine ⟨3110434797653796006641021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33177971174973824070837557 3110434797653796006641021)
      ·
        refine ⟨1166413049120173502490383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3110434797653796006641021 1166413049120173502490383)
        ·
          refine ⟨1749619573680260253735575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1166413049120173502490383 1749619573680260253735575)
          ·
            refine ⟨2624429360520390380603363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1749619573680260253735575 2624429360520390380603363)
            ·
              refine ⟨3936644040780585570905045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2624429360520390380603363 3936644040780585570905045)
              ·
                refine ⟨92265094705794974318087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3936644040780585570905045 92265094705794974318087)
                ·
                  rfl

theorem cell20_606439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 7].length) (baseStart_606439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606439 prefixEnd_606439 := by exact prefixLift 606439
  have htrace : WordTrace (prefixWord ++ tailWord_606439) baseStart_606439 baseEnd_606439 := by
    simpa [prefixWord, tailWord_606439, baseEnd_606439] using wordTrace_append hprefix tailTrace_606439
  have hstable : (prefixWord ++ tailWord_606439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606439).length < 2 ^ (prefixWord ++ tailWord_606439).sum := by decide
  have hdescent : baseEnd_606439 < baseStart_606439 := by decide
  rcases family_descends (prefixWord ++ tailWord_606439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606487 : List Nat := [1, 1, 3, 4, 1, 3, 1, 4, 2]
def baseStart_606487 : Nat := 118140960795 + 606487 * 2 ^ 59
def prefixEnd_606487 : Nat := 4983230072969 + 3 ^ 40 * 606487 * 2
def baseEnd_606487 : Nat := 276817192625310089354065

theorem tailTrace_606487 : CollatzResearch.WordTrace tailWord_606487 prefixEnd_606487 276817192625310089354065 := by
  unfold tailWord_606487
  simp only [CollatzResearch.WordTrace]
  refine ⟨22120398153808653578305715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14746932102539102385537143 22120398153808653578305715)
  ·
    refine ⟨33180597230712980367458573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22120398153808653578305715 33180597230712980367458573)
    ·
      refine ⟨12442723961517367637796965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33180597230712980367458573 12442723961517367637796965)
      ·
        refine ⟨2333010742784506432086931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12442723961517367637796965 2333010742784506432086931)
        ·
          refine ⟨3499516114176759648130397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2333010742784506432086931 3499516114176759648130397)
          ·
            refine ⟨1312318542816284868048899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3499516114176759648130397 1312318542816284868048899)
            ·
              refine ⟨1968477814224427302073349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1312318542816284868048899 1968477814224427302073349)
              ·
                refine ⟨369089590167080119138753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1968477814224427302073349 369089590167080119138753)
                ·
                  refine ⟨276817192625310089354065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 369089590167080119138753 276817192625310089354065)
                  ·
                    rfl

theorem cell20_606487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 2].length) (baseStart_606487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606487 prefixEnd_606487 := by exact prefixLift 606487
  have htrace : WordTrace (prefixWord ++ tailWord_606487) baseStart_606487 baseEnd_606487 := by
    simpa [prefixWord, tailWord_606487, baseEnd_606487] using wordTrace_append hprefix tailTrace_606487
  have hstable : (prefixWord ++ tailWord_606487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606487).length < 2 ^ (prefixWord ++ tailWord_606487).sum := by decide
  have hdescent : baseEnd_606487 < baseStart_606487 := by decide
  rcases family_descends (prefixWord ++ tailWord_606487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606515 : List Nat := [1, 1, 1, 2, 5, 1, 5, 4]
def baseStart_606515 : Nat := 118140960795 + 606515 * 2 ^ 59
def prefixEnd_606515 : Nat := 4983230072969 + 3 ^ 40 * 606515 * 2
def baseEnd_606515 : Nat := 92276657529422145473539

theorem tailTrace_606515 : CollatzResearch.WordTrace tailWord_606515 prefixEnd_606515 92276657529422145473539 := by
  unfold tailWord_606515
  simp only [CollatzResearch.WordTrace]
  refine ⟨22121419397707214360324999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14747612931804809573549999 22121419397707214360324999)
  ·
    refine ⟨33182129096560821540487499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22121419397707214360324999 33182129096560821540487499)
    ·
      refine ⟨49773193644841232310731249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33182129096560821540487499 49773193644841232310731249)
      ·
        refine ⟨37329895233630924233048437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49773193644841232310731249 37329895233630924233048437)
        ·
          refine ⟨3499677678152899146848291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37329895233630924233048437 3499677678152899146848291)
          ·
            refine ⟨5249516517229348720272437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3499677678152899146848291 5249516517229348720272437)
            ·
              refine ⟨492142173490251442525541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5249516517229348720272437 492142173490251442525541)
              ·
                refine ⟨92276657529422145473539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 492142173490251442525541 92276657529422145473539)
                ·
                  rfl

theorem cell20_606515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 4].length) (baseStart_606515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606515 prefixEnd_606515 := by exact prefixLift 606515
  have htrace : WordTrace (prefixWord ++ tailWord_606515) baseStart_606515 baseEnd_606515 := by
    simpa [prefixWord, tailWord_606515, baseEnd_606515] using wordTrace_append hprefix tailTrace_606515
  have hstable : (prefixWord ++ tailWord_606515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606515).length < 2 ^ (prefixWord ++ tailWord_606515).sum := by decide
  have hdescent : baseEnd_606515 < baseStart_606515 := by decide
  rcases family_descends (prefixWord ++ tailWord_606515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606532 : List Nat := [2, 3, 4, 1, 2, 1, 7]
def baseStart_606532 : Nat := 118140960795 + 606532 * 2 ^ 59
def prefixEnd_606532 : Nat := 4983230072969 + 3 ^ 40 * 606532 * 2
def baseEnd_606532 : Nat := 30759747983498881428209

theorem tailTrace_606532 : CollatzResearch.WordTrace tailWord_606532 prefixEnd_606532 30759747983498881428209 := by
  unfold tailWord_606532
  simp only [CollatzResearch.WordTrace]
  refine ⟨11061019719322813131846925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14748026292430417509129233 11061019719322813131846925)
  ·
    refine ⟨4147882394746054924442597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11061019719322813131846925 4147882394746054924442597)
    ·
      refine ⟨777727949014885298332987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4147882394746054924442597 777727949014885298332987)
      ·
        refine ⟨1166591923522327947499481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 777727949014885298332987 1166591923522327947499481)
        ·
          refine ⟨874943942641745960624611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1166591923522327947499481 874943942641745960624611)
          ·
            refine ⟨1312415913962618940936917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874943942641745960624611 1312415913962618940936917)
            ·
              refine ⟨30759747983498881428209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1312415913962618940936917 30759747983498881428209)
              ·
                rfl

theorem cell20_606532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 7].length) (baseStart_606532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606532 prefixEnd_606532 := by exact prefixLift 606532
  have htrace : WordTrace (prefixWord ++ tailWord_606532) baseStart_606532 baseEnd_606532 := by
    simpa [prefixWord, tailWord_606532, baseEnd_606532] using wordTrace_append hprefix tailTrace_606532
  have hstable : (prefixWord ++ tailWord_606532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606532).length < 2 ^ (prefixWord ++ tailWord_606532).sum := by decide
  have hdescent : baseEnd_606532 < baseStart_606532 := by decide
  rcases family_descends (prefixWord ++ tailWord_606532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606570 : List Nat := [3, 1, 3, 3, 1, 1, 4, 4]
def baseStart_606570 : Nat := 118140960795 + 606570 * 2 ^ 59
def prefixEnd_606570 : Nat := 4983230072969 + 3 ^ 40 * 606570 * 2
def baseEnd_606570 : Nat := 92285025362310229862353

theorem tailTrace_606570 : CollatzResearch.WordTrace tailWord_606570 prefixEnd_606570 92285025362310229862353 := by
  unfold tailWord_606570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5530856353126989688394291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14748950275005305835718109 5530856353126989688394291)
  ·
    refine ⟨8296284529690484532591437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5530856353126989688394291 8296284529690484532591437)
    ·
      refine ⟨3111106698633931699721789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8296284529690484532591437 3111106698633931699721789)
      ·
        refine ⟨1166665011987724387395671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3111106698633931699721789 1166665011987724387395671)
        ·
          refine ⟨1749997517981586581093507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1166665011987724387395671 1749997517981586581093507)
          ·
            refine ⟨2624996276972379871640261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1749997517981586581093507 2624996276972379871640261)
            ·
              refine ⟨492186801932321225932549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2624996276972379871640261 492186801932321225932549)
              ·
                refine ⟨92285025362310229862353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 492186801932321225932549 92285025362310229862353)
                ·
                  rfl

theorem cell20_606570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_606570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606570 prefixEnd_606570 := by exact prefixLift 606570
  have htrace : WordTrace (prefixWord ++ tailWord_606570) baseStart_606570 baseEnd_606570 := by
    simpa [prefixWord, tailWord_606570, baseEnd_606570] using wordTrace_append hprefix tailTrace_606570
  have hstable : (prefixWord ++ tailWord_606570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606570).length < 2 ^ (prefixWord ++ tailWord_606570).sum := by decide
  have hdescent : baseEnd_606570 < baseStart_606570 := by decide
  rcases family_descends (prefixWord ++ tailWord_606570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606615 : List Nat := [1, 1, 3, 3, 1, 1, 6, 1, 3]
def baseStart_606615 : Nat := 118140960795 + 606615 * 2 ^ 59
def prefixEnd_606615 : Nat := 4983230072969 + 3 ^ 40 * 606615 * 2
def baseEnd_606615 : Nat := 276875615313110533086875

theorem tailTrace_606615 : CollatzResearch.WordTrace tailWord_606615 prefixEnd_606615 276875615313110533086875 := by
  unfold tailWord_606615
  simp only [CollatzResearch.WordTrace]
  refine ⟨22125066697344931438965299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14750044464896620959310199 22125066697344931438965299)
  ·
    refine ⟨33187600046017397158447949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22125066697344931438965299 33187600046017397158447949)
    ·
      refine ⟨12445350017256523934417981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33187600046017397158447949 12445350017256523934417981)
      ·
        refine ⟨4667006256471196475406743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12445350017256523934417981 4667006256471196475406743)
        ·
          refine ⟨7000509384706794713110115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4667006256471196475406743 7000509384706794713110115)
          ·
            refine ⟨10500764077060192069665173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7000509384706794713110115 10500764077060192069665173)
            ·
              refine ⟨492223316112196503265555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10500764077060192069665173 492223316112196503265555)
              ·
                refine ⟨738334974168294754898333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492223316112196503265555 738334974168294754898333)
                ·
                  refine ⟨276875615313110533086875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 738334974168294754898333 276875615313110533086875)
                  ·
                    rfl

theorem cell20_606615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 3].length) (baseStart_606615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606615 prefixEnd_606615 := by exact prefixLift 606615
  have htrace : WordTrace (prefixWord ++ tailWord_606615) baseStart_606615 baseEnd_606615 := by
    simpa [prefixWord, tailWord_606615, baseEnd_606615] using wordTrace_append hprefix tailTrace_606615
  have hstable : (prefixWord ++ tailWord_606615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606615).length < 2 ^ (prefixWord ++ tailWord_606615).sum := by decide
  have hdescent : baseEnd_606615 < baseStart_606615 := by decide
  rcases family_descends (prefixWord ++ tailWord_606615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606653 : List Nat := [1, 4, 1, 2, 2, 3, 2, 2, 3]
def baseStart_606653 : Nat := 118140960795 + 606653 * 2 ^ 59
def prefixEnd_606653 : Nat := 4983230072969 + 3 ^ 40 * 606653 * 2
def baseEnd_606653 : Nat := 276892959548551289820053

theorem tailTrace_606653 : CollatzResearch.WordTrace tailWord_606653 prefixEnd_606653 276892959548551289820053 := by
  unfold tailWord_606653
  simp only [CollatzResearch.WordTrace]
  refine ⟨22126452671207263928848613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14750968447471509285899075 22126452671207263928848613)
  ·
    refine ⟨4148709875851361986659115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22126452671207263928848613 4148709875851361986659115)
    ·
      refine ⟨6223064813777042979988673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4148709875851361986659115 6223064813777042979988673)
      ·
        refine ⟨4667298610332782234991505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6223064813777042979988673 4667298610332782234991505)
        ·
          refine ⟨3500473957749586676243629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4667298610332782234991505 3500473957749586676243629)
          ·
            refine ⟨1312677734156095003591361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3500473957749586676243629 1312677734156095003591361)
            ·
              refine ⟨984508300617071252693521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1312677734156095003591361 984508300617071252693521)
              ·
                refine ⟨738381225462803439520141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 984508300617071252693521 738381225462803439520141)
                ·
                  refine ⟨276892959548551289820053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 738381225462803439520141 276892959548551289820053)
                  ·
                    rfl

theorem cell20_606653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_606653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606653 prefixEnd_606653 := by exact prefixLift 606653
  have htrace : WordTrace (prefixWord ++ tailWord_606653) baseStart_606653 baseEnd_606653 := by
    simpa [prefixWord, tailWord_606653, baseEnd_606653] using wordTrace_append hprefix tailTrace_606653
  have hstable : (prefixWord ++ tailWord_606653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606653).length < 2 ^ (prefixWord ++ tailWord_606653).sum := by decide
  have hdescent : baseEnd_606653 < baseStart_606653 := by decide
  rcases family_descends (prefixWord ++ tailWord_606653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606681 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 4]
def baseStart_606681 : Nat := 118140960795 + 606681 * 2 ^ 59
def prefixEnd_606681 : Nat := 4983230072969 + 3 ^ 40 * 606681 * 2
def baseEnd_606681 : Nat := 276905739511507636886605

theorem tailTrace_606681 : CollatzResearch.WordTrace tailWord_606681 prefixEnd_606681 276905739511507636886605 := by
  unfold tailWord_606681
  simp only [CollatzResearch.WordTrace]
  refine ⟨22127473915105824710867897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14751649276737216473911931 22127473915105824710867897)
  ·
    refine ⟨16595605436329368533150923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22127473915105824710867897 16595605436329368533150923)
    ·
      refine ⟨24893408154494052799726385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16595605436329368533150923 24893408154494052799726385)
      ·
        refine ⟨18670056115870539599794789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24893408154494052799726385 18670056115870539599794789)
        ·
          refine ⟨3500635521725726174961523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18670056115870539599794789 3500635521725726174961523)
          ·
            refine ⟨5250953282588589262442285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3500635521725726174961523 5250953282588589262442285)
            ·
              refine ⟨1969107480970720973415857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5250953282588589262442285 1969107480970720973415857)
              ·
                refine ⟨1476830610728040730061893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1969107480970720973415857 1476830610728040730061893)
                ·
                  refine ⟨276905739511507636886605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1476830610728040730061893 276905739511507636886605)
                  ·
                    rfl

theorem cell20_606681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_606681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606681 prefixEnd_606681 := by exact prefixLift 606681
  have htrace : WordTrace (prefixWord ++ tailWord_606681) baseStart_606681 baseEnd_606681 := by
    simpa [prefixWord, tailWord_606681, baseEnd_606681] using wordTrace_append hprefix tailTrace_606681
  have hstable : (prefixWord ++ tailWord_606681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606681).length < 2 ^ (prefixWord ++ tailWord_606681).sum := by decide
  have hdescent : baseEnd_606681 < baseStart_606681 := by decide
  rcases family_descends (prefixWord ++ tailWord_606681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606719 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 4]
def baseStart_606719 : Nat := 118140960795 + 606719 * 2 ^ 59
def prefixEnd_606719 : Nat := 4983230072969 + 3 ^ 40 * 606719 * 2
def baseEnd_606719 : Nat := 276923083746948393619783

theorem tailTrace_606719 : CollatzResearch.WordTrace tailWord_606719 prefixEnd_606719 276923083746948393619783 := by
  unfold tailWord_606719
  simp only [CollatzResearch.WordTrace]
  refine ⟨22128859888968157200751211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14752573259312104800500807 22128859888968157200751211)
  ·
    refine ⟨33193289833452235801126817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22128859888968157200751211 33193289833452235801126817)
    ·
      refine ⟨24894967375089176850845113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33193289833452235801126817 24894967375089176850845113)
      ·
        refine ⟨18671225531316882638133835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24894967375089176850845113 18671225531316882638133835)
        ·
          refine ⟨28006838296975323957200753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18671225531316882638133835 28006838296975323957200753)
          ·
            refine ⟨21005128722731492967900565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28006838296975323957200753 21005128722731492967900565)
            ·
              refine ⟨984615408878038732870339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21005128722731492967900565 984615408878038732870339)
              ·
                refine ⟨1476923113317058099305509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984615408878038732870339 1476923113317058099305509)
                ·
                  refine ⟨276923083746948393619783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1476923113317058099305509 276923083746948393619783)
                  ·
                    rfl

theorem cell20_606719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_606719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606719 prefixEnd_606719 := by exact prefixLift 606719
  have htrace : WordTrace (prefixWord ++ tailWord_606719) baseStart_606719 baseEnd_606719 := by
    simpa [prefixWord, tailWord_606719, baseEnd_606719] using wordTrace_append hprefix tailTrace_606719
  have hstable : (prefixWord ++ tailWord_606719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606719).length < 2 ^ (prefixWord ++ tailWord_606719).sum := by decide
  have hdescent : baseEnd_606719 < baseStart_606719 := by decide
  rcases family_descends (prefixWord ++ tailWord_606719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606771 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 5]
def baseStart_606771 : Nat := 118140960795 + 606771 * 2 ^ 59
def prefixEnd_606771 : Nat := 4983230072969 + 3 ^ 40 * 606771 * 2
def baseEnd_606771 : Nat := 276946817963867323886237

theorem tailTrace_606771 : CollatzResearch.WordTrace tailWord_606771 prefixEnd_606771 276946817963867323886237 := by
  unfold tailWord_606771
  simp only [CollatzResearch.WordTrace]
  refine ⟨22130756484779770081644167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14753837656519846721096111 22130756484779770081644167)
  ·
    refine ⟨33196134727169655122466251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22130756484779770081644167 33196134727169655122466251)
    ·
      refine ⟨49794202090754482683699377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33196134727169655122466251 49794202090754482683699377)
      ·
        refine ⟨37345651568065862012774533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49794202090754482683699377 37345651568065862012774533)
        ·
          refine ⟨7002309669012349127395225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37345651568065862012774533 7002309669012349127395225)
          ·
            refine ⟨5251732251759261845546419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7002309669012349127395225 5251732251759261845546419)
            ·
              refine ⟨7877598377638892768319629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5251732251759261845546419 7877598377638892768319629)
              ·
                refine ⟨2954099391614584788119861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7877598377638892768319629 2954099391614584788119861)
                ·
                  refine ⟨276946817963867323886237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2954099391614584788119861 276946817963867323886237)
                  ·
                    rfl

theorem cell20_606771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_606771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606771 prefixEnd_606771 := by exact prefixLift 606771
  have htrace : WordTrace (prefixWord ++ tailWord_606771) baseStart_606771 baseEnd_606771 := by
    simpa [prefixWord, tailWord_606771, baseEnd_606771] using wordTrace_append hprefix tailTrace_606771
  have hstable : (prefixWord ++ tailWord_606771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606771).length < 2 ^ (prefixWord ++ tailWord_606771).sum := by decide
  have hdescent : baseEnd_606771 < baseStart_606771 := by decide
  rcases family_descends (prefixWord ++ tailWord_606771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606781 : List Nat := [1, 4, 1, 3, 2, 2, 2, 5]
def baseStart_606781 : Nat := 118140960795 + 606781 * 2 ^ 59
def prefixEnd_606781 : Nat := 4983230072969 + 3 ^ 40 * 606781 * 2
def baseEnd_606781 : Nat := 92317127412117244517621

theorem tailTrace_606781 : CollatzResearch.WordTrace tailWord_606781 prefixEnd_606781 92317127412117244517621 := by
  unfold tailWord_606781
  simp only [CollatzResearch.WordTrace]
  refine ⟨22131121214743541789508197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14754080809829027859672131 22131121214743541789508197)
  ·
    refine ⟨4149585227764414085532787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22131121214743541789508197 4149585227764414085532787)
    ·
      refine ⟨6224377841646621128299181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4149585227764414085532787 6224377841646621128299181)
      ·
        refine ⟨2334141690617482923112193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6224377841646621128299181 2334141690617482923112193)
        ·
          refine ⟨1750606267963112192334145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2334141690617482923112193 1750606267963112192334145)
          ·
            refine ⟨1312954700972334144250609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1750606267963112192334145 1312954700972334144250609)
            ·
              refine ⟨984716025729250608187957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1312954700972334144250609 984716025729250608187957)
              ·
                refine ⟨92317127412117244517621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 984716025729250608187957 92317127412117244517621)
                ·
                  rfl

theorem cell20_606781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 5].length) (baseStart_606781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606781 prefixEnd_606781 := by exact prefixLift 606781
  have htrace : WordTrace (prefixWord ++ tailWord_606781) baseStart_606781 baseEnd_606781 := by
    simpa [prefixWord, tailWord_606781, baseEnd_606781] using wordTrace_append hprefix tailTrace_606781
  have hstable : (prefixWord ++ tailWord_606781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606781).length < 2 ^ (prefixWord ++ tailWord_606781).sum := by decide
  have hdescent : baseEnd_606781 < baseStart_606781 := by decide
  rcases family_descends (prefixWord ++ tailWord_606781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606802 : List Nat := [3, 2, 2, 1, 2, 1, 1, 8]
def baseStart_606802 : Nat := 118140960795 + 606802 * 2 ^ 59
def prefixEnd_606802 : Nat := 4983230072969 + 3 ^ 40 * 606802 * 2
def baseEnd_606802 : Nat := 92320322402856331284259

theorem tailTrace_606802 : CollatzResearch.WordTrace tailWord_606802 prefixEnd_606802 92320322402856331284259 := by
  unfold tailWord_606802
  simp only [CollatzResearch.WordTrace]
  refine ⟨5532971786916865594005665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14754591431778308250681773 5532971786916865594005665)
  ·
    refine ⟨4149728840187649195504249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5532971786916865594005665 4149728840187649195504249)
    ·
      refine ⟨3112296630140736896628187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4149728840187649195504249 3112296630140736896628187)
      ·
        refine ⟨4668444945211105344942281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3112296630140736896628187 4668444945211105344942281)
        ·
          refine ⟨3501333708908329008706711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4668444945211105344942281 3501333708908329008706711)
          ·
            refine ⟨5252000563362493513060067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3501333708908329008706711 5252000563362493513060067)
            ·
              refine ⟨7878000845043740269590101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5252000563362493513060067 7878000845043740269590101)
              ·
                refine ⟨92320322402856331284259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7878000845043740269590101 92320322402856331284259)
                ·
                  rfl

theorem cell20_606802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_606802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606802 prefixEnd_606802 := by exact prefixLift 606802
  have htrace : WordTrace (prefixWord ++ tailWord_606802) baseStart_606802 baseEnd_606802 := by
    simpa [prefixWord, tailWord_606802, baseEnd_606802] using wordTrace_append hprefix tailTrace_606802
  have hstable : (prefixWord ++ tailWord_606802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606802).length < 2 ^ (prefixWord ++ tailWord_606802).sum := by decide
  have hdescent : baseEnd_606802 < baseStart_606802 := by decide
  rcases family_descends (prefixWord ++ tailWord_606802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606829 : List Nat := [1, 5, 1, 1, 3, 2, 1, 4, 2]
def baseStart_606829 : Nat := 118140960795 + 606829 * 2 ^ 59
def prefixEnd_606829 : Nat := 4983230072969 + 3 ^ 40 * 606829 * 2
def baseEnd_606829 : Nat := 276973290744276899952667

theorem tailTrace_606829 : CollatzResearch.WordTrace tailWord_606829 prefixEnd_606829 276973290744276899952667 := by
  unfold tailWord_606829
  simp only [CollatzResearch.WordTrace]
  refine ⟨22132871918569645987255541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14755247945713097324837027 22132871918569645987255541)
  ·
    refine ⟨2074956742365904311305207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22132871918569645987255541 2074956742365904311305207)
    ·
      refine ⟨3112435113548856466957811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2074956742365904311305207 3112435113548856466957811)
      ·
        refine ⟨4668652670323284700436717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3112435113548856466957811 4668652670323284700436717)
        ·
          refine ⟨1750744751371231762663769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4668652670323284700436717 1750744751371231762663769)
          ·
            refine ⟨1313058563528423821997827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1750744751371231762663769 1313058563528423821997827)
            ·
              refine ⟨1969587845292635732996741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313058563528423821997827 1969587845292635732996741)
              ·
                refine ⟨369297720992369199936889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1969587845292635732996741 369297720992369199936889)
                ·
                  refine ⟨276973290744276899952667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 369297720992369199936889 276973290744276899952667)
                  ·
                    rfl

theorem cell20_606829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_606829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606829 prefixEnd_606829 := by exact prefixLift 606829
  have htrace : WordTrace (prefixWord ++ tailWord_606829) baseStart_606829 baseEnd_606829 := by
    simpa [prefixWord, tailWord_606829, baseEnd_606829] using wordTrace_append hprefix tailTrace_606829
  have hstable : (prefixWord ++ tailWord_606829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606829).length < 2 ^ (prefixWord ++ tailWord_606829).sum := by decide
  have hdescent : baseEnd_606829 < baseStart_606829 := by decide
  rcases family_descends (prefixWord ++ tailWord_606829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606909 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 4]
def baseStart_606909 : Nat := 118140960795 + 606909 * 2 ^ 59
def prefixEnd_606909 : Nat := 4983230072969 + 3 ^ 40 * 606909 * 2
def baseEnd_606909 : Nat := 277009804924152177285673

theorem tailTrace_606909 : CollatzResearch.WordTrace tailWord_606909 prefixEnd_606909 277009804924152177285673 := by
  unfold tailWord_606909
  simp only [CollatzResearch.WordTrace]
  refine ⟨22135789758279819650167781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14757193172186546433445187 22135789758279819650167781)
  ·
    refine ⟨4150460579677466184406459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22135789758279819650167781 4150460579677466184406459)
    ·
      refine ⟨6225690869516199276609689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4150460579677466184406459 6225690869516199276609689)
      ·
        refine ⟨4669268152137149457457267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6225690869516199276609689 4669268152137149457457267)
        ·
          refine ⟨7003902228205724186185901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4669268152137149457457267 7003902228205724186185901)
          ·
            refine ⟨2626463335577146569819713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7003902228205724186185901 2626463335577146569819713)
            ·
              refine ⟨1969847501682859927364785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2626463335577146569819713 1969847501682859927364785)
              ·
                refine ⟨1477385626262144945523589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1969847501682859927364785 1477385626262144945523589)
                ·
                  refine ⟨277009804924152177285673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1477385626262144945523589 277009804924152177285673)
                  ·
                    rfl

theorem cell20_606909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_606909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606909 prefixEnd_606909 := by exact prefixLift 606909
  have htrace : WordTrace (prefixWord ++ tailWord_606909) baseStart_606909 baseEnd_606909 := by
    simpa [prefixWord, tailWord_606909, baseEnd_606909] using wordTrace_append hprefix tailTrace_606909
  have hstable : (prefixWord ++ tailWord_606909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606909).length < 2 ^ (prefixWord ++ tailWord_606909).sum := by decide
  have hdescent : baseEnd_606909 < baseStart_606909 := by decide
  rcases family_descends (prefixWord ++ tailWord_606909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606918 : List Nat := [6, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_606918 : Nat := 118140960795 + 606918 * 2 ^ 59
def prefixEnd_606918 : Nat := 4983230072969 + 3 ^ 40 * 606918 * 2
def baseEnd_606918 : Nat := 277013912769388145985637

theorem tailTrace_606918 : CollatzResearch.WordTrace tailWord_606918 prefixEnd_606918 277013912769388145985637 := by
  unfold tailWord_606918
  simp only [CollatzResearch.WordTrace]
  refine ⟨691753687976475443351419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14757412010164809458163605 691753687976475443351419)
  ·
    refine ⟨1037630531964713165027129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 691753687976475443351419 1037630531964713165027129)
    ·
      refine ⟨778222898973534873770347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1037630531964713165027129 778222898973534873770347)
      ·
        refine ⟨1167334348460302310655521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778222898973534873770347 1167334348460302310655521)
        ·
          refine ⟨875500761345226732991641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1167334348460302310655521 875500761345226732991641)
          ·
            refine ⟨656625571008920049743731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 875500761345226732991641 656625571008920049743731)
            ·
              refine ⟨984938356513380074615597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656625571008920049743731 984938356513380074615597)
              ·
                refine ⟨369351883692517527980849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 984938356513380074615597 369351883692517527980849)
                ·
                  refine ⟨277013912769388145985637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 369351883692517527980849 277013912769388145985637)
                  ·
                    rfl

theorem cell20_606918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_606918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606918 prefixEnd_606918 := by exact prefixLift 606918
  have htrace : WordTrace (prefixWord ++ tailWord_606918) baseStart_606918 baseEnd_606918 := by
    simpa [prefixWord, tailWord_606918, baseEnd_606918] using wordTrace_append hprefix tailTrace_606918
  have hstable : (prefixWord ++ tailWord_606918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606918).length < 2 ^ (prefixWord ++ tailWord_606918).sum := by decide
  have hdescent : baseEnd_606918 < baseStart_606918 := by decide
  rcases family_descends (prefixWord ++ tailWord_606918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606943 : List Nat := [1, 1, 2, 3, 2, 4, 3, 2, 2]
def baseStart_606943 : Nat := 118140960795 + 606943 * 2 ^ 59
def prefixEnd_606943 : Nat := 4983230072969 + 3 ^ 40 * 606943 * 2
def baseEnd_606943 : Nat := 277025323450599170152201

theorem tailTrace_606943 : CollatzResearch.WordTrace tailWord_606943 prefixEnd_606943 277025323450599170152201 := by
  unfold tailWord_606943
  simp only [CollatzResearch.WordTrace]
  refine ⟨22137029840156643456905483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14758019893437762304603655 22137029840156643456905483)
  ·
    refine ⟨33205544760234965185358225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22137029840156643456905483 33205544760234965185358225)
    ·
      refine ⟨24904158570176223889018669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33205544760234965185358225 24904158570176223889018669)
      ·
        refine ⟨9339059463816083958382001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24904158570176223889018669 9339059463816083958382001)
        ·
          refine ⟨7004294597862062968786501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9339059463816083958382001 7004294597862062968786501)
          ·
            refine ⟨1313305237099136806647469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7004294597862062968786501 1313305237099136806647469)
            ·
              refine ⟨492489463912176302492801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1313305237099136806647469 492489463912176302492801)
              ·
                refine ⟨369367097934132226869601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 492489463912176302492801 369367097934132226869601)
                ·
                  refine ⟨277025323450599170152201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 369367097934132226869601 277025323450599170152201)
                  ·
                    rfl

theorem cell20_606943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 2].length) (baseStart_606943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606943 prefixEnd_606943 := by exact prefixLift 606943
  have htrace : WordTrace (prefixWord ++ tailWord_606943) baseStart_606943 baseEnd_606943 := by
    simpa [prefixWord, tailWord_606943, baseEnd_606943] using wordTrace_append hprefix tailTrace_606943
  have hstable : (prefixWord ++ tailWord_606943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606943).length < 2 ^ (prefixWord ++ tailWord_606943).sum := by decide
  have hdescent : baseEnd_606943 < baseStart_606943 := by decide
  rcases family_descends (prefixWord ++ tailWord_606943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606968 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_606968 : Nat := 118140960795 + 606968 * 2 ^ 59
def prefixEnd_606968 : Nat := 4983230072969 + 3 ^ 40 * 606968 * 2
def baseEnd_606968 : Nat := 277036734131810194318765

theorem tailTrace_606968 : CollatzResearch.WordTrace tailWord_606968 prefixEnd_606968 277036734131810194318765 := by
  unfold tailWord_606968
  simp only [CollatzResearch.WordTrace]
  refine ⟨11068970832533036363282779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14758627776710715151043705 11068970832533036363282779)
  ·
    refine ⟨16603456248799554544924169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11068970832533036363282779 16603456248799554544924169)
    ·
      refine ⟨12452592186599665908693127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16603456248799554544924169 12452592186599665908693127)
      ·
        refine ⟨18678888279899498863039691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12452592186599665908693127 18678888279899498863039691)
        ·
          refine ⟨28018332419849248294559537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18678888279899498863039691 28018332419849248294559537)
          ·
            refine ⟨21013749314886936220919653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28018332419849248294559537 21013749314886936220919653)
            ·
              refine ⟨3940077996541300541422435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21013749314886936220919653 3940077996541300541422435)
              ·
                refine ⟨5910116994811950812133653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3940077996541300541422435 5910116994811950812133653)
                ·
                  refine ⟨277036734131810194318765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5910116994811950812133653 277036734131810194318765)
                  ·
                    rfl

theorem cell20_606968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_606968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606968 prefixEnd_606968 := by exact prefixLift 606968
  have htrace : WordTrace (prefixWord ++ tailWord_606968) baseStart_606968 baseEnd_606968 := by
    simpa [prefixWord, tailWord_606968, baseEnd_606968] using wordTrace_append hprefix tailTrace_606968
  have hstable : (prefixWord ++ tailWord_606968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606968).length < 2 ^ (prefixWord ++ tailWord_606968).sum := by decide
  have hdescent : baseEnd_606968 < baseStart_606968 := by decide
  rcases family_descends (prefixWord ++ tailWord_606968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606994 : List Nat := [3, 2, 4, 1, 3, 1, 2, 2, 2]
def baseStart_606994 : Nat := 118140960795 + 606994 * 2 ^ 59
def prefixEnd_606994 : Nat := 4983230072969 + 3 ^ 40 * 606994 * 2
def baseEnd_606994 : Nat := 277048601240269659451993

theorem tailTrace_606994 : CollatzResearch.WordTrace tailWord_606994 prefixEnd_606994 277048601240269659451993 := by
  unfold tailWord_606994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5534722490742969791753009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14759259975314586111341357 5534722490742969791753009)
  ·
    refine ⟨4151041868057227343814757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5534722490742969791753009 4151041868057227343814757)
    ·
      refine ⟨778320350260730126965267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4151041868057227343814757 778320350260730126965267)
      ·
        refine ⟨1167480525391095190447901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778320350260730126965267 1167480525391095190447901)
        ·
          refine ⟨437805197021660696417963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1167480525391095190447901 437805197021660696417963)
          ·
            refine ⟨656707795532491044626945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437805197021660696417963 656707795532491044626945)
            ·
              refine ⟨492530846649368283470209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 656707795532491044626945 492530846649368283470209)
              ·
                refine ⟨369398134987026212602657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 492530846649368283470209 369398134987026212602657)
                ·
                  refine ⟨277048601240269659451993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 369398134987026212602657 277048601240269659451993)
                  ·
                    rfl

theorem cell20_606994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_606994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_606994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_606994 prefixEnd_606994 := by exact prefixLift 606994
  have htrace : WordTrace (prefixWord ++ tailWord_606994) baseStart_606994 baseEnd_606994 := by
    simpa [prefixWord, tailWord_606994, baseEnd_606994] using wordTrace_append hprefix tailTrace_606994
  have hstable : (prefixWord ++ tailWord_606994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606994).length < 2 ^ (prefixWord ++ tailWord_606994).sum := by decide
  have hdescent : baseEnd_606994 < baseStart_606994 := by decide
  rcases family_descends (prefixWord ++ tailWord_606994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607002 : List Nat := [3, 1, 1, 3, 2, 1, 3, 4, 2]
def baseStart_607002 : Nat := 118140960795 + 607002 * 2 ^ 59
def prefixEnd_607002 : Nat := 4983230072969 + 3 ^ 40 * 607002 * 2
def baseEnd_607002 : Nat := 277052252658257187185293

theorem tailTrace_607002 : CollatzResearch.WordTrace tailWord_607002 prefixEnd_607002 277052252658257187185293 := by
  unfold tailWord_607002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5534795436735724133325815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14759454497961931022202173 5534795436735724133325815)
  ·
    refine ⟨8302193155103586199988723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5534795436735724133325815 8302193155103586199988723)
    ·
      refine ⟨12453289732655379299983085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8302193155103586199988723 12453289732655379299983085)
      ·
        refine ⟨4669983649745767237493657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12453289732655379299983085 4669983649745767237493657)
        ·
          refine ⟨3502487737309325428120243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4669983649745767237493657 3502487737309325428120243)
          ·
            refine ⟨5253731605963988142180365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502487737309325428120243 5253731605963988142180365)
            ·
              refine ⟨1970149352236495553317637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5253731605963988142180365 1970149352236495553317637)
              ·
                refine ⟨369403003544342916247057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1970149352236495553317637 369403003544342916247057)
                ·
                  refine ⟨277052252658257187185293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 369403003544342916247057 277052252658257187185293)
                  ·
                    rfl

theorem cell20_607002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_607002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607002 prefixEnd_607002 := by exact prefixLift 607002
  have htrace : WordTrace (prefixWord ++ tailWord_607002) baseStart_607002 baseEnd_607002 := by
    simpa [prefixWord, tailWord_607002, baseEnd_607002] using wordTrace_append hprefix tailTrace_607002
  have hstable : (prefixWord ++ tailWord_607002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607002).length < 2 ^ (prefixWord ++ tailWord_607002).sum := by decide
  have hdescent : baseEnd_607002 < baseStart_607002 := by decide
  rcases family_descends (prefixWord ++ tailWord_607002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607005 : List Nat := [1, 4, 2, 4, 2, 1, 1, 5]
def baseStart_607005 : Nat := 118140960795 + 607005 * 2 ^ 59
def prefixEnd_607005 : Nat := 4983230072969 + 3 ^ 40 * 607005 * 2
def baseEnd_607005 : Nat := 92351207313334170028427

theorem tailTrace_607005 : CollatzResearch.WordTrace tailWord_607005 prefixEnd_607005 92351207313334170028427 := by
  unfold tailWord_607005
  simp only [CollatzResearch.WordTrace]
  refine ⟨22139291165932028045662469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14759527443954685363774979 22139291165932028045662469)
  ·
    refine ⟨4151117093612255258561713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22139291165932028045662469 4151117093612255258561713)
    ·
      refine ⟨3113337820209191443921285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4151117093612255258561713 3113337820209191443921285)
      ·
        refine ⟨583750841289223395735241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3113337820209191443921285 583750841289223395735241)
        ·
          refine ⟨437813130966917546801431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 583750841289223395735241 437813130966917546801431)
          ·
            refine ⟨656719696450376320202147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437813130966917546801431 656719696450376320202147)
            ·
              refine ⟨985079544675564480303221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656719696450376320202147 985079544675564480303221)
              ·
                refine ⟨92351207313334170028427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 985079544675564480303221 92351207313334170028427)
                ·
                  rfl

theorem cell20_607005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 5].length) (baseStart_607005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607005 prefixEnd_607005 := by exact prefixLift 607005
  have htrace : WordTrace (prefixWord ++ tailWord_607005) baseStart_607005 baseEnd_607005 := by
    simpa [prefixWord, tailWord_607005, baseEnd_607005] using wordTrace_append hprefix tailTrace_607005
  have hstable : (prefixWord ++ tailWord_607005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607005).length < 2 ^ (prefixWord ++ tailWord_607005).sum := by decide
  have hdescent : baseEnd_607005 < baseStart_607005 := by decide
  rcases family_descends (prefixWord ++ tailWord_607005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607016 : List Nat := [2, 1, 5, 1, 1, 1, 1, 5, 3]
def baseStart_607016 : Nat := 118140960795 + 607016 * 2 ^ 59
def prefixEnd_607016 : Nat := 4983230072969 + 3 ^ 40 * 607016 * 2
def baseEnd_607016 : Nat := 277058642639735360718569

theorem tailTrace_607016 : CollatzResearch.WordTrace tailWord_607016 prefixEnd_607016 277058642639735360718569 := by
  unfold tailWord_607016
  simp only [CollatzResearch.WordTrace]
  refine ⟨11069846184446088462156451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14759794912594784616208601 11069846184446088462156451)
  ·
    refine ⟨16604769276669132693234677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11069846184446088462156451 16604769276669132693234677)
    ·
      refine ⟨1556697119687731189990751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16604769276669132693234677 1556697119687731189990751)
      ·
        refine ⟨2335045679531596784986127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1556697119687731189990751 2335045679531596784986127)
        ·
          refine ⟨3502568519297395177479191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2335045679531596784986127 3502568519297395177479191)
          ·
            refine ⟨5253852778946092766218787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502568519297395177479191 5253852778946092766218787)
            ·
              refine ⟨7880779168419139149328181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5253852778946092766218787 7880779168419139149328181)
              ·
                refine ⟨738823047039294295249517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7880779168419139149328181 738823047039294295249517)
                ·
                  refine ⟨277058642639735360718569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 738823047039294295249517 277058642639735360718569)
                  ·
                    rfl

theorem cell20_607016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_607016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607016 prefixEnd_607016 := by exact prefixLift 607016
  have htrace : WordTrace (prefixWord ++ tailWord_607016) baseStart_607016 baseEnd_607016 := by
    simpa [prefixWord, tailWord_607016, baseEnd_607016] using wordTrace_append hprefix tailTrace_607016
  have hstable : (prefixWord ++ tailWord_607016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607016).length < 2 ^ (prefixWord ++ tailWord_607016).sum := by decide
  have hdescent : baseEnd_607016 < baseStart_607016 := by decide
  rcases family_descends (prefixWord ++ tailWord_607016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607046 : List Nat := [6, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_607046 : Nat := 118140960795 + 607046 * 2 ^ 59
def prefixEnd_607046 : Nat := 4983230072969 + 3 ^ 40 * 607046 * 2
def baseEnd_607046 : Nat := 277072335457188589718447

theorem tailTrace_607046 : CollatzResearch.WordTrace tailWord_607046 prefixEnd_607046 277072335457188589718447 := by
  unfold tailWord_607046
  simp only [CollatzResearch.WordTrace]
  refine ⟨691899579961984126497031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14760524372522328031936661 691899579961984126497031)
  ·
    refine ⟨1037849369942976189745547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 691899579961984126497031 1037849369942976189745547)
    ·
      refine ⟨1556774054914464284618321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1037849369942976189745547 1556774054914464284618321)
      ·
        refine ⟨1167580541185848213463741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1556774054914464284618321 1167580541185848213463741)
        ·
          refine ⟨437842702944693080048903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1167580541185848213463741 437842702944693080048903)
          ·
            refine ⟨656764054417039620073355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437842702944693080048903 656764054417039620073355)
            ·
              refine ⟨985146081625559430110033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656764054417039620073355 985146081625559430110033)
              ·
                refine ⟨738859561219169572582525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985146081625559430110033 738859561219169572582525)
                ·
                  refine ⟨277072335457188589718447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 738859561219169572582525 277072335457188589718447)
                  ·
                    rfl

theorem cell20_607046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_607046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607046 prefixEnd_607046 := by exact prefixLift 607046
  have htrace : WordTrace (prefixWord ++ tailWord_607046) baseStart_607046 baseEnd_607046 := by
    simpa [prefixWord, tailWord_607046, baseEnd_607046] using wordTrace_append hprefix tailTrace_607046
  have hstable : (prefixWord ++ tailWord_607046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607046).length < 2 ^ (prefixWord ++ tailWord_607046).sum := by decide
  have hdescent : baseEnd_607046 < baseStart_607046 := by decide
  rcases family_descends (prefixWord ++ tailWord_607046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607061 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 4]
def baseStart_607061 : Nat := 118140960795 + 607061 * 2 ^ 59
def prefixEnd_607061 : Nat := 4983230072969 + 3 ^ 40 * 607061 * 2
def baseEnd_607061 : Nat := 277079181865915204218385

theorem tailTrace_607061 : CollatzResearch.WordTrace tailWord_607061 prefixEnd_607061 277079181865915204218385 := by
  unfold tailWord_607061
  simp only [CollatzResearch.WordTrace]
  refine ⟨22141333653729149609701037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14760889102486099739800691 22141333653729149609701037)
  ·
    refine ⟨8303000120148431103637889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22141333653729149609701037 8303000120148431103637889)
    ·
      refine ⟨6227250090111323327728417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8303000120148431103637889 6227250090111323327728417)
      ·
        refine ⟨4670437567583492495796313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6227250090111323327728417 4670437567583492495796313)
        ·
          refine ⟨3502828175687619371847235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4670437567583492495796313 3502828175687619371847235)
          ·
            refine ⟨5254242263531429057770853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502828175687619371847235 5254242263531429057770853)
            ·
              refine ⟨985170424412142948332035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5254242263531429057770853 985170424412142948332035)
              ·
                refine ⟨1477755636618214422498053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985170424412142948332035 1477755636618214422498053)
                ·
                  refine ⟨277079181865915204218385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1477755636618214422498053 277079181865915204218385)
                  ·
                    rfl

theorem cell20_607061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_607061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607061 prefixEnd_607061 := by exact prefixLift 607061
  have htrace : WordTrace (prefixWord ++ tailWord_607061) baseStart_607061 baseEnd_607061 := by
    simpa [prefixWord, tailWord_607061, baseEnd_607061] using wordTrace_append hprefix tailTrace_607061
  have hstable : (prefixWord ++ tailWord_607061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607061).length < 2 ^ (prefixWord ++ tailWord_607061).sum := by decide
  have hdescent : baseEnd_607061 < baseStart_607061 := by decide
  rcases family_descends (prefixWord ++ tailWord_607061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607102 : List Nat := [4, 2, 3, 1, 2, 2, 6]
def baseStart_607102 : Nat := 118140960795 + 607102 * 2 ^ 59
def prefixEnd_607102 : Nat := 4983230072969 + 3 ^ 40 * 607102 * 2
def baseEnd_607102 : Nat := 30788655042566809316839

theorem tailTrace_607102 : CollatzResearch.WordTrace tailWord_607102 prefixEnd_607102 30788655042566809316839 := by
  unfold tailWord_607102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2767853630822576701492945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14761886031053742407962373 2767853630822576701492945)
  ·
    refine ⟨2075890223116932526119709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2767853630822576701492945 2075890223116932526119709)
    ·
      refine ⟨778458833668849697294891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2075890223116932526119709 778458833668849697294891)
      ·
        refine ⟨1167688250503274545942337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778458833668849697294891 1167688250503274545942337)
        ·
          refine ⟨875766187877455909456753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1167688250503274545942337 875766187877455909456753)
          ·
            refine ⟨656824640908091932092565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 875766187877455909456753 656824640908091932092565)
            ·
              refine ⟨30788655042566809316839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 656824640908091932092565 30788655042566809316839)
              ·
                rfl

theorem cell20_607102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 6].length) (baseStart_607102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607102 prefixEnd_607102 := by exact prefixLift 607102
  have htrace : WordTrace (prefixWord ++ tailWord_607102) baseStart_607102 baseEnd_607102 := by
    simpa [prefixWord, tailWord_607102, baseEnd_607102] using wordTrace_append hprefix tailTrace_607102
  have hstable : (prefixWord ++ tailWord_607102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607102).length < 2 ^ (prefixWord ++ tailWord_607102).sum := by decide
  have hdescent : baseEnd_607102 < baseStart_607102 := by decide
  rcases family_descends (prefixWord ++ tailWord_607102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607113 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 5]
def baseStart_607113 : Nat := 118140960795 + 607113 * 2 ^ 59
def prefixEnd_607113 : Nat := 4983230072969 + 3 ^ 40 * 607113 * 2
def baseEnd_607113 : Nat := 277102916082834134484839

theorem tailTrace_607113 : CollatzResearch.WordTrace tailWord_607113 prefixEnd_607113 277102916082834134484839 := by
  unfold tailWord_607113
  simp only [CollatzResearch.WordTrace]
  refine ⟨22143230249540762490593993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14762153499693841660395995 22143230249540762490593993)
  ·
    refine ⟨16607422687155571867945495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22143230249540762490593993 16607422687155571867945495)
    ·
      refine ⟨24911134030733357801918243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16607422687155571867945495 24911134030733357801918243)
      ·
        refine ⟨37366701046100036702877365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24911134030733357801918243 37366701046100036702877365)
        ·
          refine ⟨3503128223071878440894753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37366701046100036702877365 3503128223071878440894753)
          ·
            refine ⟨2627346167303908830671065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3503128223071878440894753 2627346167303908830671065)
            ·
              refine ⟨1970509625477931623003299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2627346167303908830671065 1970509625477931623003299)
              ·
                refine ⟨2955764438216897434504949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970509625477931623003299 2955764438216897434504949)
                ·
                  refine ⟨277102916082834134484839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2955764438216897434504949 277102916082834134484839)
                  ·
                    rfl

theorem cell20_607113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_607113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607113 prefixEnd_607113 := by exact prefixLift 607113
  have htrace : WordTrace (prefixWord ++ tailWord_607113) baseStart_607113 baseEnd_607113 := by
    simpa [prefixWord, tailWord_607113, baseEnd_607113] using wordTrace_append hprefix tailTrace_607113
  have hstable : (prefixWord ++ tailWord_607113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607113).length < 2 ^ (prefixWord ++ tailWord_607113).sum := by decide
  have hdescent : baseEnd_607113 < baseStart_607113 := by decide
  rcases family_descends (prefixWord ++ tailWord_607113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607165 : List Nat := [1, 4, 1, 2, 12]
def baseStart_607165 : Nat := 118140960795 + 607165 * 2 ^ 59
def prefixEnd_607165 : Nat := 4983230072969 + 3 ^ 40 * 607165 * 2
def baseEnd_607165 : Nat := 3421316670367321787053

theorem tailTrace_607165 : CollatzResearch.WordTrace tailWord_607165 prefixEnd_607165 3421316670367321787053 := by
  unfold tailWord_607165
  simp only [CollatzResearch.WordTrace]
  refine ⟨22145126845352375371486949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14763417896901583580991299 22145126845352375371486949)
  ·
    refine ⟨4152211283503570382153803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22145126845352375371486949 4152211283503570382153803)
    ·
      refine ⟨6228316925255355573230705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4152211283503570382153803 6228316925255355573230705)
      ·
        refine ⟨4671237693941516679923029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6228316925255355573230705 4671237693941516679923029)
        ·
          refine ⟨3421316670367321787053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4671237693941516679923029 3421316670367321787053)
          ·
            rfl

theorem cell20_607165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 12].length) (baseStart_607165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607165 prefixEnd_607165 := by exact prefixLift 607165
  have htrace : WordTrace (prefixWord ++ tailWord_607165) baseStart_607165 baseEnd_607165 := by
    simpa [prefixWord, tailWord_607165, baseEnd_607165] using wordTrace_append hprefix tailTrace_607165
  have hstable : (prefixWord ++ tailWord_607165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607165).length < 2 ^ (prefixWord ++ tailWord_607165).sum := by decide
  have hdescent : baseEnd_607165 < baseStart_607165 := by decide
  rcases family_descends (prefixWord ++ tailWord_607165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607168 : List Nat := [2, 1, 1, 2, 3, 4, 2, 2, 3]
def baseStart_607168 : Nat := 118140960795 + 607168 * 2 ^ 59
def prefixEnd_607168 : Nat := 4983230072969 + 3 ^ 40 * 607168 * 2
def baseEnd_607168 : Nat := 277128019581498387651281

theorem tailTrace_607168 : CollatzResearch.WordTrace tailWord_607168 prefixEnd_607168 277128019581498387651281 := by
  unfold tailWord_607168
  simp only [CollatzResearch.WordTrace]
  refine ⟨11072618132170753441923079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14763490842894337922564105 11072618132170753441923079)
  ·
    refine ⟨16608927198256130162884619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11072618132170753441923079 16608927198256130162884619)
    ·
      refine ⟨24913390797384195244326929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16608927198256130162884619 24913390797384195244326929)
      ·
        refine ⟨18685043098038146433245197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24913390797384195244326929 18685043098038146433245197)
        ·
          refine ⟨7006891161764304912466949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18685043098038146433245197 7006891161764304912466949)
          ·
            refine ⟨1313792092830807171087553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7006891161764304912466949 1313792092830807171087553)
            ·
              refine ⟨985344069623105378315665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1313792092830807171087553 985344069623105378315665)
              ·
                refine ⟨739008052217329033736749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985344069623105378315665 739008052217329033736749)
                ·
                  refine ⟨277128019581498387651281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 739008052217329033736749 277128019581498387651281)
                  ·
                    rfl

theorem cell20_607168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_607168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607168 prefixEnd_607168 := by exact prefixLift 607168
  have htrace : WordTrace (prefixWord ++ tailWord_607168) baseStart_607168 baseEnd_607168 := by
    simpa [prefixWord, tailWord_607168, baseEnd_607168] using wordTrace_append hprefix tailTrace_607168
  have hstable : (prefixWord ++ tailWord_607168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607168).length < 2 ^ (prefixWord ++ tailWord_607168).sum := by decide
  have hdescent : baseEnd_607168 < baseStart_607168 := by decide
  rcases family_descends (prefixWord ++ tailWord_607168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607182 : List Nat := [4, 1, 1, 1, 2, 3, 3, 5]
def baseStart_607182 : Nat := 118140960795 + 607182 * 2 ^ 59
def prefixEnd_607182 : Nat := 4983230072969 + 3 ^ 40 * 607182 * 2
def baseEnd_607182 : Nat := 92378136520992187061519

theorem tailTrace_607182 : CollatzResearch.WordTrace tailWord_607182 prefixEnd_607182 92378136520992187061519 := by
  unfold tailWord_607182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2768218360786348409356975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14763831257527191516570533 2768218360786348409356975)
  ·
    refine ⟨4152327541179522614035463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2768218360786348409356975 4152327541179522614035463)
    ·
      refine ⟨6228491311769283921053195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4152327541179522614035463 6228491311769283921053195)
      ·
        refine ⟨9342736967653925881579793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6228491311769283921053195 9342736967653925881579793)
        ·
          refine ⟨7007052725740444411184845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9342736967653925881579793 7007052725740444411184845)
          ·
            refine ⟨2627644772152666654194317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7007052725740444411184845 2627644772152666654194317)
            ·
              refine ⟨985366789557249995322869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2627644772152666654194317 985366789557249995322869)
              ·
                refine ⟨92378136520992187061519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 985366789557249995322869 92378136520992187061519)
                ·
                  rfl

theorem cell20_607182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_607182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607182 prefixEnd_607182 := by exact prefixLift 607182
  have htrace : WordTrace (prefixWord ++ tailWord_607182) baseStart_607182 baseEnd_607182 := by
    simpa [prefixWord, tailWord_607182, baseEnd_607182] using wordTrace_append hprefix tailTrace_607182
  have hstable : (prefixWord ++ tailWord_607182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607182).length < 2 ^ (prefixWord ++ tailWord_607182).sum := by decide
  have hdescent : baseEnd_607182 < baseStart_607182 := by decide
  rcases family_descends (prefixWord ++ tailWord_607182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607199 : List Nat := [1, 1, 2, 3, 5, 1, 3, 4]
def baseStart_607199 : Nat := 118140960795 + 607199 * 2 ^ 59
def prefixEnd_607199 : Nat := 4983230072969 + 3 ^ 40 * 607199 * 2
def baseEnd_607199 : Nat := 92380722942066685872607

theorem tailTrace_607199 : CollatzResearch.WordTrace tailWord_607199 prefixEnd_607199 92380722942066685872607 := by
  unfold tailWord_607199
  simp only [CollatzResearch.WordTrace]
  refine ⟨22146366927229199178224651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14764244618152799452149767 22146366927229199178224651)
  ·
    refine ⟨33219550390843798767336977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22146366927229199178224651 33219550390843798767336977)
    ·
      refine ⟨24914662793132849075502733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33219550390843798767336977 24914662793132849075502733)
      ·
        refine ⟨9342998547424818403313525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24914662793132849075502733 9342998547424818403313525)
        ·
          refine ⟨875906113821076725310643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9342998547424818403313525 875906113821076725310643)
          ·
            refine ⟨1313859170731615087965965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875906113821076725310643 1313859170731615087965965)
            ·
              refine ⟨492697189024355657987237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1313859170731615087965965 492697189024355657987237)
              ·
                refine ⟨92380722942066685872607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 492697189024355657987237 92380722942066685872607)
                ·
                  rfl

theorem cell20_607199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 4].length) (baseStart_607199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607199 prefixEnd_607199 := by exact prefixLift 607199
  have htrace : WordTrace (prefixWord ++ tailWord_607199) baseStart_607199 baseEnd_607199 := by
    simpa [prefixWord, tailWord_607199, baseEnd_607199] using wordTrace_append hprefix tailTrace_607199
  have hstable : (prefixWord ++ tailWord_607199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607199).length < 2 ^ (prefixWord ++ tailWord_607199).sum := by decide
  have hdescent : baseEnd_607199 < baseStart_607199 := by decide
  rcases family_descends (prefixWord ++ tailWord_607199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607248 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_607248 : Nat := 118140960795 + 607248 * 2 ^ 59
def prefixEnd_607248 : Nat := 4983230072969 + 3 ^ 40 * 607248 * 2
def baseEnd_607248 : Nat := 277164533761373664984287

theorem tailTrace_607248 : CollatzResearch.WordTrace tailWord_607248 prefixEnd_607248 277164533761373664984287 := by
  unfold tailWord_607248
  simp only [CollatzResearch.WordTrace]
  refine ⟨11074077052025840273379199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14765436069367787031172265 11074077052025840273379199)
  ·
    refine ⟨16611115578038760410068799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11074077052025840273379199 16611115578038760410068799)
    ·
      refine ⟨24916673367058140615103199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16611115578038760410068799 24916673367058140615103199)
      ·
        refine ⟨37375010050587210922654799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24916673367058140615103199 37375010050587210922654799)
        ·
          refine ⟨56062515075880816383982199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37375010050587210922654799 56062515075880816383982199)
          ·
            refine ⟨84093772613821224575973299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56062515075880816383982199 84093772613821224575973299)
            ·
              refine ⟨126140658920731836863959949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84093772613821224575973299 126140658920731836863959949)
              ·
                refine ⟨47302747095274438823984981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126140658920731836863959949 47302747095274438823984981)
                ·
                  refine ⟨277164533761373664984287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47302747095274438823984981 277164533761373664984287)
                  ·
                    rfl

theorem cell20_607248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_607248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607248 prefixEnd_607248 := by exact prefixLift 607248
  have htrace : WordTrace (prefixWord ++ tailWord_607248) baseStart_607248 baseEnd_607248 := by
    simpa [prefixWord, tailWord_607248, baseEnd_607248] using wordTrace_append hprefix tailTrace_607248
  have hstable : (prefixWord ++ tailWord_607248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607248).length < 2 ^ (prefixWord ++ tailWord_607248).sum := by decide
  have hdescent : baseEnd_607248 < baseStart_607248 := by decide
  rcases family_descends (prefixWord ++ tailWord_607248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607250 : List Nat := [3, 2, 5, 1, 1, 2, 2, 4]
def baseStart_607250 : Nat := 118140960795 + 607250 * 2 ^ 59
def prefixEnd_607250 : Nat := 4983230072969 + 3 ^ 40 * 607250 * 2
def baseEnd_607250 : Nat := 92388482205290182305871

theorem tailTrace_607250 : CollatzResearch.WordTrace tailWord_607250 prefixEnd_607250 92388482205290182305871 := by
  unfold tailWord_607250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5537056762511108722082801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14765484700029623258887469 5537056762511108722082801)
  ·
    refine ⟨4152792571883331541562101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5537056762511108722082801 4152792571883331541562101)
    ·
      refine ⟨389324303614062332021447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4152792571883331541562101 389324303614062332021447)
      ·
        refine ⟨583986455421093498032171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389324303614062332021447 583986455421093498032171)
        ·
          refine ⟨875979683131640247048257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583986455421093498032171 875979683131640247048257)
          ·
            refine ⟨656984762348730185286193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 875979683131640247048257 656984762348730185286193)
            ·
              refine ⟨492738571761547638964645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 656984762348730185286193 492738571761547638964645)
              ·
                refine ⟨92388482205290182305871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 492738571761547638964645 92388482205290182305871)
                ·
                  rfl

theorem cell20_607250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_607250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607250 prefixEnd_607250 := by exact prefixLift 607250
  have htrace : WordTrace (prefixWord ++ tailWord_607250) baseStart_607250 baseEnd_607250 := by
    simpa [prefixWord, tailWord_607250, baseEnd_607250] using wordTrace_append hprefix tailTrace_607250
  have hstable : (prefixWord ++ tailWord_607250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607250).length < 2 ^ (prefixWord ++ tailWord_607250).sum := by decide
  have hdescent : baseEnd_607250 < baseStart_607250 := by decide
  rcases family_descends (prefixWord ++ tailWord_607250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607264 : List Nat := [2, 1, 1, 7, 1, 2, 1, 3, 2]
def baseStart_607264 : Nat := 118140960795 + 607264 * 2 ^ 59
def prefixEnd_607264 : Nat := 4983230072969 + 3 ^ 40 * 607264 * 2
def baseEnd_607264 : Nat := 277171836597348720450889

theorem tailTrace_607264 : CollatzResearch.WordTrace tailWord_607264 prefixEnd_607264 277171836597348720450889 := by
  unfold tailWord_607264
  simp only [CollatzResearch.WordTrace]
  refine ⟨11074368835996857639670423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14765825114662476852893897 11074368835996857639670423)
  ·
    refine ⟨16611553253995286459505635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11074368835996857639670423 16611553253995286459505635)
    ·
      refine ⟨24917329880992929689258453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16611553253995286459505635 24917329880992929689258453)
      ·
        refine ⟨583999919085771789591995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 24917329880992929689258453 583999919085771789591995)
        ·
          refine ⟨875999878628657684387993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583999919085771789591995 875999878628657684387993)
          ·
            refine ⟨656999908971493263290995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 875999878628657684387993 656999908971493263290995)
            ·
              refine ⟨985499863457239894936493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656999908971493263290995 985499863457239894936493)
              ·
                refine ⟨369562448796464960601185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 985499863457239894936493 369562448796464960601185)
                ·
                  refine ⟨277171836597348720450889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 369562448796464960601185 277171836597348720450889)
                  ·
                    rfl

theorem cell20_607264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 2].length) (baseStart_607264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607264 prefixEnd_607264 := by exact prefixLift 607264
  have htrace : WordTrace (prefixWord ++ tailWord_607264) baseStart_607264 baseEnd_607264 := by
    simpa [prefixWord, tailWord_607264, baseEnd_607264] using wordTrace_append hprefix tailTrace_607264
  have hstable : (prefixWord ++ tailWord_607264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607264).length < 2 ^ (prefixWord ++ tailWord_607264).sum := by decide
  have hdescent : baseEnd_607264 < baseStart_607264 := by decide
  rcases family_descends (prefixWord ++ tailWord_607264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607265 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 5]
def baseStart_607265 : Nat := 118140960795 + 607265 * 2 ^ 59
def prefixEnd_607265 : Nat := 4983230072969 + 3 ^ 40 * 607265 * 2
def baseEnd_607265 : Nat := 277172293024597161417551

theorem tailTrace_607265 : CollatzResearch.WordTrace tailWord_607265 prefixEnd_607265 277172293024597161417551 := by
  unfold tailWord_607265
  simp only [CollatzResearch.WordTrace]
  refine ⟨22148774144990092450127249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14765849429993394966751499 22148774144990092450127249)
  ·
    refine ⟨16611580608742569337595437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22148774144990092450127249 16611580608742569337595437)
    ·
      refine ⟨6229342728278463501598289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16611580608742569337595437 6229342728278463501598289)
      ·
        refine ⟨4672007046208847626198717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6229342728278463501598289 4672007046208847626198717)
        ·
          refine ⟨1752002642328317859824519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4672007046208847626198717 1752002642328317859824519)
          ·
            refine ⟨2628003963492476789736779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752002642328317859824519 2628003963492476789736779)
            ·
              refine ⟨3942005945238715184605169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2628003963492476789736779 3942005945238715184605169)
              ·
                refine ⟨2956504458929036388453877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3942005945238715184605169 2956504458929036388453877)
                ·
                  refine ⟨277172293024597161417551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2956504458929036388453877 277172293024597161417551)
                  ·
                    rfl

theorem cell20_607265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_607265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607265 prefixEnd_607265 := by exact prefixLift 607265
  have htrace : WordTrace (prefixWord ++ tailWord_607265) baseStart_607265 baseEnd_607265 := by
    simpa [prefixWord, tailWord_607265, baseEnd_607265] using wordTrace_append hprefix tailTrace_607265
  have hstable : (prefixWord ++ tailWord_607265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607265).length < 2 ^ (prefixWord ++ tailWord_607265).sum := by decide
  have hdescent : baseEnd_607265 < baseStart_607265 := by decide
  rcases family_descends (prefixWord ++ tailWord_607265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607289 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 4]
def baseStart_607289 : Nat := 118140960795 + 607289 * 2 ^ 59
def prefixEnd_607289 : Nat := 4983230072969 + 3 ^ 40 * 607289 * 2
def baseEnd_607289 : Nat := 277183247278559744617453

theorem tailTrace_607289 : CollatzResearch.WordTrace tailWord_607289 prefixEnd_607289 277183247278559744617453 := by
  unfold tailWord_607289
  simp only [CollatzResearch.WordTrace]
  refine ⟨22149649496903144549000921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14766432997935429699333947 22149649496903144549000921)
  ·
    refine ⟨16612237122677358411750691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22149649496903144549000921 16612237122677358411750691)
    ·
      refine ⟨24918355684016037617626037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16612237122677358411750691 24918355684016037617626037)
      ·
        refine ⟨2336095845376503526652441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24918355684016037617626037 2336095845376503526652441)
        ·
          refine ⟨1752071884032377644989331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2336095845376503526652441 1752071884032377644989331)
          ·
            refine ⟨2628107826048566467483997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752071884032377644989331 2628107826048566467483997)
            ·
              refine ⟨985540434768212425306499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2628107826048566467483997 985540434768212425306499)
              ·
                refine ⟨1478310652152318637959749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985540434768212425306499 1478310652152318637959749)
                ·
                  refine ⟨277183247278559744617453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1478310652152318637959749 277183247278559744617453)
                  ·
                    rfl

theorem cell20_607289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_607289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607289 prefixEnd_607289 := by exact prefixLift 607289
  have htrace : WordTrace (prefixWord ++ tailWord_607289) baseStart_607289 baseEnd_607289 := by
    simpa [prefixWord, tailWord_607289, baseEnd_607289] using wordTrace_append hprefix tailTrace_607289
  have hstable : (prefixWord ++ tailWord_607289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607289).length < 2 ^ (prefixWord ++ tailWord_607289).sum := by decide
  have hdescent : baseEnd_607289 < baseStart_607289 := by decide
  rcases family_descends (prefixWord ++ tailWord_607289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607310 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_607310 : Nat := 118140960795 + 607310 * 2 ^ 59
def prefixEnd_607310 : Nat := 4983230072969 + 3 ^ 40 * 607310 * 2
def baseEnd_607310 : Nat := 277192832250777004917367

theorem tailTrace_607310 : CollatzResearch.WordTrace tailWord_607310 prefixEnd_607310 277192832250777004917367 := by
  unfold tailWord_607310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2768801928728383141939423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14766943619884710090343589 2768801928728383141939423)
  ·
    refine ⟨4153202893092574712909135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2768801928728383141939423 4153202893092574712909135)
    ·
      refine ⟨6229804339638862069363703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4153202893092574712909135 6229804339638862069363703)
      ·
        refine ⟨9344706509458293104045555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6229804339638862069363703 9344706509458293104045555)
        ·
          refine ⟨14017059764187439656068333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9344706509458293104045555 14017059764187439656068333)
          ·
            refine ⟨5256397411570289871025625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14017059764187439656068333 5256397411570289871025625)
            ·
              refine ⟨3942298058677717403269219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5256397411570289871025625 3942298058677717403269219)
              ·
                refine ⟨5913447088016576104903829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3942298058677717403269219 5913447088016576104903829)
                ·
                  refine ⟨277192832250777004917367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5913447088016576104903829 277192832250777004917367)
                  ·
                    rfl

theorem cell20_607310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_607310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607310 prefixEnd_607310 := by exact prefixLift 607310
  have htrace : WordTrace (prefixWord ++ tailWord_607310) baseStart_607310 baseEnd_607310 := by
    simpa [prefixWord, tailWord_607310, baseEnd_607310] using wordTrace_append hprefix tailTrace_607310
  have hstable : (prefixWord ++ tailWord_607310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607310).length < 2 ^ (prefixWord ++ tailWord_607310).sum := by decide
  have hdescent : baseEnd_607310 < baseStart_607310 := by decide
  rcases family_descends (prefixWord ++ tailWord_607310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607317 : List Nat := [1, 3, 2, 2, 1, 2, 1, 8]
def baseStart_607317 : Nat := 118140960795 + 607317 * 2 ^ 59
def prefixEnd_607317 : Nat := 4983230072969 + 3 ^ 40 * 607317 * 2
def baseEnd_607317 : Nat := 92398675747172030561335

theorem tailTrace_607317 : CollatzResearch.WordTrace tailWord_607317 prefixEnd_607317 92398675747172030561335 := by
  unfold tailWord_607317
  simp only [CollatzResearch.WordTrace]
  refine ⟨22150670740801705331020205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14767113827201136887346803 22150670740801705331020205)
  ·
    refine ⟨8306501527800639499132577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22150670740801705331020205 8306501527800639499132577)
    ·
      refine ⟨6229876145850479624349433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8306501527800639499132577 6229876145850479624349433)
      ·
        refine ⟨4672407109387859718262075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6229876145850479624349433 4672407109387859718262075)
        ·
          refine ⟨7008610664081789577393113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4672407109387859718262075 7008610664081789577393113)
          ·
            refine ⟨5256457998061342183044835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7008610664081789577393113 5256457998061342183044835)
            ·
              refine ⟨7884686997092013274567253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5256457998061342183044835 7884686997092013274567253)
              ·
                refine ⟨92398675747172030561335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7884686997092013274567253 92398675747172030561335)
                ·
                  rfl

theorem cell20_607317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_607317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607317 prefixEnd_607317 := by exact prefixLift 607317
  have htrace : WordTrace (prefixWord ++ tailWord_607317) baseStart_607317 baseEnd_607317 := by
    simpa [prefixWord, tailWord_607317, baseEnd_607317] using wordTrace_append hprefix tailTrace_607317
  have hstable : (prefixWord ++ tailWord_607317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607317).length < 2 ^ (prefixWord ++ tailWord_607317).sum := by decide
  have hdescent : baseEnd_607317 < baseStart_607317 := by decide
  rcases family_descends (prefixWord ++ tailWord_607317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607327 : List Nat := [1, 1, 2, 3, 1, 1, 4, 5, 2]
def baseStart_607327 : Nat := 118140960795 + 607327 * 2 ^ 59
def prefixEnd_607327 : Nat := 4983230072969 + 3 ^ 40 * 607327 * 2
def baseEnd_607327 : Nat := 277200591514000501350631

theorem tailTrace_607327 : CollatzResearch.WordTrace tailWord_607327 prefixEnd_607327 277200591514000501350631 := by
  unfold tailWord_607327
  simp only [CollatzResearch.WordTrace]
  refine ⟨22151035470765477038884235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14767356980510318025922823 22151035470765477038884235)
  ·
    refine ⟨33226553206148215558326353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22151035470765477038884235 33226553206148215558326353)
    ·
      refine ⟨24919914904611161668744765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33226553206148215558326353 24919914904611161668744765)
      ·
        refine ⟨9344968089229185625779287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24919914904611161668744765 9344968089229185625779287)
        ·
          refine ⟨14017452133843778438668931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9344968089229185625779287 14017452133843778438668931)
          ·
            refine ⟨21026178200765667658003397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14017452133843778438668931 21026178200765667658003397)
            ·
              refine ⟨3942408412643562685875637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21026178200765667658003397 3942408412643562685875637)
              ·
                refine ⟨369600788685334001800841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3942408412643562685875637 369600788685334001800841)
                ·
                  refine ⟨277200591514000501350631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 369600788685334001800841 277200591514000501350631)
                  ·
                    rfl

theorem cell20_607327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 2].length) (baseStart_607327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607327 prefixEnd_607327 := by exact prefixLift 607327
  have htrace : WordTrace (prefixWord ++ tailWord_607327) baseStart_607327 baseEnd_607327 := by
    simpa [prefixWord, tailWord_607327, baseEnd_607327] using wordTrace_append hprefix tailTrace_607327
  have hstable : (prefixWord ++ tailWord_607327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607327).length < 2 ^ (prefixWord ++ tailWord_607327).sum := by decide
  have hdescent : baseEnd_607327 < baseStart_607327 := by decide
  rcases family_descends (prefixWord ++ tailWord_607327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607365 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 4]
def baseStart_607365 : Nat := 118140960795 + 607365 * 2 ^ 59
def prefixEnd_607365 : Nat := 4983230072969 + 3 ^ 40 * 607365 * 2
def baseEnd_607365 : Nat := 277217935749441258083809

theorem tailTrace_607365 : CollatzResearch.WordTrace tailWord_607365 prefixEnd_607365 277217935749441258083809 := by
  unfold tailWord_607365
  simp only [CollatzResearch.WordTrace]
  refine ⟨22152421444627809528767549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14768280963085206352511699 22152421444627809528767549)
  ·
    refine ⟨8307158041735428573287831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22152421444627809528767549 8307158041735428573287831)
    ·
      refine ⟨12460737062603142859931747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8307158041735428573287831 12460737062603142859931747)
      ·
        refine ⟨18691105593904714289897621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12460737062603142859931747 18691105593904714289897621)
        ·
          refine ⟨876145574714283482338951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18691105593904714289897621 876145574714283482338951)
          ·
            refine ⟨1314218362071425223508427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876145574714283482338951 1314218362071425223508427)
            ·
              refine ⟨1971327543107137835262641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314218362071425223508427 1971327543107137835262641)
              ·
                refine ⟨1478495657330353376446981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1971327543107137835262641 1478495657330353376446981)
                ·
                  refine ⟨277217935749441258083809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1478495657330353376446981 277217935749441258083809)
                  ·
                    rfl

theorem cell20_607365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_607365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607365 prefixEnd_607365 := by exact prefixLift 607365
  have htrace : WordTrace (prefixWord ++ tailWord_607365) baseStart_607365 baseEnd_607365 := by
    simpa [prefixWord, tailWord_607365, baseEnd_607365] using wordTrace_append hprefix tailTrace_607365
  have hstable : (prefixWord ++ tailWord_607365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607365).length < 2 ^ (prefixWord ++ tailWord_607365).sum := by decide
  have hdescent : baseEnd_607365 < baseStart_607365 := by decide
  rcases family_descends (prefixWord ++ tailWord_607365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607393 : List Nat := [1, 2, 3, 3, 1, 1, 9]
def baseStart_607393 : Nat := 118140960795 + 607393 * 2 ^ 59
def prefixEnd_607393 : Nat := 4983230072969 + 3 ^ 40 * 607393 * 2
def baseEnd_607393 : Nat := 30803412856933067238929

theorem tailTrace_607393 : CollatzResearch.WordTrace tailWord_607393 prefixEnd_607393 30803412856933067238929 := by
  unfold tailWord_607393
  simp only [CollatzResearch.WordTrace]
  refine ⟨22153442688526370310786833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14768961792350913540524555 22153442688526370310786833)
  ·
    refine ⟨16615082016394777733090125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22153442688526370310786833 16615082016394777733090125)
    ·
      refine ⟨6230655756148041649908797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16615082016394777733090125 6230655756148041649908797)
      ·
        refine ⟨2336495908555515618715799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6230655756148041649908797 2336495908555515618715799)
        ·
          refine ⟨3504743862833273428073699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2336495908555515618715799 3504743862833273428073699)
          ·
            refine ⟨5257115794249910142110549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3504743862833273428073699 5257115794249910142110549)
            ·
              refine ⟨30803412856933067238929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5257115794249910142110549 30803412856933067238929)
              ·
                rfl

theorem cell20_607393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 9].length) (baseStart_607393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607393 prefixEnd_607393 := by exact prefixLift 607393
  have htrace : WordTrace (prefixWord ++ tailWord_607393) baseStart_607393 baseEnd_607393 := by
    simpa [prefixWord, tailWord_607393, baseEnd_607393] using wordTrace_append hprefix tailTrace_607393
  have hstable : (prefixWord ++ tailWord_607393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607393).length < 2 ^ (prefixWord ++ tailWord_607393).sum := by decide
  have hdescent : baseEnd_607393 < baseStart_607393 := by decide
  rcases family_descends (prefixWord ++ tailWord_607393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607396 : List Nat := [2, 3, 1, 2, 3, 1, 3, 2, 3]
def baseStart_607396 : Nat := 118140960795 + 607396 * 2 ^ 59
def prefixEnd_607396 : Nat := 4983230072969 + 3 ^ 40 * 607396 * 2
def baseEnd_607396 : Nat := 277232084994142928050349

theorem tailTrace_607396 : CollatzResearch.WordTrace tailWord_607396 prefixEnd_607396 277232084994142928050349 := by
  unfold tailWord_607396
  simp only [CollatzResearch.WordTrace]
  refine ⟨11076776053757750911573021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14769034738343667882097361 11076776053757750911573021)
  ·
    refine ⟨4153791020159156591839883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11076776053757750911573021 4153791020159156591839883)
    ·
      refine ⟨6230686530238734887759825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4153791020159156591839883 6230686530238734887759825)
      ·
        refine ⟨4673014897679051165819869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6230686530238734887759825 4673014897679051165819869)
        ·
          refine ⟨1752380586629644187182451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4673014897679051165819869 1752380586629644187182451)
          ·
            refine ⟨2628570879944466280773677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752380586629644187182451 2628570879944466280773677)
            ·
              refine ⟨985714079979174855290129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2628570879944466280773677 985714079979174855290129)
              ·
                refine ⟨739285559984381141467597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985714079979174855290129 739285559984381141467597)
                ·
                  refine ⟨277232084994142928050349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 739285559984381141467597 277232084994142928050349)
                  ·
                    rfl

theorem cell20_607396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_607396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607396 prefixEnd_607396 := by exact prefixLift 607396
  have htrace : WordTrace (prefixWord ++ tailWord_607396) baseStart_607396 baseEnd_607396 := by
    simpa [prefixWord, tailWord_607396, baseEnd_607396] using wordTrace_append hprefix tailTrace_607396
  have hstable : (prefixWord ++ tailWord_607396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607396).length < 2 ^ (prefixWord ++ tailWord_607396).sum := by decide
  have hdescent : baseEnd_607396 < baseStart_607396 := by decide
  rcases family_descends (prefixWord ++ tailWord_607396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607444 : List Nat := [2, 4, 1, 4, 2, 1, 6]
def baseStart_607444 : Nat := 118140960795 + 607444 * 2 ^ 59
def prefixEnd_607444 : Nat := 4983230072969 + 3 ^ 40 * 607444 * 2
def baseEnd_607444 : Nat := 30805999278007566050017

theorem tailTrace_607444 : CollatzResearch.WordTrace tailWord_607444 prefixEnd_607444 30805999278007566050017 := by
  unfold tailWord_607444
  simp only [CollatzResearch.WordTrace]
  refine ⟨11077651405670803010446693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14770201874227737347262257 11077651405670803010446693)
  ·
    refine ⟨2077059638563275564458755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11077651405670803010446693 2077059638563275564458755)
    ·
      refine ⟨3115589457844913346688133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2077059638563275564458755 3115589457844913346688133)
      ·
        refine ⟨584173023345921252504025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3115589457844913346688133 584173023345921252504025)
        ·
          refine ⟨438129767509440939378019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 584173023345921252504025 438129767509440939378019)
          ·
            refine ⟨657194651264161409067029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438129767509440939378019 657194651264161409067029)
            ·
              refine ⟨30805999278007566050017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 657194651264161409067029 30805999278007566050017)
              ·
                rfl

theorem cell20_607444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 6].length) (baseStart_607444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607444 prefixEnd_607444 := by exact prefixLift 607444
  have htrace : WordTrace (prefixWord ++ tailWord_607444) baseStart_607444 baseEnd_607444 := by
    simpa [prefixWord, tailWord_607444, baseEnd_607444] using wordTrace_append hprefix tailTrace_607444
  have hstable : (prefixWord ++ tailWord_607444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607444).length < 2 ^ (prefixWord ++ tailWord_607444).sum := by decide
  have hdescent : baseEnd_607444 < baseStart_607444 := by decide
  rcases family_descends (prefixWord ++ tailWord_607444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607448 : List Nat := [2, 1, 2, 2, 5, 2, 6]
def baseStart_607448 : Nat := 118140960795 + 607448 * 2 ^ 59
def prefixEnd_607448 : Nat := 4983230072969 + 3 ^ 40 * 607448 * 2
def baseEnd_607448 : Nat := 30806202134562428701867

theorem tailTrace_607448 : CollatzResearch.WordTrace tailWord_607448 prefixEnd_607448 30806202134562428701867 := by
  unfold tailWord_607448
  simp only [CollatzResearch.WordTrace]
  refine ⟨11077724351663557352019499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14770299135551409802692665 11077724351663557352019499)
  ·
    refine ⟨16616586527495336028029249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11077724351663557352019499 16616586527495336028029249)
    ·
      refine ⟨12462439895621502021021937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16616586527495336028029249 12462439895621502021021937)
      ·
        refine ⟨9346829921716126515766453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12462439895621502021021937 9346829921716126515766453)
        ·
          refine ⟨876265305160886860853105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9346829921716126515766453 876265305160886860853105)
          ·
            refine ⟨657198978870665145639829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 876265305160886860853105 657198978870665145639829)
            ·
              refine ⟨30806202134562428701867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 657198978870665145639829 30806202134562428701867)
              ·
                rfl

theorem cell20_607448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 6].length) (baseStart_607448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607448 prefixEnd_607448 := by exact prefixLift 607448
  have htrace : WordTrace (prefixWord ++ tailWord_607448) baseStart_607448 baseEnd_607448 := by
    simpa [prefixWord, tailWord_607448, baseEnd_607448] using wordTrace_append hprefix tailTrace_607448
  have hstable : (prefixWord ++ tailWord_607448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607448).length < 2 ^ (prefixWord ++ tailWord_607448).sum := by decide
  have hdescent : baseEnd_607448 < baseStart_607448 := by decide
  rcases family_descends (prefixWord ++ tailWord_607448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607486 : List Nat := [4, 2, 2, 1, 1, 2, 2, 6]
def baseStart_607486 : Nat := 118140960795 + 607486 * 2 ^ 59
def prefixEnd_607486 : Nat := 4983230072969 + 3 ^ 40 * 607486 * 2
def baseEnd_607486 : Nat := 92424387815500871683327

theorem tailTrace_607486 : CollatzResearch.WordTrace tailWord_607486 prefixEnd_607486 92424387815500871683327 := by
  unfold tailWord_607486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2769604334648680899240289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14771223118126298129281541 2769604334648680899240289)
  ·
    refine ⟨2077203250986510674430217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2769604334648680899240289 2077203250986510674430217)
    ·
      refine ⟨1557902438239883005822663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2077203250986510674430217 1557902438239883005822663)
      ·
        refine ⟨2336853657359824508733995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1557902438239883005822663 2336853657359824508733995)
        ·
          refine ⟨3505280486039736763100993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2336853657359824508733995 3505280486039736763100993)
          ·
            refine ⟨2628960364529802572325745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3505280486039736763100993 2628960364529802572325745)
            ·
              refine ⟨1971720273397351929244309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2628960364529802572325745 1971720273397351929244309)
              ·
                refine ⟨92424387815500871683327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1971720273397351929244309 92424387815500871683327)
                ·
                  rfl

theorem cell20_607486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_607486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607486 prefixEnd_607486 := by exact prefixLift 607486
  have htrace : WordTrace (prefixWord ++ tailWord_607486) baseStart_607486 baseEnd_607486 := by
    simpa [prefixWord, tailWord_607486, baseEnd_607486] using wordTrace_append hprefix tailTrace_607486
  have hstable : (prefixWord ++ tailWord_607486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607486).length < 2 ^ (prefixWord ++ tailWord_607486).sum := by decide
  have hdescent : baseEnd_607486 < baseStart_607486 := by decide
  rcases family_descends (prefixWord ++ tailWord_607486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607506 : List Nat := [3, 2, 4, 2, 1, 1, 2, 2, 3]
def baseStart_607506 : Nat := 118140960795 + 607506 * 2 ^ 59
def prefixEnd_607506 : Nat := 4983230072969 + 3 ^ 40 * 607506 * 2
def baseEnd_607506 : Nat := 277282291991471434383233

theorem tailTrace_607506 : CollatzResearch.WordTrace tailWord_607506 prefixEnd_607506 277282291991471434383233 := by
  unfold tailWord_607506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5539391034279247652412593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14771709424744660406433581 5539391034279247652412593)
  ·
    refine ⟨4154543275709435739309445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5539391034279247652412593 4154543275709435739309445)
    ·
      refine ⟨778976864195519201120521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4154543275709435739309445 778976864195519201120521)
      ·
        refine ⟨584232648146639400840391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 778976864195519201120521 584232648146639400840391)
        ·
          refine ⟨876348972219959101260587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584232648146639400840391 876348972219959101260587)
          ·
            refine ⟨1314523458329938651890881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876348972219959101260587 1314523458329938651890881)
            ·
              refine ⟨985892593747453988918161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1314523458329938651890881 985892593747453988918161)
              ·
                refine ⟨739419445310590491688621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985892593747453988918161 739419445310590491688621)
                ·
                  refine ⟨277282291991471434383233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 739419445310590491688621 277282291991471434383233)
                  ·
                    rfl

theorem cell20_607506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_607506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607506 prefixEnd_607506 := by exact prefixLift 607506
  have htrace : WordTrace (prefixWord ++ tailWord_607506) baseStart_607506 baseEnd_607506 := by
    simpa [prefixWord, tailWord_607506, baseEnd_607506] using wordTrace_append hprefix tailTrace_607506
  have hstable : (prefixWord ++ tailWord_607506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607506).length < 2 ^ (prefixWord ++ tailWord_607506).sum := by decide
  have hdescent : baseEnd_607506 < baseStart_607506 := by decide
  rcases family_descends (prefixWord ++ tailWord_607506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607538 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_607538 : Nat := 118140960795 + 607538 * 2 ^ 59
def prefixEnd_607538 : Nat := 4983230072969 + 3 ^ 40 * 607538 * 2
def baseEnd_607538 : Nat := 277296897663421545316435

theorem tailTrace_607538 : CollatzResearch.WordTrace tailWord_607538 prefixEnd_607538 277296897663421545316435 := by
  unfold tailWord_607538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5539682818250265018703817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14772487515334040049876845 5539682818250265018703817)
  ·
    refine ⟨4154762113687698764027863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5539682818250265018703817 4154762113687698764027863)
    ·
      refine ⟨6232143170531548146041795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4154762113687698764027863 6232143170531548146041795)
      ·
        refine ⟨9348214755797322219062693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6232143170531548146041795 9348214755797322219062693)
        ·
          refine ⟨1752790266711997916074255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9348214755797322219062693 1752790266711997916074255)
          ·
            refine ⟨2629185400067996874111383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752790266711997916074255 2629185400067996874111383)
            ·
              refine ⟨3943778100101995311167075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2629185400067996874111383 3943778100101995311167075)
              ·
                refine ⟨5915667150152992966750613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3943778100101995311167075 5915667150152992966750613)
                ·
                  refine ⟨277296897663421545316435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5915667150152992966750613 277296897663421545316435)
                  ·
                    rfl

theorem cell20_607538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_607538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607538 prefixEnd_607538 := by exact prefixLift 607538
  have htrace : WordTrace (prefixWord ++ tailWord_607538) baseStart_607538 baseEnd_607538 := by
    simpa [prefixWord, tailWord_607538, baseEnd_607538] using wordTrace_append hprefix tailTrace_607538
  have hstable : (prefixWord ++ tailWord_607538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607538).length < 2 ^ (prefixWord ++ tailWord_607538).sum := by decide
  have hdescent : baseEnd_607538 < baseStart_607538 := by decide
  rcases family_descends (prefixWord ++ tailWord_607538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607552 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_607552 : Nat := 118140960795 + 607552 * 2 ^ 59
def prefixEnd_607552 : Nat := 4983230072969 + 3 ^ 40 * 607552 * 2
def baseEnd_607552 : Nat := 277303287644899718849711

theorem tailTrace_607552 : CollatzResearch.WordTrace tailWord_607552 prefixEnd_607552 277303287644899718849711 := by
  unfold tailWord_607552
  simp only [CollatzResearch.WordTrace]
  refine ⟨11079620947475170232912455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14772827929966893643883273 11079620947475170232912455)
  ·
    refine ⟨16619431421212755349368683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11079620947475170232912455 16619431421212755349368683)
    ·
      refine ⟨24929147131819133024053025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16619431421212755349368683 24929147131819133024053025)
      ·
        refine ⟨18696860348864349768039769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24929147131819133024053025 18696860348864349768039769)
        ·
          refine ⟨14022645261648262326029827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18696860348864349768039769 14022645261648262326029827)
          ·
            refine ⟨21033967892472393489044741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14022645261648262326029827 21033967892472393489044741)
            ·
              refine ⟨3943868979838573779195889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21033967892472393489044741 3943868979838573779195889)
              ·
                refine ⟨2957901734878930334396917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3943868979838573779195889 2957901734878930334396917)
                ·
                  refine ⟨277303287644899718849711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2957901734878930334396917 277303287644899718849711)
                  ·
                    rfl

theorem cell20_607552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_607552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607552 prefixEnd_607552 := by exact prefixLift 607552
  have htrace : WordTrace (prefixWord ++ tailWord_607552) baseStart_607552 baseEnd_607552 := by
    simpa [prefixWord, tailWord_607552, baseEnd_607552] using wordTrace_append hprefix tailTrace_607552
  have hstable : (prefixWord ++ tailWord_607552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607552).length < 2 ^ (prefixWord ++ tailWord_607552).sum := by decide
  have hdescent : baseEnd_607552 < baseStart_607552 := by decide
  rcases family_descends (prefixWord ++ tailWord_607552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607558 : List Nat := [6, 1, 1, 3, 1, 1, 7]
def baseStart_607558 : Nat := 118140960795 + 607558 * 2 ^ 59
def prefixEnd_607558 : Nat := 4983230072969 + 3 ^ 40 * 607558 * 2
def baseEnd_607558 : Nat := 30811780689821151627743

theorem tailTrace_607558 : CollatzResearch.WordTrace tailWord_607558 prefixEnd_607558 30811780689821151627743 := by
  unfold tailWord_607558
  simp only [CollatzResearch.WordTrace]
  refine ⟨692483147904018859079479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14772973821952402327028885 692483147904018859079479)
  ·
    refine ⟨1038724721856028288619219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 692483147904018859079479 1038724721856028288619219)
    ·
      refine ⟨1558087082784042432928829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1038724721856028288619219 1558087082784042432928829)
      ·
        refine ⟨584282656044015912348311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1558087082784042432928829 584282656044015912348311)
        ·
          refine ⟨876423984066023868522467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584282656044015912348311 876423984066023868522467)
          ·
            refine ⟨1314635976099035802783701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876423984066023868522467 1314635976099035802783701)
            ·
              refine ⟨30811780689821151627743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1314635976099035802783701 30811780689821151627743)
              ·
                rfl

theorem cell20_607558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 7].length) (baseStart_607558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607558 prefixEnd_607558 := by exact prefixLift 607558
  have htrace : WordTrace (prefixWord ++ tailWord_607558) baseStart_607558 baseEnd_607558 := by
    simpa [prefixWord, tailWord_607558, baseEnd_607558] using wordTrace_append hprefix tailTrace_607558
  have hstable : (prefixWord ++ tailWord_607558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607558).length < 2 ^ (prefixWord ++ tailWord_607558).sum := by decide
  have hdescent : baseEnd_607558 < baseStart_607558 := by decide
  rcases family_descends (prefixWord ++ tailWord_607558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607565 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 5]
def baseStart_607565 : Nat := 118140960795 + 607565 * 2 ^ 59
def prefixEnd_607565 : Nat := 4983230072969 + 3 ^ 40 * 607565 * 2
def baseEnd_607565 : Nat := 277309221199129451416325

theorem tailTrace_607565 : CollatzResearch.WordTrace tailWord_607565 prefixEnd_607565 277309221199129451416325 := by
  unfold tailWord_607565
  simp only [CollatzResearch.WordTrace]
  refine ⟨22159716043903243686048149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14773144029268829124032099 22159716043903243686048149)
  ·
    refine ⟨1038736689557964547783507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22159716043903243686048149 1038736689557964547783507)
    ·
      refine ⟨1558105034336946821675261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1038736689557964547783507 1558105034336946821675261)
      ·
        refine ⟨584289387876355058128223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1558105034336946821675261 584289387876355058128223)
        ·
          refine ⟨876434081814532587192335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584289387876355058128223 876434081814532587192335)
          ·
            refine ⟨1314651122721798880788503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876434081814532587192335 1314651122721798880788503)
            ·
              refine ⟨1971976684082698321182755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314651122721798880788503 1971976684082698321182755)
              ·
                refine ⟨2957965026124047481774133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1971976684082698321182755 2957965026124047481774133)
                ·
                  refine ⟨277309221199129451416325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2957965026124047481774133 277309221199129451416325)
                  ·
                    rfl

theorem cell20_607565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_607565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607565 prefixEnd_607565 := by exact prefixLift 607565
  have htrace : WordTrace (prefixWord ++ tailWord_607565) baseStart_607565 baseEnd_607565 := by
    simpa [prefixWord, tailWord_607565, baseEnd_607565] using wordTrace_append hprefix tailTrace_607565
  have hstable : (prefixWord ++ tailWord_607565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607565).length < 2 ^ (prefixWord ++ tailWord_607565).sum := by decide
  have hdescent : baseEnd_607565 < baseStart_607565 := by decide
  rcases family_descends (prefixWord ++ tailWord_607565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607576 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 4]
def baseStart_607576 : Nat := 118140960795 + 607576 * 2 ^ 59
def prefixEnd_607576 : Nat := 4983230072969 + 3 ^ 40 * 607576 * 2
def baseEnd_607576 : Nat := 277314241898862302049613

theorem tailTrace_607576 : CollatzResearch.WordTrace tailWord_607576 prefixEnd_607576 277314241898862302049613 := by
  unfold tailWord_607576
  simp only [CollatzResearch.WordTrace]
  refine ⟨11080058623431696282349291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14773411497908928376465721 11080058623431696282349291)
  ·
    refine ⟨16620087935147544423523937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11080058623431696282349291 16620087935147544423523937)
    ·
      refine ⟨12465065951360658317642953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16620087935147544423523937 12465065951360658317642953)
      ·
        refine ⟨9348799463520493738232215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12465065951360658317642953 9348799463520493738232215)
        ·
          refine ⟨14023199195280740607348323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9348799463520493738232215 14023199195280740607348323)
          ·
            refine ⟨21034798792921110911022485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14023199195280740607348323 21034798792921110911022485)
            ·
              refine ⟨986006193418177073954179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21034798792921110911022485 986006193418177073954179)
              ·
                refine ⟨1479009290127265610931269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986006193418177073954179 1479009290127265610931269)
                ·
                  refine ⟨277314241898862302049613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1479009290127265610931269 277314241898862302049613)
                  ·
                    rfl

theorem cell20_607576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_607576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607576 prefixEnd_607576 := by exact prefixLift 607576
  have htrace : WordTrace (prefixWord ++ tailWord_607576) baseStart_607576 baseEnd_607576 := by
    simpa [prefixWord, tailWord_607576, baseEnd_607576] using wordTrace_append hprefix tailTrace_607576
  have hstable : (prefixWord ++ tailWord_607576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607576).length < 2 ^ (prefixWord ++ tailWord_607576).sum := by decide
  have hdescent : baseEnd_607576 < baseStart_607576 := by decide
  rcases family_descends (prefixWord ++ tailWord_607576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607617 : List Nat := [1, 2, 4, 3, 3, 1, 6]
def baseStart_607617 : Nat := 118140960795 + 607617 * 2 ^ 59
def prefixEnd_607617 : Nat := 4983230072969 + 3 ^ 40 * 607617 * 2
def baseEnd_607617 : Nat := 30814772824005375742531

theorem tailTrace_607617 : CollatzResearch.WordTrace tailWord_607617 prefixEnd_607617 30814772824005375742531 := by
  unfold tailWord_607617
  simp only [CollatzResearch.WordTrace]
  refine ⟨22161612639714856566941105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14774408426476571044627403 22161612639714856566941105)
  ·
    refine ⟨16621209479786142425205829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22161612639714856566941105 16621209479786142425205829)
    ·
      refine ⟨3116476777459901704726093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16621209479786142425205829 3116476777459901704726093)
      ·
        refine ⟨1168678791547463139272285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3116476777459901704726093 1168678791547463139272285)
        ·
          refine ⟨438254546830298677227107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1168678791547463139272285 438254546830298677227107)
          ·
            refine ⟨657381820245448015840661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438254546830298677227107 657381820245448015840661)
            ·
              refine ⟨30814772824005375742531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 657381820245448015840661 30814772824005375742531)
              ·
                rfl

theorem cell20_607617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 6].length) (baseStart_607617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607617 prefixEnd_607617 := by exact prefixLift 607617
  have htrace : WordTrace (prefixWord ++ tailWord_607617) baseStart_607617 baseEnd_607617 := by
    simpa [prefixWord, tailWord_607617, baseEnd_607617] using wordTrace_append hprefix tailTrace_607617
  have hstable : (prefixWord ++ tailWord_607617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607617).length < 2 ^ (prefixWord ++ tailWord_607617).sum := by decide
  have hdescent : baseEnd_607617 < baseStart_607617 := by decide
  rcases family_descends (prefixWord ++ tailWord_607617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607628 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_607628 : Nat := 118140960795 + 607628 * 2 ^ 59
def prefixEnd_607628 : Nat := 4983230072969 + 3 ^ 40 * 607628 * 2
def baseEnd_607628 : Nat := 277337976115781232316067

theorem tailTrace_607628 : CollatzResearch.WordTrace tailWord_607628 prefixEnd_607628 277337976115781232316067 := by
  unfold tailWord_607628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11081006921337502722795769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14774675895116670297061025 11081006921337502722795769)
  ·
    refine ⟨8310755191003127042096827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11081006921337502722795769 8310755191003127042096827)
    ·
      refine ⟨12466132786504690563145241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8310755191003127042096827 12466132786504690563145241)
      ·
        refine ⟨9349599589878517922358931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12466132786504690563145241 9349599589878517922358931)
        ·
          refine ⟨14024399384817776883538397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9349599589878517922358931 14024399384817776883538397)
          ·
            refine ⟨5259149769306666331326899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14024399384817776883538397 5259149769306666331326899)
            ·
              refine ⟨7888724653959999496990349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5259149769306666331326899 7888724653959999496990349)
              ·
                refine ⟨2958271745234999811371381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7888724653959999496990349 2958271745234999811371381)
                ·
                  refine ⟨277337976115781232316067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2958271745234999811371381 277337976115781232316067)
                  ·
                    rfl

theorem cell20_607628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_607628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607628 prefixEnd_607628 := by exact prefixLift 607628
  have htrace : WordTrace (prefixWord ++ tailWord_607628) baseStart_607628 baseEnd_607628 := by
    simpa [prefixWord, tailWord_607628, baseEnd_607628] using wordTrace_append hprefix tailTrace_607628
  have hstable : (prefixWord ++ tailWord_607628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607628).length < 2 ^ (prefixWord ++ tailWord_607628).sum := by decide
  have hdescent : baseEnd_607628 < baseStart_607628 := by decide
  rcases family_descends (prefixWord ++ tailWord_607628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607666 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_607666 : Nat := 118140960795 + 607666 * 2 ^ 59
def prefixEnd_607666 : Nat := 4983230072969 + 3 ^ 40 * 607666 * 2
def baseEnd_607666 : Nat := 277355320351221989049245

theorem tailTrace_607666 : CollatzResearch.WordTrace tailWord_607666 prefixEnd_607666 277355320351221989049245 := by
  unfold tailWord_607666
  simp only [CollatzResearch.WordTrace]
  refine ⟨5540849954134334483868713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14775599877691558623649901 5540849954134334483868713)
  ·
    refine ⟨4155637465600750862901535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5540849954134334483868713 4155637465600750862901535)
    ·
      refine ⟨6233456198401126294352303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4155637465600750862901535 6233456198401126294352303)
      ·
        refine ⟨9350184297601689441528455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6233456198401126294352303 9350184297601689441528455)
        ·
          refine ⟨14025276446402534162292683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9350184297601689441528455 14025276446402534162292683)
          ·
            refine ⟨21037914669603801243439025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14025276446402534162292683 21037914669603801243439025)
            ·
              refine ⟨15778436002202850932579269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21037914669603801243439025 15778436002202850932579269)
              ·
                refine ⟨2958456750413034549858613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15778436002202850932579269 2958456750413034549858613)
                ·
                  refine ⟨277355320351221989049245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2958456750413034549858613 277355320351221989049245)
                  ·
                    rfl

theorem cell20_607666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_607666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607666 prefixEnd_607666 := by exact prefixLift 607666
  have htrace : WordTrace (prefixWord ++ tailWord_607666) baseStart_607666 baseEnd_607666 := by
    simpa [prefixWord, tailWord_607666, baseEnd_607666] using wordTrace_append hprefix tailTrace_607666
  have hstable : (prefixWord ++ tailWord_607666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607666).length < 2 ^ (prefixWord ++ tailWord_607666).sum := by decide
  have hdescent : baseEnd_607666 < baseStart_607666 := by decide
  rcases family_descends (prefixWord ++ tailWord_607666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607676 : List Nat := [2, 2, 2, 4, 3, 7]
def baseStart_607676 : Nat := 118140960795 + 607676 * 2 ^ 59
def prefixEnd_607676 : Nat := 4983230072969 + 3 ^ 40 * 607676 * 2
def baseEnd_607676 : Nat := 10272588319396533285773

theorem tailTrace_607676 : CollatzResearch.WordTrace tailWord_607676 prefixEnd_607676 10272588319396533285773 := by
  unfold tailWord_607676
  simp only [CollatzResearch.WordTrace]
  refine ⟨11081882273250554821669441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14775843031000739762225921 11081882273250554821669441)
  ·
    refine ⟨8311411704937916116252081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11081882273250554821669441 8311411704937916116252081)
    ·
      refine ⟨6233558778703437087189061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8311411704937916116252081 6233558778703437087189061)
      ·
        refine ⟨1168792271006894453847949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6233558778703437087189061 1168792271006894453847949)
        ·
          refine ⟨438297101627585420192981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1168792271006894453847949 438297101627585420192981)
          ·
            refine ⟨10272588319396533285773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 438297101627585420192981 10272588319396533285773)
            ·
              rfl

theorem cell20_607676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 7].length) (baseStart_607676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607676 prefixEnd_607676 := by exact prefixLift 607676
  have htrace : WordTrace (prefixWord ++ tailWord_607676) baseStart_607676 baseEnd_607676 := by
    simpa [prefixWord, tailWord_607676, baseEnd_607676] using wordTrace_append hprefix tailTrace_607676
  have hstable : (prefixWord ++ tailWord_607676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607676).length < 2 ^ (prefixWord ++ tailWord_607676).sum := by decide
  have hdescent : baseEnd_607676 < baseStart_607676 := by decide
  rcases family_descends (prefixWord ++ tailWord_607676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607745 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 4]
def baseStart_607745 : Nat := 118140960795 + 607745 * 2 ^ 59
def prefixEnd_607745 : Nat := 4983230072969 + 3 ^ 40 * 607745 * 2
def baseEnd_607745 : Nat := 277391378103848825415589

theorem tailTrace_607745 : CollatzResearch.WordTrace tailWord_607745 prefixEnd_607745 277391378103848825415589 := by
  unfold tailWord_607745
  simp only [CollatzResearch.WordTrace]
  refine ⟨22166281183251134427600689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14777520788834089618400459 22166281183251134427600689)
  ·
    refine ⟨16624710887438350820700517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22166281183251134427600689 16624710887438350820700517)
    ·
      refine ⟨3117133291394690778881347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16624710887438350820700517 3117133291394690778881347)
      ·
        refine ⟨4675699937092036168322021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3117133291394690778881347 4675699937092036168322021)
        ·
          refine ⟨876693738204756781560379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4675699937092036168322021 876693738204756781560379)
          ·
            refine ⟨1315040607307135172340569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876693738204756781560379 1315040607307135172340569)
            ·
              refine ⟨986280455480351379255427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1315040607307135172340569 986280455480351379255427)
              ·
                refine ⟨1479420683220527068883141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986280455480351379255427 1479420683220527068883141)
                ·
                  refine ⟨277391378103848825415589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1479420683220527068883141 277391378103848825415589)
                  ·
                    rfl

theorem cell20_607745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_607745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607745 prefixEnd_607745 := by exact prefixLift 607745
  have htrace : WordTrace (prefixWord ++ tailWord_607745) baseStart_607745 baseEnd_607745 := by
    simpa [prefixWord, tailWord_607745, baseEnd_607745] using wordTrace_append hprefix tailTrace_607745
  have hstable : (prefixWord ++ tailWord_607745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607745).length < 2 ^ (prefixWord ++ tailWord_607745).sum := by decide
  have hdescent : baseEnd_607745 < baseStart_607745 := by decide
  rcases family_descends (prefixWord ++ tailWord_607745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607773 : List Nat := [1, 4, 2, 2, 1, 1, 3, 6]
def baseStart_607773 : Nat := 118140960795 + 607773 * 2 ^ 59
def prefixEnd_607773 : Nat := 4983230072969 + 3 ^ 40 * 607773 * 2
def baseEnd_607773 : Nat := 92468052688935057494047

theorem tailTrace_607773 : CollatzResearch.WordTrace tailWord_607773 prefixEnd_607773 92468052688935057494047 := by
  unfold tailWord_607773
  simp only [CollatzResearch.WordTrace]
  refine ⟨22167302427149695209619973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14778201618099796806413315 22167302427149695209619973)
  ·
    refine ⟨4156369205090567851803745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22167302427149695209619973 4156369205090567851803745)
    ·
      refine ⟨3117276903817925888852809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4156369205090567851803745 3117276903817925888852809)
      ·
        refine ⟨2337957677863444416639607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3117276903817925888852809 2337957677863444416639607)
        ·
          refine ⟨3506936516795166624959411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337957677863444416639607 3506936516795166624959411)
          ·
            refine ⟨5260404775192749937439117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3506936516795166624959411 5260404775192749937439117)
            ·
              refine ⟨1972651790697281226539669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5260404775192749937439117 1972651790697281226539669)
              ·
                refine ⟨92468052688935057494047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1972651790697281226539669 92468052688935057494047)
                ·
                  rfl

theorem cell20_607773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 6].length) (baseStart_607773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607773 prefixEnd_607773 := by exact prefixLift 607773
  have htrace : WordTrace (prefixWord ++ tailWord_607773) baseStart_607773 baseEnd_607773 := by
    simpa [prefixWord, tailWord_607773, baseEnd_607773] using wordTrace_append hprefix tailTrace_607773
  have hstable : (prefixWord ++ tailWord_607773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607773).length < 2 ^ (prefixWord ++ tailWord_607773).sum := by decide
  have hdescent : baseEnd_607773 < baseStart_607773 := by decide
  rcases family_descends (prefixWord ++ tailWord_607773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607779 : List Nat := [1, 1, 1, 4, 6, 1, 1, 3, 2]
def baseStart_607779 : Nat := 118140960795 + 607779 * 2 ^ 59
def prefixEnd_607779 : Nat := 4983230072969 + 3 ^ 40 * 607779 * 2
def baseEnd_607779 : Nat := 277406896630295818282117

theorem tailTrace_607779 : CollatzResearch.WordTrace tailWord_607779 prefixEnd_607779 277406896630295818282117 := by
  unfold tailWord_607779
  simp only [CollatzResearch.WordTrace]
  refine ⟨22167521265127958234338391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14778347510085305489558927 22167521265127958234338391)
  ·
    refine ⟨33251281897691937351507587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22167521265127958234338391 33251281897691937351507587)
    ·
      refine ⟨49876922846537906027261381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33251281897691937351507587 49876922846537906027261381)
      ·
        refine ⟨9351923033725857380111509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49876922846537906027261381 9351923033725857380111509)
        ·
          refine ⟨438371392205899564692727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9351923033725857380111509 438371392205899564692727)
          ·
            refine ⟨657557088308849347039091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438371392205899564692727 657557088308849347039091)
            ·
              refine ⟨986335632463274020558637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657557088308849347039091 986335632463274020558637)
              ·
                refine ⟨369875862173727757709489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 986335632463274020558637 369875862173727757709489)
                ·
                  refine ⟨277406896630295818282117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 369875862173727757709489 277406896630295818282117)
                  ·
                    rfl

theorem cell20_607779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 2].length) (baseStart_607779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607779 prefixEnd_607779 := by exact prefixLift 607779
  have htrace : WordTrace (prefixWord ++ tailWord_607779) baseStart_607779 baseEnd_607779 := by
    simpa [prefixWord, tailWord_607779, baseEnd_607779] using wordTrace_append hprefix tailTrace_607779
  have hstable : (prefixWord ++ tailWord_607779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607779).length < 2 ^ (prefixWord ++ tailWord_607779).sum := by decide
  have hdescent : baseEnd_607779 < baseStart_607779 := by decide
  rcases family_descends (prefixWord ++ tailWord_607779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607790 : List Nat := [4, 1, 3, 1, 2, 3, 6]
def baseStart_607790 : Nat := 118140960795 + 607790 * 2 ^ 59
def prefixEnd_607790 : Nat := 4983230072969 + 3 ^ 40 * 607790 * 2
def baseEnd_607790 : Nat := 30823546370003185435045

theorem tailTrace_607790 : CollatzResearch.WordTrace tailWord_607790 prefixEnd_607790 30823546370003185435045 := by
  unfold tailWord_607790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2770990308511013389123603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14778614978725404741992549 2770990308511013389123603)
  ·
    refine ⟨4156485462766520083685405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2770990308511013389123603 4156485462766520083685405)
    ·
      refine ⟨1558682048537445031382027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4156485462766520083685405 1558682048537445031382027)
      ·
        refine ⟨2338023072806167547073041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1558682048537445031382027 2338023072806167547073041)
        ·
          refine ⟨1753517304604625660304781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2338023072806167547073041 1753517304604625660304781)
          ·
            refine ⟨657568989226734622614293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1753517304604625660304781 657568989226734622614293)
            ·
              refine ⟨30823546370003185435045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 657568989226734622614293 30823546370003185435045)
              ·
                rfl

theorem cell20_607790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 6].length) (baseStart_607790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607790 prefixEnd_607790 := by exact prefixLift 607790
  have htrace : WordTrace (prefixWord ++ tailWord_607790) baseStart_607790 baseEnd_607790 := by
    simpa [prefixWord, tailWord_607790, baseEnd_607790] using wordTrace_append hprefix tailTrace_607790
  have hstable : (prefixWord ++ tailWord_607790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607790).length < 2 ^ (prefixWord ++ tailWord_607790).sum := by decide
  have hdescent : baseEnd_607790 < baseStart_607790 := by decide
  rcases family_descends (prefixWord ++ tailWord_607790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607800 : List Nat := [2, 1, 2, 1, 4, 3, 3, 2, 2]
def baseStart_607800 : Nat := 118140960795 + 607800 * 2 ^ 59
def prefixEnd_607800 : Nat := 4983230072969 + 3 ^ 40 * 607800 * 2
def baseEnd_607800 : Nat := 277416481602513078582031

theorem tailTrace_607800 : CollatzResearch.WordTrace tailWord_607800 prefixEnd_607800 277416481602513078582031 := by
  unfold tailWord_607800
  simp only [CollatzResearch.WordTrace]
  refine ⟨11084143599025939410426427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14778858132034585880568569 11084143599025939410426427)
  ·
    refine ⟨16626215398538909115639641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11084143599025939410426427 16626215398538909115639641)
    ·
      refine ⟨12469661548904181836729731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16626215398538909115639641 12469661548904181836729731)
      ·
        refine ⟨18704492323356272755094597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12469661548904181836729731 18704492323356272755094597)
        ·
          refine ⟨3507092310629301141580237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18704492323356272755094597 3507092310629301141580237)
          ·
            refine ⟨1315159616485987928092589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3507092310629301141580237 1315159616485987928092589)
            ·
              refine ⟨493184856182245473034721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1315159616485987928092589 493184856182245473034721)
              ·
                refine ⟨369888642136684104776041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493184856182245473034721 369888642136684104776041)
                ·
                  refine ⟨277416481602513078582031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 369888642136684104776041 277416481602513078582031)
                  ·
                    rfl

theorem cell20_607800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 2].length) (baseStart_607800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607800 prefixEnd_607800 := by exact prefixLift 607800
  have htrace : WordTrace (prefixWord ++ tailWord_607800) baseStart_607800 baseEnd_607800 := by
    simpa [prefixWord, tailWord_607800, baseEnd_607800] using wordTrace_append hprefix tailTrace_607800
  have hstable : (prefixWord ++ tailWord_607800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607800).length < 2 ^ (prefixWord ++ tailWord_607800).sum := by decide
  have hdescent : baseEnd_607800 < baseStart_607800 := by decide
  rcases family_descends (prefixWord ++ tailWord_607800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607825 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 6]
def baseStart_607825 : Nat := 118140960795 + 607825 * 2 ^ 59
def prefixEnd_607825 : Nat := 4983230072969 + 3 ^ 40 * 607825 * 2
def baseEnd_607825 : Nat := 277427892283724102748595

theorem tailTrace_607825 : CollatzResearch.WordTrace tailWord_607825 prefixEnd_607825 277427892283724102748595 := by
  unfold tailWord_607825
  simp only [CollatzResearch.WordTrace]
  refine ⟨22169199022961308090512929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14779466015307538727008619 22169199022961308090512929)
  ·
    refine ⟨16626899267220981067884697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22169199022961308090512929 16626899267220981067884697)
    ·
      refine ⟨12470174450415735800913523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16626899267220981067884697 12470174450415735800913523)
      ·
        refine ⟨18705261675623603701370285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12470174450415735800913523 18705261675623603701370285)
        ·
          refine ⟨7014473128358851388013857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18705261675623603701370285 7014473128358851388013857)
          ·
            refine ⟨5260854846269138541010393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7014473128358851388013857 5260854846269138541010393)
            ·
              refine ⟨3945641134701853905757795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5260854846269138541010393 3945641134701853905757795)
              ·
                refine ⟨5918461702052780858636693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3945641134701853905757795 5918461702052780858636693)
                ·
                  refine ⟨277427892283724102748595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5918461702052780858636693 277427892283724102748595)
                  ·
                    rfl

theorem cell20_607825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_607825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607825 prefixEnd_607825 := by exact prefixLift 607825
  have htrace : WordTrace (prefixWord ++ tailWord_607825) baseStart_607825 baseEnd_607825 := by
    simpa [prefixWord, tailWord_607825, baseEnd_607825] using wordTrace_append hprefix tailTrace_607825
  have hstable : (prefixWord ++ tailWord_607825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607825).length < 2 ^ (prefixWord ++ tailWord_607825).sum := by decide
  have hdescent : baseEnd_607825 < baseStart_607825 := by decide
  rcases family_descends (prefixWord ++ tailWord_607825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607863 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 4]
def baseStart_607863 : Nat := 118140960795 + 607863 * 2 ^ 59
def prefixEnd_607863 : Nat := 4983230072969 + 3 ^ 40 * 607863 * 2
def baseEnd_607863 : Nat := 277445236519164859481773

theorem tailTrace_607863 : CollatzResearch.WordTrace tailWord_607863 prefixEnd_607863 277445236519164859481773 := by
  unfold tailWord_607863
  simp only [CollatzResearch.WordTrace]
  refine ⟨22170584996823640580396243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14780389997882427053597495 22170584996823640580396243)
  ·
    refine ⟨33255877495235460870594365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22170584996823640580396243 33255877495235460870594365)
    ·
      refine ⟨12470954060713297826472887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33255877495235460870594365 12470954060713297826472887)
      ·
        refine ⟨18706431091069946739709331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12470954060713297826472887 18706431091069946739709331)
        ·
          refine ⟨28059646636604920109563997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18706431091069946739709331 28059646636604920109563997)
          ·
            refine ⟨10522367488726845041086499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28059646636604920109563997 10522367488726845041086499)
            ·
              refine ⟨15783551233090267561629749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10522367488726845041086499 15783551233090267561629749)
              ·
                refine ⟨1479707928102212583902789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15783551233090267561629749 1479707928102212583902789)
                ·
                  refine ⟨277445236519164859481773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1479707928102212583902789 277445236519164859481773)
                  ·
                    rfl

theorem cell20_607863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_607863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607863 prefixEnd_607863 := by exact prefixLift 607863
  have htrace : WordTrace (prefixWord ++ tailWord_607863) baseStart_607863 baseEnd_607863 := by
    simpa [prefixWord, tailWord_607863, baseEnd_607863] using wordTrace_append hprefix tailTrace_607863
  have hstable : (prefixWord ++ tailWord_607863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607863).length < 2 ^ (prefixWord ++ tailWord_607863).sum := by decide
  have hdescent : baseEnd_607863 < baseStart_607863 := by decide
  rcases family_descends (prefixWord ++ tailWord_607863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607873 : List Nat := [1, 2, 4, 2, 1, 2, 2, 3, 3]
def baseStart_607873 : Nat := 118140960795 + 607873 * 2 ^ 59
def prefixEnd_607873 : Nat := 4983230072969 + 3 ^ 40 * 607873 * 2
def baseEnd_607873 : Nat := 277449800791649269148399

theorem tailTrace_607873 : CollatzResearch.WordTrace tailWord_607873 prefixEnd_607873 277449800791649269148399 := by
  unfold tailWord_607873
  simp only [CollatzResearch.WordTrace]
  refine ⟨22170949726787412288260273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14780633151191608192173515 22170949726787412288260273)
  ·
    refine ⟨16628212295090559216195205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22170949726787412288260273 16628212295090559216195205)
    ·
      refine ⟨3117789805329479853036601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16628212295090559216195205 3117789805329479853036601)
      ·
        refine ⟨2338342353997109889777451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3117789805329479853036601 2338342353997109889777451)
        ·
          refine ⟨3507513530995664834666177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2338342353997109889777451 3507513530995664834666177)
          ·
            refine ⟨2630635148246748625999633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3507513530995664834666177 2630635148246748625999633)
            ·
              refine ⟨1972976361185061469499725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2630635148246748625999633 1972976361185061469499725)
              ·
                refine ⟨739866135444398051062397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1972976361185061469499725 739866135444398051062397)
                ·
                  refine ⟨277449800791649269148399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 739866135444398051062397 277449800791649269148399)
                  ·
                    rfl

theorem cell20_607873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_607873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607873 prefixEnd_607873 := by exact prefixLift 607873
  have htrace : WordTrace (prefixWord ++ tailWord_607873) baseStart_607873 baseEnd_607873 := by
    simpa [prefixWord, tailWord_607873, baseEnd_607873] using wordTrace_append hprefix tailTrace_607873
  have hstable : (prefixWord ++ tailWord_607873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607873).length < 2 ^ (prefixWord ++ tailWord_607873).sum := by decide
  have hdescent : baseEnd_607873 < baseStart_607873 := by decide
  rcases family_descends (prefixWord ++ tailWord_607873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607901 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 8]
def baseStart_607901 : Nat := 118140960795 + 607901 * 2 ^ 59
def prefixEnd_607901 : Nat := 4983230072969 + 3 ^ 40 * 607901 * 2
def baseEnd_607901 : Nat := 277462580754605616214951

theorem tailTrace_607901 : CollatzResearch.WordTrace tailWord_607901 prefixEnd_607901 277462580754605616214951 := by
  unfold tailWord_607901
  simp only [CollatzResearch.WordTrace]
  refine ⟨22171970970685973070279557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14781313980457315380186371 22171970970685973070279557)
  ·
    refine ⟨4157244557003619950677417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22171970970685973070279557 4157244557003619950677417)
    ·
      refine ⟨3117933417752714963008063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4157244557003619950677417 3117933417752714963008063)
      ·
        refine ⟨4676900126629072444512095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3117933417752714963008063 4676900126629072444512095)
        ·
          refine ⟨7015350189943608666768143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4676900126629072444512095 7015350189943608666768143)
          ·
            refine ⟨10523025284915413000152215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7015350189943608666768143 10523025284915413000152215)
            ·
              refine ⟨15784537927373119500228323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10523025284915413000152215 15784537927373119500228323)
              ·
                refine ⟨23676806891059679250342485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15784537927373119500228323 23676806891059679250342485)
                ·
                  refine ⟨277462580754605616214951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23676806891059679250342485 277462580754605616214951)
                  ·
                    rfl

theorem cell20_607901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_607901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607901 prefixEnd_607901 := by exact prefixLift 607901
  have htrace : WordTrace (prefixWord ++ tailWord_607901) baseStart_607901 baseEnd_607901 := by
    simpa [prefixWord, tailWord_607901, baseEnd_607901] using wordTrace_append hprefix tailTrace_607901
  have hstable : (prefixWord ++ tailWord_607901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607901).length < 2 ^ (prefixWord ++ tailWord_607901).sum := by decide
  have hdescent : baseEnd_607901 < baseStart_607901 := by decide
  rcases family_descends (prefixWord ++ tailWord_607901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607938 : List Nat := [3, 5, 1, 2, 1, 1, 1, 6]
def baseStart_607938 : Nat := 118140960795 + 607938 * 2 ^ 59
def prefixEnd_607938 : Nat := 4983230072969 + 3 ^ 40 * 607938 * 2
def baseEnd_607938 : Nat := 92493156187599310660489

theorem tailTrace_607938 : CollatzResearch.WordTrace tailWord_607938 prefixEnd_607938 92493156187599310660489 := by
  unfold tailWord_607938
  simp only [CollatzResearch.WordTrace]
  refine ⟨5543330117887982097344117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14782213647701285592917645 5543330117887982097344117)
  ·
    refine ⟨519687198551998321626011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5543330117887982097344117 519687198551998321626011)
    ·
      refine ⟨779530797827997482439017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 519687198551998321626011 779530797827997482439017)
      ·
        refine ⟨584648098370998111829263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 779530797827997482439017 584648098370998111829263)
        ·
          refine ⟨876972147556497167743895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584648098370998111829263 876972147556497167743895)
          ·
            refine ⟨1315458221334745751615843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876972147556497167743895 1315458221334745751615843)
            ·
              refine ⟨1973187332002118627423765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315458221334745751615843 1973187332002118627423765)
              ·
                refine ⟨92493156187599310660489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1973187332002118627423765 92493156187599310660489)
                ·
                  rfl

theorem cell20_607938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_607938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607938 prefixEnd_607938 := by exact prefixLift 607938
  have htrace : WordTrace (prefixWord ++ tailWord_607938) baseStart_607938 baseEnd_607938 := by
    simpa [prefixWord, tailWord_607938, baseEnd_607938] using wordTrace_append hprefix tailTrace_607938
  have hstable : (prefixWord ++ tailWord_607938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607938).length < 2 ^ (prefixWord ++ tailWord_607938).sum := by decide
  have hdescent : baseEnd_607938 < baseStart_607938 := by decide
  rcases family_descends (prefixWord ++ tailWord_607938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607987 : List Nat := [1, 1, 1, 2, 2, 3, 6, 1, 3]
def baseStart_607987 : Nat := 118140960795 + 607987 * 2 ^ 59
def prefixEnd_607987 : Nat := 4983230072969 + 3 ^ 40 * 607987 * 2
def baseEnd_607987 : Nat := 277501833497971539347933

theorem tailTrace_607987 : CollatzResearch.WordTrace tailWord_607987 prefixEnd_607987 277501833497971539347933 := by
  unfold tailWord_607987
  simp only [CollatzResearch.WordTrace]
  refine ⟨22175107648374409757910215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14783405098916273171940143 22175107648374409757910215)
  ·
    refine ⟨33262661472561614636865323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22175107648374409757910215 33262661472561614636865323)
    ·
      refine ⟨49893992208842421955297985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33262661472561614636865323 49893992208842421955297985)
      ·
        refine ⟨37420494156631816466473489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49893992208842421955297985 37420494156631816466473489)
        ·
          refine ⟨28065370617473862349855117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37420494156631816466473489 28065370617473862349855117)
          ·
            refine ⟨10524513981552698381195669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28065370617473862349855117 10524513981552698381195669)
            ·
              refine ⟨493336592885282736618547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10524513981552698381195669 493336592885282736618547)
              ·
                refine ⟨740004889327924104927821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493336592885282736618547 740004889327924104927821)
                ·
                  refine ⟨277501833497971539347933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740004889327924104927821 277501833497971539347933)
                  ·
                    rfl

theorem cell20_607987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 3].length) (baseStart_607987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_607987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_607987 prefixEnd_607987 := by exact prefixLift 607987
  have htrace : WordTrace (prefixWord ++ tailWord_607987) baseStart_607987 baseEnd_607987 := by
    simpa [prefixWord, tailWord_607987, baseEnd_607987] using wordTrace_append hprefix tailTrace_607987
  have hstable : (prefixWord ++ tailWord_607987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607987).length < 2 ^ (prefixWord ++ tailWord_607987).sum := by decide
  have hdescent : baseEnd_607987 < baseStart_607987 := by decide
  rcases family_descends (prefixWord ++ tailWord_607987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608020 : List Nat := [2, 4, 4, 1, 2, 1, 2, 2, 2]
def baseStart_608020 : Nat := 118140960795 + 608020 * 2 ^ 59
def prefixEnd_608020 : Nat := 4983230072969 + 3 ^ 40 * 608020 * 2
def baseEnd_608020 : Nat := 277516895597170091247799

theorem tailTrace_608020 : CollatzResearch.WordTrace tailWord_608020 prefixEnd_608020 277516895597170091247799 := by
  unfold tailWord_608020
  simp only [CollatzResearch.WordTrace]
  refine ⟨11088155628627428196930757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14784207504836570929241009 11088155628627428196930757)
  ·
    refine ⟨2079029180367642786924517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11088155628627428196930757 2079029180367642786924517)
    ·
      refine ⟨389817971318933022548347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2079029180367642786924517 389817971318933022548347)
      ·
        refine ⟨584726956978399533822521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389817971318933022548347 584726956978399533822521)
        ·
          refine ⟨438545217733799650366891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 584726956978399533822521 438545217733799650366891)
          ·
            refine ⟨657817826600699475550337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438545217733799650366891 657817826600699475550337)
            ·
              refine ⟨493363369950524606662753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 657817826600699475550337 493363369950524606662753)
              ·
                refine ⟨370022527462893454997065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493363369950524606662753 370022527462893454997065)
                ·
                  refine ⟨277516895597170091247799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370022527462893454997065 277516895597170091247799)
                  ·
                    rfl

theorem cell20_608020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_608020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608020 prefixEnd_608020 := by exact prefixLift 608020
  have htrace : WordTrace (prefixWord ++ tailWord_608020) baseStart_608020 baseEnd_608020 := by
    simpa [prefixWord, tailWord_608020, baseEnd_608020] using wordTrace_append hprefix tailTrace_608020
  have hstable : (prefixWord ++ tailWord_608020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608020).length < 2 ^ (prefixWord ++ tailWord_608020).sum := by decide
  have hdescent : baseEnd_608020 < baseStart_608020 := by decide
  rcases family_descends (prefixWord ++ tailWord_608020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608060 : List Nat := [2, 2, 2, 2, 1, 1, 2, 8]
def baseStart_608060 : Nat := 118140960795 + 608060 * 2 ^ 59
def prefixEnd_608060 : Nat := 4983230072969 + 3 ^ 40 * 608060 * 2
def baseEnd_608060 : Nat := 92511717562369243304767

theorem tailTrace_608060 : CollatzResearch.WordTrace tailWord_608060 prefixEnd_608060 92511717562369243304767 := by
  unfold tailWord_608060
  simp only [CollatzResearch.WordTrace]
  refine ⟨11088885088554971612658817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14785180118073295483545089 11088885088554971612658817)
  ·
    refine ⟨8316663816416228709494113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11088885088554971612658817 8316663816416228709494113)
    ·
      refine ⟨6237497862312171532120585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8316663816416228709494113 6237497862312171532120585)
      ·
        refine ⟨4678123396734128649090439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6237497862312171532120585 4678123396734128649090439)
        ·
          refine ⟨7017185095101192973635659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4678123396734128649090439 7017185095101192973635659)
          ·
            refine ⟨10525777642651789460453489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7017185095101192973635659 10525777642651789460453489)
            ·
              refine ⟨7894333231988842095340117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10525777642651789460453489 7894333231988842095340117)
              ·
                refine ⟨92511717562369243304767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7894333231988842095340117 92511717562369243304767)
                ·
                  rfl

theorem cell20_608060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_608060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608060 prefixEnd_608060 := by exact prefixLift 608060
  have htrace : WordTrace (prefixWord ++ tailWord_608060) baseStart_608060 baseEnd_608060 := by
    simpa [prefixWord, tailWord_608060, baseEnd_608060] using wordTrace_append hprefix tailTrace_608060
  have hstable : (prefixWord ++ tailWord_608060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608060).length < 2 ^ (prefixWord ++ tailWord_608060).sum := by decide
  have hdescent : baseEnd_608060 < baseStart_608060 := by decide
  rcases family_descends (prefixWord ++ tailWord_608060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608142 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_608142 : Nat := 118140960795 + 608142 * 2 ^ 59
def prefixEnd_608142 : Nat := 4983230072969 + 3 ^ 40 * 608142 * 2
def baseEnd_608142 : Nat := 277572579721479889180633

theorem tailTrace_608142 : CollatzResearch.WordTrace tailWord_608142 prefixEnd_608142 277572579721479889180633 := by
  unfold tailWord_608142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2772595120351608903725335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14787173975208580819868453 2772595120351608903725335)
  ·
    refine ⟨4158892680527413355588003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2772595120351608903725335 4158892680527413355588003)
    ·
      refine ⟨6238339020791120033382005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4158892680527413355588003 6238339020791120033382005)
      ·
        refine ⟨584844283199167503129563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6238339020791120033382005 584844283199167503129563)
        ·
          refine ⟨877266424798751254694345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584844283199167503129563 877266424798751254694345)
          ·
            refine ⟨657949818599063441020759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 877266424798751254694345 657949818599063441020759)
            ·
              refine ⟨986924727898595161531139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657949818599063441020759 986924727898595161531139)
              ·
                refine ⟨1480387091847892742296709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986924727898595161531139 1480387091847892742296709)
                ·
                  refine ⟨277572579721479889180633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1480387091847892742296709 277572579721479889180633)
                  ·
                    rfl

theorem cell20_608142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_608142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608142 prefixEnd_608142 := by exact prefixLift 608142
  have htrace : WordTrace (prefixWord ++ tailWord_608142) baseStart_608142 baseEnd_608142 := by
    simpa [prefixWord, tailWord_608142, baseEnd_608142] using wordTrace_append hprefix tailTrace_608142
  have hstable : (prefixWord ++ tailWord_608142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608142).length < 2 ^ (prefixWord ++ tailWord_608142).sum := by decide
  have hdescent : baseEnd_608142 < baseStart_608142 := by decide
  rcases family_descends (prefixWord ++ tailWord_608142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
