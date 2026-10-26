import V185TrunkScan23Chunk0517

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3063231 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 5, 3, 2]
def baseStart_3063231 : Nat := 118140960795 + 3063231 * 2 ^ 59
def prefixEnd_3063231 : Nat := 4983230072969 + 3 ^ 40 * 3063231 * 2
def baseEnd_3063231 : Nat := 1572909858752809828324963

theorem tailTrace_3063231 : CollatzResearch.WordTrace tailWord_3063231 prefixEnd_3063231 1572909858752809828324963 := by
  unfold tailWord_3063231
  simp only [CollatzResearch.WordTrace]
  refine ⟨111725213165444720049157547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74483475443629813366105031 111725213165444720049157547)
  ·
    refine ⟨167587819748167080073736321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111725213165444720049157547 167587819748167080073736321)
    ·
      refine ⟨125690864811125310055302241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167587819748167080073736321 125690864811125310055302241)
      ·
        refine ⟨94268148608343982541476681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125690864811125310055302241 94268148608343982541476681)
        ·
          refine ⟨70701111456257986906107511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94268148608343982541476681 70701111456257986906107511)
          ·
            refine ⟨106051667184386980359161267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70701111456257986906107511 106051667184386980359161267)
            ·
              refine ⟨159077500776580470538741901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106051667184386980359161267 159077500776580470538741901)
              ·
                refine ⟨59654062791217676452028213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159077500776580470538741901 59654062791217676452028213)
                ·
                  refine ⟨5592568386676657167377645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59654062791217676452028213 5592568386676657167377645)
                  ·
                    refine ⟨2097213145003746437766617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5592568386676657167377645 2097213145003746437766617)
                    ·
                      refine ⟨1572909858752809828324963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2097213145003746437766617 1572909858752809828324963)
                      ·
                        rfl

theorem cell23_3063231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 3, 2].length) (baseStart_3063231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063231 prefixEnd_3063231 := by exact prefixLift 3063231
  have htrace : WordTrace (prefixWord ++ tailWord_3063231) baseStart_3063231 baseEnd_3063231 := by
    simpa [prefixWord, tailWord_3063231, baseEnd_3063231] using wordTrace_append hprefix tailTrace_3063231
  have hstable : (prefixWord ++ tailWord_3063231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063231).length < 2 ^ (prefixWord ++ tailWord_3063231).sum := by decide
  have hdescent : baseEnd_3063231 < baseStart_3063231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063298 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3063298 : Nat := 118140960795 + 3063298 * 2 ^ 59
def prefixEnd_3063298 : Nat := 4983230072969 + 3 ^ 40 * 3063298 * 2
def baseEnd_3063298 : Nat := 1572944261956661066187155

theorem tailTrace_3063298 : CollatzResearch.WordTrace tailWord_3063298 prefixEnd_3063298 1572944261956661066187155 := by
  unfold tailWord_3063298
  simp only [CollatzResearch.WordTrace]
  refine ⟨27931914214050497622961637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74485104570801326994564365 27931914214050497622961637)
  ·
    refine ⟨5237233915134468304305307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27931914214050497622961637 5237233915134468304305307)
    ·
      refine ⟨7855850872701702456457961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5237233915134468304305307 7855850872701702456457961)
      ·
        refine ⟨5891888154526276842343471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7855850872701702456457961 5891888154526276842343471)
        ·
          refine ⟨8837832231789415263515207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5891888154526276842343471 8837832231789415263515207)
          ·
            refine ⟨13256748347684122895272811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8837832231789415263515207 13256748347684122895272811)
            ·
              refine ⟨19885122521526184342909217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13256748347684122895272811 19885122521526184342909217)
              ·
                refine ⟨14913841891144638257181913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19885122521526184342909217 14913841891144638257181913)
                ·
                  refine ⟨11185381418358478692886435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14913841891144638257181913 11185381418358478692886435)
                  ·
                    refine ⟨16778072127537718039329653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11185381418358478692886435 16778072127537718039329653)
                    ·
                      refine ⟨1572944261956661066187155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16778072127537718039329653 1572944261956661066187155)
                      ·
                        rfl

theorem cell23_3063298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3063298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063298 prefixEnd_3063298 := by exact prefixLift 3063298
  have htrace : WordTrace (prefixWord ++ tailWord_3063298) baseStart_3063298 baseEnd_3063298 := by
    simpa [prefixWord, tailWord_3063298, baseEnd_3063298] using wordTrace_append hprefix tailTrace_3063298
  have hstable : (prefixWord ++ tailWord_3063298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063298).length < 2 ^ (prefixWord ++ tailWord_3063298).sum := by decide
  have hdescent : baseEnd_3063298 < baseStart_3063298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063321 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 3, 7, 2]
def baseStart_3063321 : Nat := 118140960795 + 3063321 * 2 ^ 59
def prefixEnd_3063321 : Nat := 4983230072969 + 3 ^ 40 * 3063321 * 2
def baseEnd_3063321 : Nat := 1572956072011714476199549

theorem tailTrace_3063321 : CollatzResearch.WordTrace tailWord_3063321 prefixEnd_3063321 1572956072011714476199549 := by
  unfold tailWord_3063321
  simp only [CollatzResearch.WordTrace]
  refine ⟨111728495735118665419933817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74485663823412443613289211 111728495735118665419933817)
  ·
    refine ⟨83796371801338999064950363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111728495735118665419933817 83796371801338999064950363)
    ·
      refine ⟨125694557702008498597425545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83796371801338999064950363 125694557702008498597425545)
      ·
        refine ⟨94270918276506373948069159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125694557702008498597425545 94270918276506373948069159)
        ·
          refine ⟨141406377414759560922103739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94270918276506373948069159 141406377414759560922103739)
          ·
            refine ⟨212109566122139341383155609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141406377414759560922103739 212109566122139341383155609)
            ·
              refine ⟨159082174591604506037366707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212109566122139341383155609 159082174591604506037366707)
              ·
                refine ⟨238623261887406759056050061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159082174591604506037366707 238623261887406759056050061)
                ·
                  refine ⟨89483723207777534646018773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238623261887406759056050061 89483723207777534646018773)
                  ·
                    refine ⟨2097274762682285968266065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 89483723207777534646018773 2097274762682285968266065)
                    ·
                      refine ⟨1572956072011714476199549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2097274762682285968266065 1572956072011714476199549)
                      ·
                        rfl

theorem cell23_3063321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 7, 2].length) (baseStart_3063321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063321 prefixEnd_3063321 := by exact prefixLift 3063321
  have htrace : WordTrace (prefixWord ++ tailWord_3063321) baseStart_3063321 baseEnd_3063321 := by
    simpa [prefixWord, tailWord_3063321, baseEnd_3063321] using wordTrace_append hprefix tailTrace_3063321
  have hstable : (prefixWord ++ tailWord_3063321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063321).length < 2 ^ (prefixWord ++ tailWord_3063321).sum := by decide
  have hdescent : baseEnd_3063321 < baseStart_3063321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063338 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_3063338 : Nat := 118140960795 + 3063338 * 2 ^ 59
def prefixEnd_3063338 : Nat := 4983230072969 + 3 ^ 40 * 3063338 * 2
def baseEnd_3063338 : Nat := 1572964801182840909686971

theorem tailTrace_3063338 : CollatzResearch.WordTrace tailWord_3063338 prefixEnd_3063338 1572964801182840909686971 := by
  unfold tailWord_3063338
  simp only [CollatzResearch.WordTrace]
  refine ⟨27932278944014269330825667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74486077184038051548868445 27932278944014269330825667)
  ·
    refine ⟨41898418416021403996238501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27932278944014269330825667 41898418416021403996238501)
    ·
      refine ⟨7855953453004013249294719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41898418416021403996238501 7855953453004013249294719)
      ·
        refine ⟨11783930179506019873942079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7855953453004013249294719 11783930179506019873942079)
        ·
          refine ⟨17675895269259029810913119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11783930179506019873942079 17675895269259029810913119)
          ·
            refine ⟨26513842903888544716369679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17675895269259029810913119 26513842903888544716369679)
            ·
              refine ⟨39770764355832817074554519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26513842903888544716369679 39770764355832817074554519)
              ·
                refine ⟨59656146533749225611831779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39770764355832817074554519 59656146533749225611831779)
                ·
                  refine ⟨89484219800623838417747669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59656146533749225611831779 89484219800623838417747669)
                  ·
                    refine ⟨2097286401577121212915961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 89484219800623838417747669 2097286401577121212915961)
                    ·
                      refine ⟨1572964801182840909686971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2097286401577121212915961 1572964801182840909686971)
                      ·
                        rfl

theorem cell23_3063338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_3063338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063338 prefixEnd_3063338 := by exact prefixLift 3063338
  have htrace : WordTrace (prefixWord ++ tailWord_3063338) baseStart_3063338 baseEnd_3063338 := by
    simpa [prefixWord, tailWord_3063338, baseEnd_3063338] using wordTrace_append hprefix tailTrace_3063338
  have hstable : (prefixWord ++ tailWord_3063338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063338).length < 2 ^ (prefixWord ++ tailWord_3063338).sum := by decide
  have hdescent : baseEnd_3063338 < baseStart_3063338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063344 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 2, 8]
def baseStart_3063344 : Nat := 118140960795 + 3063344 * 2 ^ 59
def prefixEnd_3063344 : Nat := 4983230072969 + 3 ^ 40 * 3063344 * 2
def baseEnd_3063344 : Nat := 524322627355589295403981

theorem tailTrace_3063344 : CollatzResearch.WordTrace tailWord_3063344 prefixEnd_3063344 524322627355589295403981 := by
  unfold tailWord_3063344
  simp only [CollatzResearch.WordTrace]
  refine ⟨55864667307017670174010543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74486223076023560232014057 55864667307017670174010543)
  ·
    refine ⟨83797000960526505261015815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55864667307017670174010543 83797000960526505261015815)
    ·
      refine ⟨125695501440789757891523723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83797000960526505261015815 125695501440789757891523723)
      ·
        refine ⟨188543252161184636837285585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125695501440789757891523723 188543252161184636837285585)
        ·
          refine ⟨141407439120888477627964189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188543252161184636837285585 141407439120888477627964189)
          ·
            refine ⟨53027789670333179110486571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141407439120888477627964189 53027789670333179110486571)
            ·
              refine ⟨79541684505499768665729857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53027789670333179110486571 79541684505499768665729857)
              ·
                refine ⟨59656263379124826499297393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79541684505499768665729857 59656263379124826499297393)
                ·
                  refine ⟨44742197534343619874473045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59656263379124826499297393 44742197534343619874473045)
                  ·
                    refine ⟨524322627355589295403981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44742197534343619874473045 524322627355589295403981)
                    ·
                      rfl

theorem cell23_3063344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_3063344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063344 prefixEnd_3063344 := by exact prefixLift 3063344
  have htrace : WordTrace (prefixWord ++ tailWord_3063344) baseStart_3063344 baseEnd_3063344 := by
    simpa [prefixWord, tailWord_3063344, baseEnd_3063344] using wordTrace_append hprefix tailTrace_3063344
  have hstable : (prefixWord ++ tailWord_3063344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063344).length < 2 ^ (prefixWord ++ tailWord_3063344).sum := by decide
  have hdescent : baseEnd_3063344 < baseStart_3063344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063395 : List Nat := [1, 1, 1, 5, 1, 3, 2, 4, 1, 4]
def baseStart_3063395 : Nat := 118140960795 + 3063395 * 2 ^ 59
def prefixEnd_3063395 : Nat := 4983230072969 + 3 ^ 40 * 3063395 * 2
def baseEnd_3063395 : Nat := 524331356526715728891403

theorem tailTrace_3063395 : CollatzResearch.WordTrace tailWord_3063395 prefixEnd_3063395 524331356526715728891403 := by
  unfold tailWord_3063395
  simp only [CollatzResearch.WordTrace]
  refine ⟨111731194736850576058127639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74487463157900384038751759 111731194736850576058127639)
  ·
    refine ⟨167596792105275864087191459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111731194736850576058127639 167596792105275864087191459)
    ·
      refine ⟨251395188157913796130787189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167596792105275864087191459 251395188157913796130787189)
      ·
        refine ⟨23568298889804418387261299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251395188157913796130787189 23568298889804418387261299)
        ·
          refine ⟨35352448334706627580891949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23568298889804418387261299 35352448334706627580891949)
          ·
            refine ⟨13257168125514985342834481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35352448334706627580891949 13257168125514985342834481)
            ·
              refine ⟨9942876094136239007125861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13257168125514985342834481 9942876094136239007125861)
              ·
                refine ⟨1864289267650544813836099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9942876094136239007125861 1864289267650544813836099)
                ·
                  refine ⟨2796433901475817220754149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1864289267650544813836099 2796433901475817220754149)
                  ·
                    refine ⟨524331356526715728891403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2796433901475817220754149 524331356526715728891403)
                    ·
                      rfl

theorem cell23_3063395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 1, 4].length) (baseStart_3063395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063395 prefixEnd_3063395 := by exact prefixLift 3063395
  have htrace : WordTrace (prefixWord ++ tailWord_3063395) baseStart_3063395 baseEnd_3063395 := by
    simpa [prefixWord, tailWord_3063395, baseEnd_3063395] using wordTrace_append hprefix tailTrace_3063395
  have hstable : (prefixWord ++ tailWord_3063395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063395).length < 2 ^ (prefixWord ++ tailWord_3063395).sum := by decide
  have hdescent : baseEnd_3063395 < baseStart_3063395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063418 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3]
def baseStart_3063418 : Nat := 118140960795 + 3063418 * 2 ^ 59
def prefixEnd_3063418 : Nat := 4983230072969 + 3 ^ 40 * 3063418 * 2
def baseEnd_3063418 : Nat := 1573005879635200596686603

theorem tailTrace_3063418 : CollatzResearch.WordTrace tailWord_3063418 prefixEnd_3063418 1573005879635200596686603 := by
  unfold tailWord_3063418
  simp only [CollatzResearch.WordTrace]
  refine ⟨27933008403941812746553727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74488022410511500657476605 27933008403941812746553727)
  ·
    refine ⟨41899512605912719119830591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27933008403941812746553727 41899512605912719119830591)
    ·
      refine ⟨62849268908869078679745887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41899512605912719119830591 62849268908869078679745887)
      ·
        refine ⟨94273903363303618019618831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62849268908869078679745887 94273903363303618019618831)
        ·
          refine ⟨141410855044955427029428247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94273903363303618019618831 141410855044955427029428247)
          ·
            refine ⟨212116282567433140544142371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141410855044955427029428247 212116282567433140544142371)
            ·
              refine ⟨318174423851149710816213557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212116282567433140544142371 318174423851149710816213557)
              ·
                refine ⟨29828852236045285389020021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 318174423851149710816213557 29828852236045285389020021)
                ·
                  refine ⟨2796454897129245505220627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29828852236045285389020021 2796454897129245505220627)
                  ·
                    refine ⟨4194682345693868257830941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2796454897129245505220627 4194682345693868257830941)
                    ·
                      refine ⟨1573005879635200596686603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4194682345693868257830941 1573005879635200596686603)
                      ·
                        rfl

theorem cell23_3063418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_3063418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063418 prefixEnd_3063418 := by exact prefixLift 3063418
  have htrace : WordTrace (prefixWord ++ tailWord_3063418) baseStart_3063418 baseEnd_3063418 := by
    simpa [prefixWord, tailWord_3063418, baseEnd_3063418] using wordTrace_append hprefix tailTrace_3063418
  have hstable : (prefixWord ++ tailWord_3063418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063418).length < 2 ^ (prefixWord ++ tailWord_3063418).sum := by decide
  have hdescent : baseEnd_3063418 < baseStart_3063418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063471 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 6]
def baseStart_3063471 : Nat := 118140960795 + 3063471 * 2 ^ 59
def prefixEnd_3063471 : Nat := 4983230072969 + 3 ^ 40 * 3063471 * 2
def baseEnd_3063471 : Nat := 1573033094109888889323859

theorem tailTrace_3063471 : CollatzResearch.WordTrace tailWord_3063471 prefixEnd_3063471 1573033094109888889323859 := by
  unfold tailWord_3063471
  simp only [CollatzResearch.WordTrace]
  refine ⟨111733966684575241037894267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74489311123050160691929511 111733966684575241037894267)
  ·
    refine ⟨167600950026862861556841401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111733966684575241037894267 167600950026862861556841401)
    ·
      refine ⟨125700712520147146167631051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167600950026862861556841401 125700712520147146167631051)
      ·
        refine ⟨188551068780220719251446577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125700712520147146167631051 188551068780220719251446577)
        ·
          refine ⟨141413301585165539438584933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188551068780220719251446577 141413301585165539438584933)
          ·
            refine ⟨26514994047218538644734675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141413301585165539438584933 26514994047218538644734675)
            ·
              refine ⟨39772491070827807967102013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26514994047218538644734675 39772491070827807967102013)
              ·
                refine ⟨14914684151560427987663255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39772491070827807967102013 14914684151560427987663255)
                ·
                  refine ⟨22372026227340641981494883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14914684151560427987663255 22372026227340641981494883)
                  ·
                    refine ⟨33558039341010962972242325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22372026227340641981494883 33558039341010962972242325)
                    ·
                      refine ⟨1573033094109888889323859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33558039341010962972242325 1573033094109888889323859)
                      ·
                        rfl

theorem cell23_3063471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_3063471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063471 prefixEnd_3063471 := by exact prefixLift 3063471
  have htrace : WordTrace (prefixWord ++ tailWord_3063471) baseStart_3063471 baseEnd_3063471 := by
    simpa [prefixWord, tailWord_3063471, baseEnd_3063471] using wordTrace_append hprefix tailTrace_3063471
  have hstable : (prefixWord ++ tailWord_3063471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063471).length < 2 ^ (prefixWord ++ tailWord_3063471).sum := by decide
  have hdescent : baseEnd_3063471 < baseStart_3063471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063475 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 5, 2, 2]
def baseStart_3063475 : Nat := 118140960795 + 3063475 * 2 ^ 59
def prefixEnd_3063475 : Nat := 4983230072969 + 3 ^ 40 * 3063475 * 2
def baseEnd_3063475 : Nat := 1573035148032506873673841

theorem tailTrace_3063475 : CollatzResearch.WordTrace tailWord_3063475 prefixEnd_3063475 1573035148032506873673841 := by
  unfold tailWord_3063475
  simp only [CollatzResearch.WordTrace]
  refine ⟨111734112576560749721039879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74489408384373833147359919 111734112576560749721039879)
  ·
    refine ⟨167601168864841124581559819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111734112576560749721039879 167601168864841124581559819)
    ·
      refine ⟨251401753297261686872339729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167601168864841124581559819 251401753297261686872339729)
      ·
        refine ⟨188551314972946265154254797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251401753297261686872339729 188551314972946265154254797)
        ·
          refine ⟨70706743114854849432845549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188551314972946265154254797 70706743114854849432845549)
          ·
            refine ⟨26515028668070568537317081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70706743114854849432845549 26515028668070568537317081)
            ·
              refine ⟨19886271501052926402987811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26515028668070568537317081 19886271501052926402987811)
              ·
                refine ⟨29829407251579389604481717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19886271501052926402987811 29829407251579389604481717)
                ·
                  refine ⟨2796506929835567775420161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29829407251579389604481717 2796506929835567775420161)
                  ·
                    refine ⟨2097380197376675831565121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2796506929835567775420161 2097380197376675831565121)
                    ·
                      refine ⟨1573035148032506873673841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2097380197376675831565121 1573035148032506873673841)
                      ·
                        rfl

theorem cell23_3063475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 2, 2].length) (baseStart_3063475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063475 prefixEnd_3063475 := by exact prefixLift 3063475
  have htrace : WordTrace (prefixWord ++ tailWord_3063475) baseStart_3063475 baseEnd_3063475 := by
    simpa [prefixWord, tailWord_3063475, baseEnd_3063475] using wordTrace_append hprefix tailTrace_3063475
  have hstable : (prefixWord ++ tailWord_3063475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063475).length < 2 ^ (prefixWord ++ tailWord_3063475).sum := by decide
  have hdescent : baseEnd_3063475 < baseStart_3063475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063481 : List Nat := [1, 2, 1, 4, 1, 1, 4, 9]
def baseStart_3063481 : Nat := 118140960795 + 3063481 * 2 ^ 59
def prefixEnd_3063481 : Nat := 4983230072969 + 3 ^ 40 * 3063481 * 2
def baseEnd_3063481 : Nat := 58260675145053105562919

theorem tailTrace_3063481 : CollatzResearch.WordTrace tailWord_3063481 prefixEnd_3063481 58260675145053105562919 := by
  unfold tailWord_3063481
  simp only [CollatzResearch.WordTrace]
  refine ⟨111734331414539012745758297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74489554276359341830505531 111734331414539012745758297)
  ·
    refine ⟨83800748560904259559318723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111734331414539012745758297 83800748560904259559318723)
    ·
      refine ⟨125701122841356389338978085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83800748560904259559318723 125701122841356389338978085)
      ·
        refine ⟨23568960532754323001058391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125701122841356389338978085 23568960532754323001058391)
        ·
          refine ⟨35353440799131484501587587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23568960532754323001058391 35353440799131484501587587)
          ·
            refine ⟨53030161198697226752381381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35353440799131484501587587 53030161198697226752381381)
            ·
              refine ⟨9943155224755730016071509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53030161198697226752381381 9943155224755730016071509)
              ·
                refine ⟨58260675145053105562919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9943155224755730016071509 58260675145053105562919)
                ·
                  rfl

theorem cell23_3063481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 9].length) (baseStart_3063481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063481 prefixEnd_3063481 := by exact prefixLift 3063481
  have htrace : WordTrace (prefixWord ++ tailWord_3063481) baseStart_3063481 baseEnd_3063481 := by
    simpa [prefixWord, tailWord_3063481, baseEnd_3063481] using wordTrace_append hprefix tailTrace_3063481
  have hstable : (prefixWord ++ tailWord_3063481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063481).length < 2 ^ (prefixWord ++ tailWord_3063481).sum := by decide
  have hdescent : baseEnd_3063481 < baseStart_3063481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063488 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 4]
def baseStart_3063488 : Nat := 118140960795 + 3063488 * 2 ^ 59
def prefixEnd_3063488 : Nat := 4983230072969 + 3 ^ 40 * 3063488 * 2
def baseEnd_3063488 : Nat := 1573041823281015322811281

theorem tailTrace_3063488 : CollatzResearch.WordTrace tailWord_3063488 prefixEnd_3063488 1573041823281015322811281 := by
  unfold tailWord_3063488
  simp only [CollatzResearch.WordTrace]
  refine ⟨55867293362756826470631559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74489724483675768627508745 55867293362756826470631559)
  ·
    refine ⟨83800940044135239705947339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55867293362756826470631559 83800940044135239705947339)
    ·
      refine ⟨125701410066202859558921009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83800940044135239705947339 125701410066202859558921009)
      ·
        refine ⟨94276057549652144669190757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125701410066202859558921009 94276057549652144669190757)
        ·
          refine ⟨17676760790559777125473267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94276057549652144669190757 17676760790559777125473267)
          ·
            refine ⟨26515141185839665688209901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17676760790559777125473267 26515141185839665688209901)
            ·
              refine ⟨9943177944689874633078713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26515141185839665688209901 9943177944689874633078713)
              ·
                refine ⟨7457383458517405974809035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9943177944689874633078713 7457383458517405974809035)
                ·
                  refine ⟨11186075187776108962213553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7457383458517405974809035 11186075187776108962213553)
                  ·
                    refine ⟨8389556390832081721660165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11186075187776108962213553 8389556390832081721660165)
                    ·
                      refine ⟨1573041823281015322811281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8389556390832081721660165 1573041823281015322811281)
                      ·
                        rfl

theorem cell23_3063488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_3063488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063488 prefixEnd_3063488 := by exact prefixLift 3063488
  have htrace : WordTrace (prefixWord ++ tailWord_3063488) baseStart_3063488 baseEnd_3063488 := by
    simpa [prefixWord, tailWord_3063488, baseEnd_3063488] using wordTrace_append hprefix tailTrace_3063488
  have hstable : (prefixWord ++ tailWord_3063488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063488).length < 2 ^ (prefixWord ++ tailWord_3063488).sum := by decide
  have hdescent : baseEnd_3063488 < baseStart_3063488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063492 : List Nat := [2, 3, 3, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_3063492 : Nat := 118140960795 + 3063492 * 2 ^ 59
def prefixEnd_3063492 : Nat := 4983230072969 + 3 ^ 40 * 3063492 * 2
def baseEnd_3063492 : Nat := 1573043877203633307161263

theorem tailTrace_3063492 : CollatzResearch.WordTrace tailWord_3063492 prefixEnd_3063492 1573043877203633307161263 := by
  unfold tailWord_3063492
  simp only [CollatzResearch.WordTrace]
  refine ⟨55867366308749580812204365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74489821744999441082939153 55867366308749580812204365)
  ·
    refine ⟨20950262365781092804576637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55867366308749580812204365 20950262365781092804576637)
    ·
      refine ⟨7856348387167909801716239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20950262365781092804576637 7856348387167909801716239)
      ·
        refine ⟨11784522580751864702574359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7856348387167909801716239 11784522580751864702574359)
        ·
          refine ⟨17676783871127797053861539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11784522580751864702574359 17676783871127797053861539)
          ·
            refine ⟨26515175806691695580792309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17676783871127797053861539 26515175806691695580792309)
            ·
              refine ⟨2485797731877346460699279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26515175806691695580792309 2485797731877346460699279)
              ·
                refine ⟨3728696597816019691048919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2485797731877346460699279 3728696597816019691048919)
                ·
                  refine ⟨5593044896724029536573379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3728696597816019691048919 5593044896724029536573379)
                  ·
                    refine ⟨8389567345086044304860069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5593044896724029536573379 8389567345086044304860069)
                    ·
                      refine ⟨1573043877203633307161263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8389567345086044304860069 1573043877203633307161263)
                      ·
                        rfl

theorem cell23_3063492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_3063492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063492 prefixEnd_3063492 := by exact prefixLift 3063492
  have htrace : WordTrace (prefixWord ++ tailWord_3063492) baseStart_3063492 baseEnd_3063492 := by
    simpa [prefixWord, tailWord_3063492, baseEnd_3063492] using wordTrace_append hprefix tailTrace_3063492
  have hstable : (prefixWord ++ tailWord_3063492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063492).length < 2 ^ (prefixWord ++ tailWord_3063492).sum := by decide
  have hdescent : baseEnd_3063492 < baseStart_3063492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063498 : List Nat := [3, 1, 2, 1, 6, 10]
def baseStart_3063498 : Nat := 118140960795 + 3063498 * 2 ^ 59
def prefixEnd_3063498 : Nat := 4983230072969 + 3 ^ 40 * 3063498 * 2
def baseEnd_3063498 : Nat := 6473444271965268657145

theorem tailTrace_3063498 : CollatzResearch.WordTrace tailWord_3063498 prefixEnd_3063498 6473444271965268657145 := by
  unfold tailWord_3063498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27933737863869356162281787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74489967636984949766084765 27933737863869356162281787)
  ·
    refine ⟨41900606795804034243422681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27933737863869356162281787 41900606795804034243422681)
    ·
      refine ⟨31425455096853025682567011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41900606795804034243422681 31425455096853025682567011)
      ·
        refine ⟨47138182645279538523850517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31425455096853025682567011 47138182645279538523850517)
        ·
          refine ⟨2209602311497478368305493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47138182645279538523850517 2209602311497478368305493)
          ·
            refine ⟨6473444271965268657145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2209602311497478368305493 6473444271965268657145)
            ·
              rfl

theorem cell23_3063498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 10].length) (baseStart_3063498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063498 prefixEnd_3063498 := by exact prefixLift 3063498
  have htrace : WordTrace (prefixWord ++ tailWord_3063498) baseStart_3063498 baseEnd_3063498 := by
    simpa [prefixWord, tailWord_3063498, baseEnd_3063498] using wordTrace_append hprefix tailTrace_3063498
  have hstable : (prefixWord ++ tailWord_3063498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063498).length < 2 ^ (prefixWord ++ tailWord_3063498).sum := by decide
  have hdescent : baseEnd_3063498 < baseStart_3063498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063511 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 1, 9]
def baseStart_3063511 : Nat := 118140960795 + 3063511 * 2 ^ 59
def prefixEnd_3063511 : Nat := 4983230072969 + 3 ^ 40 * 3063511 * 2
def baseEnd_3063511 : Nat := 524351211112022910941225

theorem tailTrace_3063511 : CollatzResearch.WordTrace tailWord_3063511 prefixEnd_3063511 524351211112022910941225 := by
  unfold tailWord_3063511
  simp only [CollatzResearch.WordTrace]
  refine ⟨111735425604430327869350387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74490283736286885246233591 111735425604430327869350387)
  ·
    refine ⟨167603138406645491804025581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111735425604430327869350387 167603138406645491804025581)
    ·
      refine ⟨62851176902492059426509593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167603138406645491804025581 62851176902492059426509593)
      ·
        refine ⟨47138382676869044569882195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62851176902492059426509593 47138382676869044569882195)
        ·
          refine ⟨70707574015303566854823293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47138382676869044569882195 70707574015303566854823293)
          ·
            refine ⟨26515340255738837570558735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70707574015303566854823293 26515340255738837570558735)
            ·
              refine ⟨39773010383608256355838103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26515340255738837570558735 39773010383608256355838103)
              ·
                refine ⟨59659515575412384533757155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39773010383608256355838103 59659515575412384533757155)
                ·
                  refine ⟨89489273363118576800635733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59659515575412384533757155 89489273363118576800635733)
                  ·
                    refine ⟨524351211112022910941225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 89489273363118576800635733 524351211112022910941225)
                    ·
                      rfl

theorem cell23_3063511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_3063511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063511 prefixEnd_3063511 := by exact prefixLift 3063511
  have htrace : WordTrace (prefixWord ++ tailWord_3063511) baseStart_3063511 baseEnd_3063511 := by
    simpa [prefixWord, tailWord_3063511, baseEnd_3063511] using wordTrace_append hprefix tailTrace_3063511
  have hstable : (prefixWord ++ tailWord_3063511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063511).length < 2 ^ (prefixWord ++ tailWord_3063511).sum := by decide
  have hdescent : baseEnd_3063511 < baseStart_3063511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063525 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 1, 3, 3]
def baseStart_3063525 : Nat := 118140960795 + 3063525 * 2 ^ 59
def prefixEnd_3063525 : Nat := 4983230072969 + 3 ^ 40 * 3063525 * 2
def baseEnd_3063525 : Nat := 1573060822065231678048611

theorem tailTrace_3063525 : CollatzResearch.WordTrace tailWord_3063525 prefixEnd_3063525 1573060822065231678048611 := by
  unfold tailWord_3063525
  simp only [CollatzResearch.WordTrace]
  refine ⟨111735936226379608260360029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74490624150919738840240019 111735936226379608260360029)
  ·
    refine ⟨41900976084892353097635011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111735936226379608260360029 41900976084892353097635011)
    ·
      refine ⟨62851464127338529646452517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41900976084892353097635011 62851464127338529646452517)
      ·
        refine ⟨11784649523875974308709847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62851464127338529646452517 11784649523875974308709847)
        ·
          refine ⟨17676974285813961463064771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11784649523875974308709847 17676974285813961463064771)
          ·
            refine ⟨26515461428720942194597157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17676974285813961463064771 26515461428720942194597157)
            ·
              refine ⟨4971649017885176661486967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26515461428720942194597157 4971649017885176661486967)
              ·
                refine ⟨7457473526827764992230451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4971649017885176661486967 7457473526827764992230451)
                ·
                  refine ⟨11186210290241647488345677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7457473526827764992230451 11186210290241647488345677)
                  ·
                    refine ⟨4194828858840617808129629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11186210290241647488345677 4194828858840617808129629)
                    ·
                      refine ⟨1573060822065231678048611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4194828858840617808129629 1573060822065231678048611)
                      ·
                        rfl

theorem cell23_3063525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_3063525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063525 prefixEnd_3063525 := by exact prefixLift 3063525
  have htrace : WordTrace (prefixWord ++ tailWord_3063525) baseStart_3063525 baseEnd_3063525 := by
    simpa [prefixWord, tailWord_3063525, baseEnd_3063525] using wordTrace_append hprefix tailTrace_3063525
  have hstable : (prefixWord ++ tailWord_3063525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063525).length < 2 ^ (prefixWord ++ tailWord_3063525).sum := by decide
  have hdescent : baseEnd_3063525 < baseStart_3063525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063535 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 3, 3, 2]
def baseStart_3063535 : Nat := 118140960795 + 3063535 * 2 ^ 59
def prefixEnd_3063535 : Nat := 4983230072969 + 3 ^ 40 * 3063535 * 2
def baseEnd_3063535 : Nat := 1573065956871776638923565

theorem tailTrace_3063535 : CollatzResearch.WordTrace tailWord_3063535 prefixEnd_3063535 1573065956871776638923565 := by
  unfold tailWord_3063535
  simp only [CollatzResearch.WordTrace]
  refine ⟨111736300956343379968224059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74490867304228919978816039 111736300956343379968224059)
  ·
    refine ⟨167604451434515069952336089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111736300956343379968224059 167604451434515069952336089)
    ·
      refine ⟨125703338575886302464252067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167604451434515069952336089 125703338575886302464252067)
      ·
        refine ⟨188555007863829453696378101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125703338575886302464252067 188555007863829453696378101)
        ·
          refine ⟨17677031987234011284035447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188555007863829453696378101 17677031987234011284035447)
          ·
            refine ⟨26515547980851016926053171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17677031987234011284035447 26515547980851016926053171)
            ·
              refine ⟨39773321971276525389079757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26515547980851016926053171 39773321971276525389079757)
              ·
                refine ⟨14914995739228697020904909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39773321971276525389079757 14914995739228697020904909)
                ·
                  refine ⟨5593123402210761382839341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14914995739228697020904909 5593123402210761382839341)
                  ·
                    refine ⟨2097421275829035518564753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5593123402210761382839341 2097421275829035518564753)
                    ·
                      refine ⟨1573065956871776638923565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2097421275829035518564753 1573065956871776638923565)
                      ·
                        rfl

theorem cell23_3063535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 3, 2].length) (baseStart_3063535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063535 prefixEnd_3063535 := by exact prefixLift 3063535
  have htrace : WordTrace (prefixWord ++ tailWord_3063535) baseStart_3063535 baseEnd_3063535 := by
    simpa [prefixWord, tailWord_3063535, baseEnd_3063535] using wordTrace_append hprefix tailTrace_3063535
  have hstable : (prefixWord ++ tailWord_3063535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063535).length < 2 ^ (prefixWord ++ tailWord_3063535).sum := by decide
  have hdescent : baseEnd_3063535 < baseStart_3063535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063538 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3063538 : Nat := 118140960795 + 3063538 * 2 ^ 59
def prefixEnd_3063538 : Nat := 4983230072969 + 3 ^ 40 * 3063538 * 2
def baseEnd_3063538 : Nat := 1573067497313740127186051

theorem tailTrace_3063538 : CollatzResearch.WordTrace tailWord_3063538 prefixEnd_3063538 1573067497313740127186051 := by
  unfold tailWord_3063538
  simp only [CollatzResearch.WordTrace]
  refine ⟨27934102593833127870145817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74490940250221674320388845 27934102593833127870145817)
  ·
    refine ⟨20950576945374845902609363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27934102593833127870145817 20950576945374845902609363)
    ·
      refine ⟨31425865418062268853914045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20950576945374845902609363 31425865418062268853914045)
      ·
        refine ⟨11784699531773350820217767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31425865418062268853914045 11784699531773350820217767)
        ·
          refine ⟨17677049297660026230326651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11784699531773350820217767 17677049297660026230326651)
          ·
            refine ⟨26515573946490039345489977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17677049297660026230326651 26515573946490039345489977)
            ·
              refine ⟨19886680459867529509117483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26515573946490039345489977 19886680459867529509117483)
              ·
                refine ⟨29830020689801294263676225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19886680459867529509117483 29830020689801294263676225)
                ·
                  refine ⟨22372515517350970697757169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29830020689801294263676225 22372515517350970697757169)
                  ·
                    refine ⟨16779386638013228023317877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22372515517350970697757169 16779386638013228023317877)
                    ·
                      refine ⟨1573067497313740127186051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16779386638013228023317877 1573067497313740127186051)
                      ·
                        rfl

theorem cell23_3063538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3063538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063538 prefixEnd_3063538 := by exact prefixLift 3063538
  have htrace : WordTrace (prefixWord ++ tailWord_3063538) baseStart_3063538 baseEnd_3063538 := by
    simpa [prefixWord, tailWord_3063538, baseEnd_3063538] using wordTrace_append hprefix tailTrace_3063538
  have hstable : (prefixWord ++ tailWord_3063538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063538).length < 2 ^ (prefixWord ++ tailWord_3063538).sum := by decide
  have hdescent : baseEnd_3063538 < baseStart_3063538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063625 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 2, 5, 2]
def baseStart_3063625 : Nat := 118140960795 + 3063625 * 2 ^ 59
def prefixEnd_3063625 : Nat := 4983230072969 + 3 ^ 40 * 3063625 * 2
def baseEnd_3063625 : Nat := 1573112170130681286798151

theorem tailTrace_3063625 : CollatzResearch.WordTrace tailWord_3063625 prefixEnd_3063625 1573112170130681286798151 := by
  unfold tailWord_3063625
  simp only [CollatzResearch.WordTrace]
  refine ⟨111739583526017325339000329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74493055684011550226000219 111739583526017325339000329)
  ·
    refine ⟨83804687644512994004250247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111739583526017325339000329 83804687644512994004250247)
    ·
      refine ⟨125707031466769491006375371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83804687644512994004250247 125707031466769491006375371)
      ·
        refine ⟨188560547200154236509563057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125707031466769491006375371 188560547200154236509563057)
        ·
          refine ⟨141420410400115677382172293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188560547200154236509563057 141420410400115677382172293)
          ·
            refine ⟨26516326950021689509157305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141420410400115677382172293 26516326950021689509157305)
            ·
              refine ⟨19887245212516267131867979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26516326950021689509157305 19887245212516267131867979)
              ·
                refine ⟨29830867818774400697801969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19887245212516267131867979 29830867818774400697801969)
                ·
                  refine ⟨22373150864080800523351477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29830867818774400697801969 22373150864080800523351477)
                  ·
                    refine ⟨2097482893507575049064201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22373150864080800523351477 2097482893507575049064201)
                    ·
                      refine ⟨1573112170130681286798151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2097482893507575049064201 1573112170130681286798151)
                      ·
                        rfl

theorem cell23_3063625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 5, 2].length) (baseStart_3063625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063625 prefixEnd_3063625 := by exact prefixLift 3063625
  have htrace : WordTrace (prefixWord ++ tailWord_3063625) baseStart_3063625 baseEnd_3063625 := by
    simpa [prefixWord, tailWord_3063625, baseEnd_3063625] using wordTrace_append hprefix tailTrace_3063625
  have hstable : (prefixWord ++ tailWord_3063625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063625).length < 2 ^ (prefixWord ++ tailWord_3063625).sum := by decide
  have hdescent : baseEnd_3063625 < baseStart_3063625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063652 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_3063652 : Nat := 118140960795 + 3063652 * 2 ^ 59
def prefixEnd_3063652 : Nat := 4983230072969 + 3 ^ 40 * 3063652 * 2
def baseEnd_3063652 : Nat := 524375344702784227053509

theorem tailTrace_3063652 : CollatzResearch.WordTrace tailWord_3063652 prefixEnd_3063652 524375344702784227053509 := by
  unfold tailWord_3063652
  simp only [CollatzResearch.WordTrace]
  refine ⟨55870284148459754475116605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74493712197946339300155473 55870284148459754475116605)
  ·
    refine ⟨20951356555672407928168727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55870284148459754475116605 20951356555672407928168727)
    ·
      refine ⟨31427034833508611892253091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20951356555672407928168727 31427034833508611892253091)
      ·
        refine ⟨47140552250262917838379637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31427034833508611892253091 47140552250262917838379637)
        ·
          refine ⟨4419426773462148547348091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47140552250262917838379637 4419426773462148547348091)
          ·
            refine ⟨6629140160193222821022137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4419426773462148547348091 6629140160193222821022137)
            ·
              refine ⟨4971855120144917115766603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6629140160193222821022137 4971855120144917115766603)
              ·
                refine ⟨7457782680217375673649905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4971855120144917115766603 7457782680217375673649905)
                ·
                  refine ⟨5593337010163031755237429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7457782680217375673649905 5593337010163031755237429)
                  ·
                    refine ⟨524375344702784227053509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5593337010163031755237429 524375344702784227053509)
                    ·
                      rfl

theorem cell23_3063652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_3063652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063652 prefixEnd_3063652 := by exact prefixLift 3063652
  have htrace : WordTrace (prefixWord ++ tailWord_3063652) baseStart_3063652 baseEnd_3063652 := by
    simpa [prefixWord, tailWord_3063652, baseEnd_3063652] using wordTrace_append hprefix tailTrace_3063652
  have hstable : (prefixWord ++ tailWord_3063652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063652).length < 2 ^ (prefixWord ++ tailWord_3063652).sum := by decide
  have hdescent : baseEnd_3063652 < baseStart_3063652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063709 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_3063709 : Nat := 118140960795 + 3063709 * 2 ^ 59
def prefixEnd_3063709 : Nat := 4983230072969 + 3 ^ 40 * 3063709 * 2
def baseEnd_3063709 : Nat := 1573155302505658958147765

theorem tailTrace_3063709 : CollatzResearch.WordTrace tailWord_3063709 prefixEnd_3063709 1573155302505658958147765 := by
  unfold tailWord_3063709
  simp only [CollatzResearch.WordTrace]
  refine ⟨111742647257713007685058181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74495098171808671790038787 111742647257713007685058181)
  ·
    refine ⟨20951746360821188940948409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111742647257713007685058181 20951746360821188940948409)
    ·
      refine ⟨15713809770615891705711307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20951746360821188940948409 15713809770615891705711307)
      ·
        refine ⟨23570714655923837558566961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15713809770615891705711307 23570714655923837558566961)
        ·
          refine ⟨17678035991942878168925221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23570714655923837558566961 17678035991942878168925221)
          ·
            refine ⟨3314631748489289656673479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17678035991942878168925221 3314631748489289656673479)
            ·
              refine ⟨4971947622733934485010219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3314631748489289656673479 4971947622733934485010219)
              ·
                refine ⟨7457921434100901727515329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4971947622733934485010219 7457921434100901727515329)
                ·
                  refine ⟨5593441075575676295636497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7457921434100901727515329 5593441075575676295636497)
                  ·
                    refine ⟨4195080806681757221727373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5593441075575676295636497 4195080806681757221727373)
                    ·
                      refine ⟨1573155302505658958147765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4195080806681757221727373 1573155302505658958147765)
                      ·
                        rfl

theorem cell23_3063709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_3063709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063709 prefixEnd_3063709 := by exact prefixLift 3063709
  have htrace : WordTrace (prefixWord ++ tailWord_3063709) baseStart_3063709 baseEnd_3063709 := by
    simpa [prefixWord, tailWord_3063709, baseEnd_3063709] using wordTrace_append hprefix tailTrace_3063709
  have hstable : (prefixWord ++ tailWord_3063709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063709).length < 2 ^ (prefixWord ++ tailWord_3063709).sum := by decide
  have hdescent : baseEnd_3063709 < baseStart_3063709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063806 : List Nat := [4, 2, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_3063806 : Nat := 118140960795 + 3063806 * 2 ^ 59
def prefixEnd_3063806 : Nat := 4983230072969 + 3 ^ 40 * 3063806 * 2
def baseEnd_3063806 : Nat := 524401703376381692878273

theorem tailTrace_3063806 : CollatzResearch.WordTrace tailWord_3063806 prefixEnd_3063806 524401703376381692878273 := by
  unfold tailWord_3063806
  simp only [CollatzResearch.WordTrace]
  refine ⟨13968273142295199156417409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74497456758907728834226181 13968273142295199156417409)
  ·
    refine ⟨10476204856721399367313057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13968273142295199156417409 10476204856721399367313057)
    ·
      refine ⟨7857153642541049525484793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10476204856721399367313057 7857153642541049525484793)
      ·
        refine ⟨5892865231905787144113595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7857153642541049525484793 5892865231905787144113595)
        ·
          refine ⟨8839297847858680716170393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5892865231905787144113595 8839297847858680716170393)
          ·
            refine ⟨6629473385894010537127795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8839297847858680716170393 6629473385894010537127795)
            ·
              refine ⟨9944210078841015805691693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6629473385894010537127795 9944210078841015805691693)
              ·
                refine ⟨3729078779565380927134385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9944210078841015805691693 3729078779565380927134385)
                ·
                  refine ⟨2796809084674035695350789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3729078779565380927134385 2796809084674035695350789)
                  ·
                    refine ⟨524401703376381692878273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2796809084674035695350789 524401703376381692878273)
                    ·
                      rfl

theorem cell23_3063806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_3063806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063806 prefixEnd_3063806 := by exact prefixLift 3063806
  have htrace : WordTrace (prefixWord ++ tailWord_3063806) baseStart_3063806 baseEnd_3063806 := by
    simpa [prefixWord, tailWord_3063806, baseEnd_3063806] using wordTrace_append hprefix tailTrace_3063806
  have hstable : (prefixWord ++ tailWord_3063806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063806).length < 2 ^ (prefixWord ++ tailWord_3063806).sum := by decide
  have hdescent : baseEnd_3063806 < baseStart_3063806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063829 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_3063829 : Nat := 118140960795 + 3063829 * 2 ^ 59
def prefixEnd_3063829 : Nat := 4983230072969 + 3 ^ 40 * 3063829 * 2
def baseEnd_3063829 : Nat := 1573216920184198488647213

theorem tailTrace_3063829 : CollatzResearch.WordTrace tailWord_3063829 prefixEnd_3063829 1573216920184198488647213 := by
  unfold tailWord_3063829
  simp only [CollatzResearch.WordTrace]
  refine ⟨111747024017278268179426541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74498016011518845452951027 111747024017278268179426541)
  ·
    refine ⟨41905134006479350567284953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111747024017278268179426541 41905134006479350567284953)
    ·
      refine ⟨31428850504859512925463715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41905134006479350567284953 31428850504859512925463715)
      ·
        refine ⟨47143275757289269388195573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31428850504859512925463715 47143275757289269388195573)
        ·
          refine ⟨4419682102245869005143335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47143275757289269388195573 4419682102245869005143335)
          ·
            refine ⟨6629523153368803507715003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4419682102245869005143335 6629523153368803507715003)
            ·
              refine ⟨9944284730053205261572505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6629523153368803507715003 9944284730053205261572505)
              ·
                refine ⟨7458213547539903946179379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9944284730053205261572505 7458213547539903946179379)
                ·
                  refine ⟨11187320321309855919269069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7458213547539903946179379 11187320321309855919269069)
                  ·
                    refine ⟨4195245120491195969725901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11187320321309855919269069 4195245120491195969725901)
                    ·
                      refine ⟨1573216920184198488647213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4195245120491195969725901 1573216920184198488647213)
                      ·
                        rfl

theorem cell23_3063829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_3063829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063829 prefixEnd_3063829 := by exact prefixLift 3063829
  have htrace : WordTrace (prefixWord ++ tailWord_3063829) baseStart_3063829 baseEnd_3063829 := by
    simpa [prefixWord, tailWord_3063829, baseEnd_3063829] using wordTrace_append hprefix tailTrace_3063829
  have hstable : (prefixWord ++ tailWord_3063829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063829).length < 2 ^ (prefixWord ++ tailWord_3063829).sum := by decide
  have hdescent : baseEnd_3063829 < baseStart_3063829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063855 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 5]
def baseStart_3063855 : Nat := 118140960795 + 3063855 * 2 ^ 59
def prefixEnd_3063855 : Nat := 4983230072969 + 3 ^ 40 * 3063855 * 2
def baseEnd_3063855 : Nat := 1573230270681215386922093

theorem tailTrace_3063855 : CollatzResearch.WordTrace tailWord_3063855 prefixEnd_3063855 1573230270681215386922093 := by
  unfold tailWord_3063855
  simp only [CollatzResearch.WordTrace]
  refine ⟨111747972315184074619873019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74498648210122716413248679 111747972315184074619873019)
  ·
    refine ⟨167621958472776111929809529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111747972315184074619873019 167621958472776111929809529)
    ·
      refine ⟨125716468854582083947357147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167621958472776111929809529 125716468854582083947357147)
      ·
        refine ⟨188574703281873125921035721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125716468854582083947357147 188574703281873125921035721)
        ·
          refine ⟨141431027461404844440776791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188574703281873125921035721 141431027461404844440776791)
          ·
            refine ⟨212146541192107266661165187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141431027461404844440776791 212146541192107266661165187)
            ·
              refine ⟨318219811788160899991747781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212146541192107266661165187 318219811788160899991747781)
              ·
                refine ⟨59666214710280168748452709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 318219811788160899991747781 59666214710280168748452709)
                ·
                  refine ⟨11187415258177531640334883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59666214710280168748452709 11187415258177531640334883)
                  ·
                    refine ⟨16781122887266297460502325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11187415258177531640334883 16781122887266297460502325)
                    ·
                      refine ⟨1573230270681215386922093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16781122887266297460502325 1573230270681215386922093)
                      ·
                        rfl

theorem cell23_3063855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_3063855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063855 prefixEnd_3063855 := by exact prefixLift 3063855
  have htrace : WordTrace (prefixWord ++ tailWord_3063855) baseStart_3063855 baseEnd_3063855 := by
    simpa [prefixWord, tailWord_3063855, baseEnd_3063855] using wordTrace_append hprefix tailTrace_3063855
  have hstable : (prefixWord ++ tailWord_3063855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063855).length < 2 ^ (prefixWord ++ tailWord_3063855).sum := by decide
  have hdescent : baseEnd_3063855 < baseStart_3063855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063890 : List Nat := [3, 2, 2, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_3063890 : Nat := 118140960795 + 3063890 * 2 ^ 59
def prefixEnd_3063890 : Nat := 4983230072969 + 3 ^ 40 * 3063890 * 2
def baseEnd_3063890 : Nat := 1573248242504122749984433

theorem tailTrace_3063890 : CollatzResearch.WordTrace tailWord_3063890 prefixEnd_3063890 1573248242504122749984433 := by
  unfold tailWord_3063890
  simp only [CollatzResearch.WordTrace]
  refine ⟨27937312217514318899349281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74499499246704850398264749 27937312217514318899349281)
  ·
    refine ⟨20952984163135739174511961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27937312217514318899349281 20952984163135739174511961)
    ·
      refine ⟨15714738122351804380883971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20952984163135739174511961 15714738122351804380883971)
      ·
        refine ⟨23572107183527706571325957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15714738122351804380883971 23572107183527706571325957)
        ·
          refine ⟨4419770096911444982123617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23572107183527706571325957 4419770096911444982123617)
          ·
            refine ⟨3314827572683583736592713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4419770096911444982123617 3314827572683583736592713)
            ·
              refine ⟨2486120679512687802444535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3314827572683583736592713 2486120679512687802444535)
              ·
                refine ⟨3729181019269031703666803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486120679512687802444535 3729181019269031703666803)
                ·
                  refine ⟨5593771528903547555500205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3729181019269031703666803 5593771528903547555500205)
                  ·
                    refine ⟨2097664323338830333312577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5593771528903547555500205 2097664323338830333312577)
                    ·
                      refine ⟨1573248242504122749984433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2097664323338830333312577 1573248242504122749984433)
                      ·
                        rfl

theorem cell23_3063890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_3063890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063890 prefixEnd_3063890 := by exact prefixLift 3063890
  have htrace : WordTrace (prefixWord ++ tailWord_3063890) baseStart_3063890 baseEnd_3063890 := by
    simpa [prefixWord, tailWord_3063890, baseEnd_3063890] using wordTrace_append hprefix tailTrace_3063890
  have hstable : (prefixWord ++ tailWord_3063890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063890).length < 2 ^ (prefixWord ++ tailWord_3063890).sum := by decide
  have hdescent : baseEnd_3063890 < baseStart_3063890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063909 : List Nat := [1, 3, 1, 3, 2, 2, 2, 4, 5]
def baseStart_3063909 : Nat := 118140960795 + 3063909 * 2 ^ 59
def prefixEnd_3063909 : Nat := 4983230072969 + 3 ^ 40 * 3063909 * 2
def baseEnd_3063909 : Nat := 174806444292950908405205

theorem tailTrace_3063909 : CollatzResearch.WordTrace tailWord_3063909 prefixEnd_3063909 174806444292950908405205 := by
  unfold tailWord_3063909
  simp only [CollatzResearch.WordTrace]
  refine ⟨111749941856988441842338781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74499961237992294561559187 111749941856988441842338781)
  ·
    refine ⟨41906228196370665690877043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111749941856988441842338781 41906228196370665690877043)
    ·
      refine ⟨62859342294555998536315565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41906228196370665690877043 62859342294555998536315565)
      ·
        refine ⟨23572253360458499451118337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62859342294555998536315565 23572253360458499451118337)
        ·
          refine ⟨17679190020343874588338753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23572253360458499451118337 17679190020343874588338753)
          ·
            refine ⟨13259392515257905941254065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17679190020343874588338753 13259392515257905941254065)
            ·
              refine ⟨9944544386443429455940549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13259392515257905941254065 9944544386443429455940549)
              ·
                refine ⟨1864602072458143022988853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9944544386443429455940549 1864602072458143022988853)
                ·
                  refine ⟨174806444292950908405205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1864602072458143022988853 174806444292950908405205)
                  ·
                    rfl

theorem cell23_3063909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 5].length) (baseStart_3063909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063909 prefixEnd_3063909 := by exact prefixLift 3063909
  have htrace : WordTrace (prefixWord ++ tailWord_3063909) baseStart_3063909 baseEnd_3063909 := by
    simpa [prefixWord, tailWord_3063909, baseEnd_3063909] using wordTrace_append hprefix tailTrace_3063909
  have hstable : (prefixWord ++ tailWord_3063909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063909).length < 2 ^ (prefixWord ++ tailWord_3063909).sum := by decide
  have hdescent : baseEnd_3063909 < baseStart_3063909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063922 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_3063922 : Nat := 118140960795 + 3063922 * 2 ^ 59
def prefixEnd_3063922 : Nat := 4983230072969 + 3 ^ 40 * 3063922 * 2
def baseEnd_3063922 : Nat := 524421557961688874928095

theorem tailTrace_3063922 : CollatzResearch.WordTrace tailWord_3063922 prefixEnd_3063922 524421557961688874928095 := by
  unfold tailWord_3063922
  simp only [CollatzResearch.WordTrace]
  refine ⟨27937604001485336265640505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74500277337294230041708013 27937604001485336265640505)
  ·
    refine ⟨20953203001114002199230379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27937604001485336265640505 20953203001114002199230379)
    ·
      refine ⟨31429804501671003298845569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20953203001114002199230379 31429804501671003298845569)
      ·
        refine ⟨23572353376253252474134177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31429804501671003298845569 23572353376253252474134177)
        ·
          refine ⟨17679265032189939355600633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23572353376253252474134177 17679265032189939355600633)
          ·
            refine ⟨13259448774142454516700475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17679265032189939355600633 13259448774142454516700475)
            ·
              refine ⟨19889173161213681775050713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13259448774142454516700475 19889173161213681775050713)
              ·
                refine ⟨14916879870910261331288035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19889173161213681775050713 14916879870910261331288035)
                ·
                  refine ⟨22375319806365391996932053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14916879870910261331288035 22375319806365391996932053)
                  ·
                    refine ⟨524421557961688874928095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22375319806365391996932053 524421557961688874928095)
                    ·
                      rfl

theorem cell23_3063922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_3063922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063922 prefixEnd_3063922 := by exact prefixLift 3063922
  have htrace : WordTrace (prefixWord ++ tailWord_3063922) baseStart_3063922 baseEnd_3063922 := by
    simpa [prefixWord, tailWord_3063922, baseEnd_3063922] using wordTrace_append hprefix tailTrace_3063922
  have hstable : (prefixWord ++ tailWord_3063922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063922).length < 2 ^ (prefixWord ++ tailWord_3063922).sum := by decide
  have hdescent : baseEnd_3063922 < baseStart_3063922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063966 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_3063966 : Nat := 118140960795 + 3063966 * 2 ^ 59
def prefixEnd_3063966 : Nat := 4983230072969 + 3 ^ 40 * 3063966 * 2
def baseEnd_3063966 : Nat := 1573287267033864452634083

theorem tailTrace_3063966 : CollatzResearch.WordTrace tailWord_3063966 prefixEnd_3063966 1573287267033864452634083 := by
  unfold tailWord_3063966
  simp only [CollatzResearch.WordTrace]
  refine ⟨13969002602222742572145469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74501347211854627051442501 13969002602222742572145469)
  ·
    refine ⟨5238375975833528464554551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13969002602222742572145469 5238375975833528464554551)
    ·
      refine ⟨7857563963750292696831827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5238375975833528464554551 7857563963750292696831827)
      ·
        refine ⟨11786345945625439045247741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7857563963750292696831827 11786345945625439045247741)
        ·
          refine ⟨4419879729609539641967903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11786345945625439045247741 4419879729609539641967903)
          ·
            refine ⟨6629819594414309462951855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4419879729609539641967903 6629819594414309462951855)
            ·
              refine ⟨9944729391621464194427783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6629819594414309462951855 9944729391621464194427783)
              ·
                refine ⟨14917094087432196291641675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9944729391621464194427783 14917094087432196291641675)
                ·
                  refine ⟨22375641131148294437462513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14917094087432196291641675 22375641131148294437462513)
                  ·
                    refine ⟨16781730848361220828096885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22375641131148294437462513 16781730848361220828096885)
                    ·
                      refine ⟨1573287267033864452634083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16781730848361220828096885 1573287267033864452634083)
                      ·
                        rfl

theorem cell23_3063966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_3063966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063966 prefixEnd_3063966 := by exact prefixLift 3063966
  have htrace : WordTrace (prefixWord ++ tailWord_3063966) baseStart_3063966 baseEnd_3063966 := by
    simpa [prefixWord, tailWord_3063966, baseEnd_3063966] using wordTrace_append hprefix tailTrace_3063966
  have hstable : (prefixWord ++ tailWord_3063966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063966).length < 2 ^ (prefixWord ++ tailWord_3063966).sum := by decide
  have hdescent : baseEnd_3063966 < baseStart_3063966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064009 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 7, 1, 3]
def baseStart_3064009 : Nat := 118140960795 + 3064009 * 2 ^ 59
def prefixEnd_3064009 : Nat := 4983230072969 + 3 ^ 40 * 3064009 * 2
def baseEnd_3064009 : Nat := 1573309346702007784396385

theorem tailTrace_3064009 : CollatzResearch.WordTrace tailWord_3064009 prefixEnd_3064009 1573309346702007784396385 := by
  unfold tailWord_3064009
  simp only [CollatzResearch.WordTrace]
  refine ⟨111753589156626158920979081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74502392771084105947319387 111753589156626158920979081)
  ·
    refine ⟨83815191867469619190734311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111753589156626158920979081 83815191867469619190734311)
    ·
      refine ⟨125722787801204428786101467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83815191867469619190734311 125722787801204428786101467)
      ·
        refine ⟨188584181701806643179152201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125722787801204428786101467 188584181701806643179152201)
        ·
          refine ⟨141438136276354982384364151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188584181701806643179152201 141438136276354982384364151)
          ·
            refine ⟨212157204414532473576546227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141438136276354982384364151 212157204414532473576546227)
            ·
              refine ⟨318235806621798710364819341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212157204414532473576546227 318235806621798710364819341)
              ·
                refine ⟨119338427483174516386807253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318235806621798710364819341 119338427483174516386807253)
                ·
                  refine ⟨2796994394136902727815795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 119338427483174516386807253 2796994394136902727815795)
                  ·
                    refine ⟨4195491591205354091723693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2796994394136902727815795 4195491591205354091723693)
                    ·
                      refine ⟨1573309346702007784396385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4195491591205354091723693 1573309346702007784396385)
                      ·
                        rfl

theorem cell23_3064009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 1, 3].length) (baseStart_3064009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064009 prefixEnd_3064009 := by exact prefixLift 3064009
  have htrace : WordTrace (prefixWord ++ tailWord_3064009) baseStart_3064009 baseEnd_3064009 := by
    simpa [prefixWord, tailWord_3064009, baseEnd_3064009] using wordTrace_append hprefix tailTrace_3064009
  have hstable : (prefixWord ++ tailWord_3064009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064009).length < 2 ^ (prefixWord ++ tailWord_3064009).sum := by decide
  have hdescent : baseEnd_3064009 < baseStart_3064009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064049 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 3, 1, 4]
def baseStart_3064049 : Nat := 118140960795 + 3064049 * 2 ^ 59
def prefixEnd_3064049 : Nat := 4983230072969 + 3 ^ 40 * 3064049 * 2
def baseEnd_3064049 : Nat := 1573329885928187627896201

theorem tailTrace_3064049 : CollatzResearch.WordTrace tailWord_3064049 prefixEnd_3064049 1573329885928187627896201 := by
  unfold tailWord_3064049
  simp only [CollatzResearch.WordTrace]
  refine ⟨111755048076481245752435201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74503365384320830501623467 111755048076481245752435201)
  ·
    refine ⟨83816286057360934314326401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111755048076481245752435201 83816286057360934314326401)
    ·
      refine ⟨62862214543020700735744801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83816286057360934314326401 62862214543020700735744801)
      ·
        refine ⟨47146660907265525551808601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62862214543020700735744801 47146660907265525551808601)
        ·
          refine ⟨35359995680449144163856451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47146660907265525551808601 35359995680449144163856451)
          ·
            refine ⟨53039993520673716245784677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35359995680449144163856451 53039993520673716245784677)
            ·
              refine ⟨9944998785126321796084627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53039993520673716245784677 9944998785126321796084627)
              ·
                refine ⟨14917498177689482694126941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9944998785126321796084627 14917498177689482694126941)
                ·
                  refine ⟨5594061816633556010297603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14917498177689482694126941 5594061816633556010297603)
                  ·
                    refine ⟨8391092724950334015446405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5594061816633556010297603 8391092724950334015446405)
                    ·
                      refine ⟨1573329885928187627896201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8391092724950334015446405 1573329885928187627896201)
                      ·
                        rfl

theorem cell23_3064049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_3064049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064049 prefixEnd_3064049 := by exact prefixLift 3064049
  have htrace : WordTrace (prefixWord ++ tailWord_3064049) baseStart_3064049 baseEnd_3064049 := by
    simpa [prefixWord, tailWord_3064049, baseEnd_3064049] using wordTrace_append hprefix tailTrace_3064049
  have hstable : (prefixWord ++ tailWord_3064049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064049).length < 2 ^ (prefixWord ++ tailWord_3064049).sum := by decide
  have hdescent : baseEnd_3064049 < baseStart_3064049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064060 : List Nat := [2, 2, 2, 1, 4, 2, 2, 3, 1, 1, 3]
def baseStart_3064060 : Nat := 118140960795 + 3064060 * 2 ^ 59
def prefixEnd_3064060 : Nat := 4983230072969 + 3 ^ 40 * 3064060 * 2
def baseEnd_3064060 : Nat := 1573335534215387084858651

theorem tailTrace_3064060 : CollatzResearch.WordTrace tailWord_3064060 prefixEnd_3064060 1573335534215387084858651 := by
  unfold tailWord_3064060
  simp only [CollatzResearch.WordTrace]
  refine ⟨55877724639720697315542817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74503632852960929754057089 55877724639720697315542817)
  ·
    refine ⟨41908293479790522986657113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55877724639720697315542817 41908293479790522986657113)
    ·
      refine ⟨31431220109842892239992835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41908293479790522986657113 31431220109842892239992835)
      ·
        refine ⟨47146830164764338359989253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31431220109842892239992835 47146830164764338359989253)
        ·
          refine ⟨8840030655893313442497985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47146830164764338359989253 8840030655893313442497985)
          ·
            refine ⟨6630022991919985081873489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8840030655893313442497985 6630022991919985081873489)
            ·
              refine ⟨4972517243939988811405117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6630022991919985081873489 4972517243939988811405117)
              ·
                refine ⟨1864693966477495804276919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4972517243939988811405117 1864693966477495804276919)
                ·
                  refine ⟨2797040949716243706415379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1864693966477495804276919 2797040949716243706415379)
                  ·
                    refine ⟨4195561424574365559623069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2797040949716243706415379 4195561424574365559623069)
                    ·
                      refine ⟨1573335534215387084858651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4195561424574365559623069 1573335534215387084858651)
                      ·
                        rfl

theorem cell23_3064060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_3064060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064060 prefixEnd_3064060 := by exact prefixLift 3064060
  have htrace : WordTrace (prefixWord ++ tailWord_3064060) baseStart_3064060 baseEnd_3064060 := by
    simpa [prefixWord, tailWord_3064060, baseEnd_3064060] using wordTrace_append hprefix tailTrace_3064060
  have hstable : (prefixWord ++ tailWord_3064060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064060).length < 2 ^ (prefixWord ++ tailWord_3064060).sum := by decide
  have hdescent : baseEnd_3064060 < baseStart_3064060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064069 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 5, 2, 3]
def baseStart_3064069 : Nat := 118140960795 + 3064069 * 2 ^ 59
def prefixEnd_3064069 : Nat := 4983230072969 + 3 ^ 40 * 3064069 * 2
def baseEnd_3064069 : Nat := 1573340155541277549646109

theorem tailTrace_3064069 : CollatzResearch.WordTrace tailWord_3064069 prefixEnd_3064069 1573340155541277549646109 := by
  unfold tailWord_3064069
  simp only [CollatzResearch.WordTrace]
  refine ⟨111755777536408789168163261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74503851690939192778775507 111755777536408789168163261)
  ·
    refine ⟨41908416576153295938061223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111755777536408789168163261 41908416576153295938061223)
    ·
      refine ⟨62862624864229943907091835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41908416576153295938061223 62862624864229943907091835)
      ·
        refine ⟨94293937296344915860637753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62862624864229943907091835 94293937296344915860637753)
        ·
          refine ⟨70720452972258686895478315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94293937296344915860637753 70720452972258686895478315)
          ·
            refine ⟨106080679458388030343217473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70720452972258686895478315 106080679458388030343217473)
            ·
              refine ⟨79560509593791022757413105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106080679458388030343217473 79560509593791022757413105)
              ·
                refine ⟨59670382195343267068059829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79560509593791022757413105 59670382195343267068059829)
                ·
                  refine ⟨5594098330813431287630609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59670382195343267068059829 5594098330813431287630609)
                  ·
                    refine ⟨4195573748110073465722957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5594098330813431287630609 4195573748110073465722957)
                    ·
                      refine ⟨1573340155541277549646109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4195573748110073465722957 1573340155541277549646109)
                      ·
                        rfl

theorem cell23_3064069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_3064069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064069 prefixEnd_3064069 := by exact prefixLift 3064069
  have htrace : WordTrace (prefixWord ++ tailWord_3064069) baseStart_3064069 baseEnd_3064069 := by
    simpa [prefixWord, tailWord_3064069, baseEnd_3064069] using wordTrace_append hprefix tailTrace_3064069
  have hstable : (prefixWord ++ tailWord_3064069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064069).length < 2 ^ (prefixWord ++ tailWord_3064069).sum := by decide
  have hdescent : baseEnd_3064069 < baseStart_3064069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064093 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_3064093 : Nat := 118140960795 + 3064093 * 2 ^ 59
def prefixEnd_3064093 : Nat := 4983230072969 + 3 ^ 40 * 3064093 * 2
def baseEnd_3064093 : Nat := 524450826358995151915333

theorem tailTrace_3064093 : CollatzResearch.WordTrace tailWord_3064093 prefixEnd_3064093 524450826358995151915333 := by
  unfold tailWord_3064093
  simp only [CollatzResearch.WordTrace]
  refine ⟨111756652888321841267036933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74504435258881227511357955 111756652888321841267036933)
  ·
    refine ⟨20954372416560345237569425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111756652888321841267036933 20954372416560345237569425)
    ·
      refine ⟨15715779312420258928177069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20954372416560345237569425 15715779312420258928177069)
      ·
        refine ⟨5893417242157597098066401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15715779312420258928177069 5893417242157597098066401)
        ·
          refine ⟨4420062931618197823549801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5893417242157597098066401 4420062931618197823549801)
          ·
            refine ⟨3315047198713648367662351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4420062931618197823549801 3315047198713648367662351)
            ·
              refine ⟨4972570798070472551493527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315047198713648367662351 4972570798070472551493527)
              ·
                refine ⟨7458856197105708827240291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4972570798070472551493527 7458856197105708827240291)
                ·
                  refine ⟨11188284295658563240860437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7458856197105708827240291 11188284295658563240860437)
                  ·
                    refine ⟨524450826358995151915333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11188284295658563240860437 524450826358995151915333)
                    ·
                      rfl

theorem cell23_3064093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_3064093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064093 prefixEnd_3064093 := by exact prefixLift 3064093
  have htrace : WordTrace (prefixWord ++ tailWord_3064093) baseStart_3064093 baseEnd_3064093 := by
    simpa [prefixWord, tailWord_3064093, baseEnd_3064093] using wordTrace_append hprefix tailTrace_3064093
  have hstable : (prefixWord ++ tailWord_3064093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064093).length < 2 ^ (prefixWord ++ tailWord_3064093).sum := by decide
  have hdescent : baseEnd_3064093 < baseStart_3064093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064096 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 4]
def baseStart_3064096 : Nat := 118140960795 + 3064096 * 2 ^ 59
def prefixEnd_3064096 : Nat := 4983230072969 + 3 ^ 40 * 3064096 * 2
def baseEnd_3064096 : Nat := 1573354019518948944008485

theorem tailTrace_3064096 : CollatzResearch.WordTrace tailWord_3064096 prefixEnd_3064096 1573354019518948944008485 := by
  unfold tailWord_3064096
  simp only [CollatzResearch.WordTrace]
  refine ⟨55878381153655486389698071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74504508204873981852930761 55878381153655486389698071)
  ·
    refine ⟨83817571730483229584547107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55878381153655486389698071 83817571730483229584547107)
    ·
      refine ⟨125726357595724844376820661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83817571730483229584547107 125726357595724844376820661)
      ·
        refine ⟨11786846024599204160326937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125726357595724844376820661 11786846024599204160326937)
        ·
          refine ⟨8840134518449403120245203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11786846024599204160326937 8840134518449403120245203)
          ·
            refine ⟨13260201777674104680367805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8840134518449403120245203 13260201777674104680367805)
            ·
              refine ⟨4972575666627789255137927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13260201777674104680367805 4972575666627789255137927)
              ·
                refine ⟨7458863499941683882706891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4972575666627789255137927 7458863499941683882706891)
                ·
                  refine ⟨11188295249912525824060337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7458863499941683882706891 11188295249912525824060337)
                  ·
                    refine ⟨8391221437434394368045253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11188295249912525824060337 8391221437434394368045253)
                    ·
                      refine ⟨1573354019518948944008485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8391221437434394368045253 1573354019518948944008485)
                      ·
                        rfl

theorem cell23_3064096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_3064096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064096 prefixEnd_3064096 := by exact prefixLift 3064096
  have htrace : WordTrace (prefixWord ++ tailWord_3064096) baseStart_3064096 baseEnd_3064096 := by
    simpa [prefixWord, tailWord_3064096, baseEnd_3064096] using wordTrace_append hprefix tailTrace_3064096
  have hstable : (prefixWord ++ tailWord_3064096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064096).length < 2 ^ (prefixWord ++ tailWord_3064096).sum := by decide
  have hdescent : baseEnd_3064096 < baseStart_3064096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064106 : List Nat := [3, 1, 4, 2, 2, 1, 1, 9]
def baseStart_3064106 : Nat := 118140960795 + 3064106 * 2 ^ 59
def prefixEnd_3064106 : Nat := 4983230072969 + 3 ^ 40 * 3064106 * 2
def baseEnd_3064106 : Nat := 58272561271314589069757

theorem tailTrace_3064106 : CollatzResearch.WordTrace tailWord_3064106 prefixEnd_3064106 58272561271314589069757 := by
  unfold tailWord_3064106
  simp only [CollatzResearch.WordTrace]
  refine ⟨27939281759318686121815043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74504751358183162991506781 27939281759318686121815043)
  ·
    refine ⟨41908922638978029182722565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27939281759318686121815043 41908922638978029182722565)
    ·
      refine ⟨7857922994808380471760481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41908922638978029182722565 7857922994808380471760481)
      ·
        refine ⟨5893442246106285353820361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7857922994808380471760481 5893442246106285353820361)
        ·
          refine ⟨4420081684579714015365271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5893442246106285353820361 4420081684579714015365271)
          ·
            refine ⟨6630122526869571023047907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4420081684579714015365271 6630122526869571023047907)
            ·
              refine ⟨9945183790304356534571861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6630122526869571023047907 9945183790304356534571861)
              ·
                refine ⟨58272561271314589069757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9945183790304356534571861 58272561271314589069757)
                ·
                  rfl

theorem cell23_3064106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 9].length) (baseStart_3064106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064106 prefixEnd_3064106 := by exact prefixLift 3064106
  have htrace : WordTrace (prefixWord ++ tailWord_3064106) baseStart_3064106 baseEnd_3064106 := by
    simpa [prefixWord, tailWord_3064106, baseEnd_3064106] using wordTrace_append hprefix tailTrace_3064106
  have hstable : (prefixWord ++ tailWord_3064106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064106).length < 2 ^ (prefixWord ++ tailWord_3064106).sum := by decide
  have hdescent : baseEnd_3064106 < baseStart_3064106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064159 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 5]
def baseStart_3064159 : Nat := 118140960795 + 3064159 * 2 ^ 59
def prefixEnd_3064159 : Nat := 4983230072969 + 3 ^ 40 * 3064159 * 2
def baseEnd_3064159 : Nat := 1573386368800182197520695

theorem tailTrace_3064159 : CollatzResearch.WordTrace tailWord_3064159 prefixEnd_3064159 1573386368800182197520695 := by
  unfold tailWord_3064159
  simp only [CollatzResearch.WordTrace]
  refine ⟨111759060106082734538939531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74506040070721823025959687 111759060106082734538939531)
  ·
    refine ⟨167638590159124101808409297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111759060106082734538939531 167638590159124101808409297)
    ·
      refine ⟨125728942619343076356306973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167638590159124101808409297 125728942619343076356306973)
      ·
        refine ⟨47148353482253653633615115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125728942619343076356306973 47148353482253653633615115)
        ·
          refine ⟨70722530223380480450422673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47148353482253653633615115 70722530223380480450422673)
          ·
            refine ⟨53041897667535360337817005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70722530223380480450422673 53041897667535360337817005)
            ·
              refine ⟨19890711625325760126681377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53041897667535360337817005 19890711625325760126681377)
              ·
                refine ⟨14918033718994320095011033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19890711625325760126681377 14918033718994320095011033)
                ·
                  refine ⟨11188525289245740071258275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14918033718994320095011033 11188525289245740071258275)
                  ·
                    refine ⟨16782787933868610106887413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11188525289245740071258275 16782787933868610106887413)
                    ·
                      refine ⟨1573386368800182197520695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16782787933868610106887413 1573386368800182197520695)
                      ·
                        rfl

theorem cell23_3064159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_3064159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064159 prefixEnd_3064159 := by exact prefixLift 3064159
  have htrace : WordTrace (prefixWord ++ tailWord_3064159) baseStart_3064159 baseEnd_3064159 := by
    simpa [prefixWord, tailWord_3064159, baseEnd_3064159] using wordTrace_append hprefix tailTrace_3064159
  have hstable : (prefixWord ++ tailWord_3064159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064159).length < 2 ^ (prefixWord ++ tailWord_3064159).sum := by decide
  have hdescent : baseEnd_3064159 < baseStart_3064159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064173 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_3064173 : Nat := 118140960795 + 3064173 * 2 ^ 59
def prefixEnd_3064173 : Nat := 4983230072969 + 3 ^ 40 * 3064173 * 2
def baseEnd_3064173 : Nat := 1573393557529345142745631

theorem tailTrace_3064173 : CollatzResearch.WordTrace tailWord_3064173 prefixEnd_3064173 1573393557529345142745631 := by
  unfold tailWord_3064173
  simp only [CollatzResearch.WordTrace]
  refine ⟨111759570728032014929949173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74506380485354676619966115 111759570728032014929949173)
  ·
    refine ⟨10477459755753001399682735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111759570728032014929949173 10477459755753001399682735)
    ·
      refine ⟨15716189633629502099524103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10477459755753001399682735 15716189633629502099524103)
      ·
        refine ⟨23574284450444253149286155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15716189633629502099524103 23574284450444253149286155)
        ·
          refine ⟨35361426675666379723929233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23574284450444253149286155 35361426675666379723929233)
          ·
            refine ⟨26521070006749784792946925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35361426675666379723929233 26521070006749784792946925)
            ·
              refine ⟨9945401252531169297355097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26521070006749784792946925 9945401252531169297355097)
              ·
                refine ⟨7459050939398376973016323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9945401252531169297355097 7459050939398376973016323)
                ·
                  refine ⟨11188576409097565459524485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7459050939398376973016323 11188576409097565459524485)
                  ·
                    refine ⟨2097858076705793523660841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11188576409097565459524485 2097858076705793523660841)
                    ·
                      refine ⟨1573393557529345142745631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2097858076705793523660841 1573393557529345142745631)
                      ·
                        rfl

theorem cell23_3064173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_3064173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064173 prefixEnd_3064173 := by exact prefixLift 3064173
  have htrace : WordTrace (prefixWord ++ tailWord_3064173) baseStart_3064173 baseEnd_3064173 := by
    simpa [prefixWord, tailWord_3064173, baseEnd_3064173] using wordTrace_append hprefix tailTrace_3064173
  have hstable : (prefixWord ++ tailWord_3064173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064173).length < 2 ^ (prefixWord ++ tailWord_3064173).sum := by decide
  have hdescent : baseEnd_3064173 < baseStart_3064173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064226 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_3064226 : Nat := 118140960795 + 3064226 * 2 ^ 59
def prefixEnd_3064226 : Nat := 4983230072969 + 3 ^ 40 * 3064226 * 2
def baseEnd_3064226 : Nat := 524473590668011145127629

theorem tailTrace_3064226 : CollatzResearch.WordTrace tailWord_3064226 prefixEnd_3064226 524473590668011145127629 := by
  unfold tailWord_3064226
  simp only [CollatzResearch.WordTrace]
  refine ⟨27940375949210001245407133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74507669197893336654419021 27940375949210001245407133)
  ·
    refine ⟨10477640980953750467027675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27940375949210001245407133 10477640980953750467027675)
    ·
      refine ⟨15716461471430625700541513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10477640980953750467027675 15716461471430625700541513)
      ·
        refine ⟨11787346103572969275406135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15716461471430625700541513 11787346103572969275406135)
        ·
          refine ⟨17681019155359453913109203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11787346103572969275406135 17681019155359453913109203)
          ·
            refine ⟨26521528733039180869663805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17681019155359453913109203 26521528733039180869663805)
            ·
              refine ⟨9945573274889692826123927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26521528733039180869663805 9945573274889692826123927)
              ·
                refine ⟨14918359912334539239185891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9945573274889692826123927 14918359912334539239185891)
                ·
                  refine ⟨22377539868501808858778837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14918359912334539239185891 22377539868501808858778837)
                  ·
                    refine ⟨524473590668011145127629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22377539868501808858778837 524473590668011145127629)
                    ·
                      rfl

theorem cell23_3064226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_3064226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064226 prefixEnd_3064226 := by exact prefixLift 3064226
  have htrace : WordTrace (prefixWord ++ tailWord_3064226) baseStart_3064226 baseEnd_3064226 := by
    simpa [prefixWord, tailWord_3064226, baseEnd_3064226] using wordTrace_append hprefix tailTrace_3064226
  have hstable : (prefixWord ++ tailWord_3064226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064226).length < 2 ^ (prefixWord ++ tailWord_3064226).sum := by decide
  have hdescent : baseEnd_3064226 < baseStart_3064226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064259 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 6]
def baseStart_3064259 : Nat := 118140960795 + 3064259 * 2 ^ 59
def prefixEnd_3064259 : Nat := 4983230072969 + 3 ^ 40 * 3064259 * 2
def baseEnd_3064259 : Nat := 1573437716865631806270235

theorem tailTrace_3064259 : CollatzResearch.WordTrace tailWord_3064259 prefixEnd_3064259 1573437716865631806270235 := by
  unfold tailWord_3064259
  simp only [CollatzResearch.WordTrace]
  refine ⟨111762707405720451617579831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74508471603813634411719887 111762707405720451617579831)
  ·
    refine ⟨167644061108580677426369747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111762707405720451617579831 167644061108580677426369747)
    ·
      refine ⟨251466091662871016139554621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167644061108580677426369747 251466091662871016139554621)
      ·
        refine ⟨94299784373576631052332983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251466091662871016139554621 94299784373576631052332983)
        ·
          refine ⟨141449676560364946578499475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94299784373576631052332983 141449676560364946578499475)
          ·
            refine ⟨212174514840547419867749213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141449676560364946578499475 212174514840547419867749213)
            ·
              refine ⟨79565443065205282450405955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212174514840547419867749213 79565443065205282450405955)
              ·
                refine ⟨119348164597807923675608933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79565443065205282450405955 119348164597807923675608933)
                ·
                  refine ⟨22377780862088985689176675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119348164597807923675608933 22377780862088985689176675)
                  ·
                    refine ⟨33566671293133478533765013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22377780862088985689176675 33566671293133478533765013)
                    ·
                      refine ⟨1573437716865631806270235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33566671293133478533765013 1573437716865631806270235)
                      ·
                        rfl

theorem cell23_3064259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_3064259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064259 prefixEnd_3064259 := by exact prefixLift 3064259
  have htrace : WordTrace (prefixWord ++ tailWord_3064259) baseStart_3064259 baseEnd_3064259 := by
    simpa [prefixWord, tailWord_3064259, baseEnd_3064259] using wordTrace_append hprefix tailTrace_3064259
  have hstable : (prefixWord ++ tailWord_3064259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064259).length < 2 ^ (prefixWord ++ tailWord_3064259).sum := by decide
  have hdescent : baseEnd_3064259 < baseStart_3064259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064263 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 2, 4, 2]
def baseStart_3064263 : Nat := 118140960795 + 3064263 * 2 ^ 59
def prefixEnd_3064263 : Nat := 4983230072969 + 3 ^ 40 * 3064263 * 2
def baseEnd_3064263 : Nat := 1573439770788249790620217

theorem tailTrace_3064263 : CollatzResearch.WordTrace tailWord_3064263 prefixEnd_3064263 1573439770788249790620217 := by
  unfold tailWord_3064263
  simp only [CollatzResearch.WordTrace]
  refine ⟨111762853297705960300725443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74508568865137306867150295 111762853297705960300725443)
  ·
    refine ⟨167644279946558940451088165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111762853297705960300725443 167644279946558940451088165)
    ·
      refine ⟨31433302489979801334579031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167644279946558940451088165 31433302489979801334579031)
      ·
        refine ⟨47149953734969702001868547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31433302489979801334579031 47149953734969702001868547)
        ·
          refine ⟨70724930602454553002802821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47149953734969702001868547 70724930602454553002802821)
          ·
            refine ⟨13260924487960228688025529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70724930602454553002802821 13260924487960228688025529)
            ·
              refine ⟨9945693365970171516019147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13260924487960228688025529 9945693365970171516019147)
              ·
                refine ⟨14918540048955257274028721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9945693365970171516019147 14918540048955257274028721)
                ·
                  refine ⟨11188905036716442955521541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14918540048955257274028721 11188905036716442955521541)
                  ·
                    refine ⟨2097919694384333054160289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11188905036716442955521541 2097919694384333054160289)
                    ·
                      refine ⟨1573439770788249790620217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2097919694384333054160289 1573439770788249790620217)
                      ·
                        rfl

theorem cell23_3064263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_3064263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064263 prefixEnd_3064263 := by exact prefixLift 3064263
  have htrace : WordTrace (prefixWord ++ tailWord_3064263) baseStart_3064263 baseEnd_3064263 := by
    simpa [prefixWord, tailWord_3064263, baseEnd_3064263] using wordTrace_append hprefix tailTrace_3064263
  have hstable : (prefixWord ++ tailWord_3064263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064263).length < 2 ^ (prefixWord ++ tailWord_3064263).sum := by decide
  have hdescent : baseEnd_3064263 < baseStart_3064263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064266 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_3064266 : Nat := 118140960795 + 3064266 * 2 ^ 59
def prefixEnd_3064266 : Nat := 4983230072969 + 3 ^ 40 * 3064266 * 2
def baseEnd_3064266 : Nat := 1573441311230213278882703

theorem tailTrace_3064266 : CollatzResearch.WordTrace tailWord_3064266 prefixEnd_3064266 1573441311230213278882703 := by
  unfold tailWord_3064266
  simp only [CollatzResearch.WordTrace]
  refine ⟨27940740679173772953271163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74508641811130061208723101 27940740679173772953271163)
  ·
    refine ⟨41911111018760659429906745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27940740679173772953271163 41911111018760659429906745)
    ·
      refine ⟨31433333264070494572430059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41911111018760659429906745 31433333264070494572430059)
      ·
        refine ⟨47149999896105741858645089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31433333264070494572430059 47149999896105741858645089)
        ·
          refine ⟨35362499922079306393983817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47149999896105741858645089 35362499922079306393983817)
          ·
            refine ⟨26521874941559479795487863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35362499922079306393983817 26521874941559479795487863)
            ·
              refine ⟨39782812412339219693231795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26521874941559479795487863 39782812412339219693231795)
              ·
                refine ⟨59674218618508829539847693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39782812412339219693231795 59674218618508829539847693)
                ·
                  refine ⟨22377831981940811077442885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59674218618508829539847693 22377831981940811077442885)
                  ·
                    refine ⟨4195843496613902077020541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22377831981940811077442885 4195843496613902077020541)
                    ·
                      refine ⟨1573441311230213278882703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4195843496613902077020541 1573441311230213278882703)
                      ·
                        rfl

theorem cell23_3064266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_3064266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064266 prefixEnd_3064266 := by exact prefixLift 3064266
  have htrace : WordTrace (prefixWord ++ tailWord_3064266) baseStart_3064266 baseEnd_3064266 := by
    simpa [prefixWord, tailWord_3064266, baseEnd_3064266] using wordTrace_append hprefix tailTrace_3064266
  have hstable : (prefixWord ++ tailWord_3064266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064266).length < 2 ^ (prefixWord ++ tailWord_3064266).sum := by decide
  have hdescent : baseEnd_3064266 < baseStart_3064266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064279 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_3064279 : Nat := 118140960795 + 3064279 * 2 ^ 59
def prefixEnd_3064279 : Nat := 4983230072969 + 3 ^ 40 * 3064279 * 2
def baseEnd_3064279 : Nat := 1573447986478721728020143

theorem tailTrace_3064279 : CollatzResearch.WordTrace tailWord_3064279 prefixEnd_3064279 1573447986478721728020143 := by
  unfold tailWord_3064279
  simp only [CollatzResearch.WordTrace]
  refine ⟨111763436865647995033307891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74508957910431996688871927 111763436865647995033307891)
  ·
    refine ⟨167645155298471992549961837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111763436865647995033307891 167645155298471992549961837)
    ·
      refine ⟨62866933236926997206235689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167645155298471992549961837 62866933236926997206235689)
      ·
        refine ⟨47150199927695247904676767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62866933236926997206235689 47150199927695247904676767)
        ·
          refine ⟨70725299891542871857015151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47150199927695247904676767 70725299891542871857015151)
          ·
            refine ⟨106087949837314307785522727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70725299891542871857015151 106087949837314307785522727)
            ·
              refine ⟨159131924755971461678284091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106087949837314307785522727 159131924755971461678284091)
              ·
                refine ⟨238697887133957192517426137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159131924755971461678284091 238697887133957192517426137)
                ·
                  refine ⟨179023415350467894388069603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238697887133957192517426137 179023415350467894388069603)
                  ·
                    refine ⟨268535123025701841582104405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 179023415350467894388069603 268535123025701841582104405)
                    ·
                      refine ⟨1573447986478721728020143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 268535123025701841582104405 1573447986478721728020143)
                      ·
                        rfl

theorem cell23_3064279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_3064279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064279 prefixEnd_3064279 := by exact prefixLift 3064279
  have htrace : WordTrace (prefixWord ++ tailWord_3064279) baseStart_3064279 baseEnd_3064279 := by
    simpa [prefixWord, tailWord_3064279, baseEnd_3064279] using wordTrace_append hprefix tailTrace_3064279
  have hstable : (prefixWord ++ tailWord_3064279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064279).length < 2 ^ (prefixWord ++ tailWord_3064279).sum := by decide
  have hdescent : baseEnd_3064279 < baseStart_3064279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064316 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 3, 5]
def baseStart_3064316 : Nat := 118140960795 + 3064316 * 2 ^ 59
def prefixEnd_3064316 : Nat := 4983230072969 + 3 ^ 40 * 3064316 * 2
def baseEnd_3064316 : Nat := 524488995087646027752491

theorem tailTrace_3064316 : CollatzResearch.WordTrace tailWord_3064316 prefixEnd_3064316 524488995087646027752491 := by
  unfold tailWord_3064316
  simp only [CollatzResearch.WordTrace]
  refine ⟨55882393183256975176202401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74509857577675966901603201 55882393183256975176202401)
  ·
    refine ⟨41911794887442731382151801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55882393183256975176202401 41911794887442731382151801)
    ·
      refine ⟨31433846165582048536613851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41911794887442731382151801 31433846165582048536613851)
      ·
        refine ⟨47150769248373072804920777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31433846165582048536613851 47150769248373072804920777)
        ·
          refine ⟨35363076936279804603690583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47150769248373072804920777 35363076936279804603690583)
          ·
            refine ⟨53044615404419706905535875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35363076936279804603690583 53044615404419706905535875)
            ·
              refine ⟨79566923106629560358303813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53044615404419706905535875 79566923106629560358303813)
              ·
                refine ⟨14918798082493042567181965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79566923106629560358303813 14918798082493042567181965)
                ·
                  refine ⟨5594549280934890962693237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14918798082493042567181965 5594549280934890962693237)
                  ·
                    refine ⟨524488995087646027752491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5594549280934890962693237 524488995087646027752491)
                    ·
                      rfl

theorem cell23_3064316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_3064316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064316 prefixEnd_3064316 := by exact prefixLift 3064316
  have htrace : WordTrace (prefixWord ++ tailWord_3064316) baseStart_3064316 baseEnd_3064316 := by
    simpa [prefixWord, tailWord_3064316, baseEnd_3064316] using wordTrace_append hprefix tailTrace_3064316
  have hstable : (prefixWord ++ tailWord_3064316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064316).length < 2 ^ (prefixWord ++ tailWord_3064316).sum := by decide
  have hdescent : baseEnd_3064316 < baseStart_3064316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064323 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 4, 3, 2]
def baseStart_3064323 : Nat := 118140960795 + 3064323 * 2 ^ 59
def prefixEnd_3064323 : Nat := 4983230072969 + 3 ^ 40 * 3064323 * 2
def baseEnd_3064323 : Nat := 1573470579627519555869941

theorem tailTrace_3064323 : CollatzResearch.WordTrace tailWord_3064323 prefixEnd_3064323 1573470579627519555869941 := by
  unfold tailWord_3064323
  simp only [CollatzResearch.WordTrace]
  refine ⟨111765041677488590547909623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74510027784992393698606415 111765041677488590547909623)
  ·
    refine ⟨167647562516232885821864435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111765041677488590547909623 167647562516232885821864435)
    ·
      refine ⟨251471343774349328732796653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167647562516232885821864435 251471343774349328732796653)
      ·
        refine ⟨94301753915380998274798745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251471343774349328732796653 94301753915380998274798745)
        ·
          refine ⟨70726315436535748706099059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94301753915380998274798745 70726315436535748706099059)
          ·
            refine ⟨106089473154803623059148589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70726315436535748706099059 106089473154803623059148589)
            ·
              refine ⟨39783552433051358647180721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106089473154803623059148589 39783552433051358647180721)
              ·
                refine ⟨29837664324788518985385541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39783552433051358647180721 29837664324788518985385541)
                ·
                  refine ⟨5594562060897847309759789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29837664324788518985385541 5594562060897847309759789)
                  ·
                    refine ⟨2097960772836692741159921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5594562060897847309759789 2097960772836692741159921)
                    ·
                      refine ⟨1573470579627519555869941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2097960772836692741159921 1573470579627519555869941)
                      ·
                        rfl

theorem cell23_3064323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 3, 2].length) (baseStart_3064323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064323 prefixEnd_3064323 := by exact prefixLift 3064323
  have htrace : WordTrace (prefixWord ++ tailWord_3064323) baseStart_3064323 baseEnd_3064323 := by
    simpa [prefixWord, tailWord_3064323, baseEnd_3064323] using wordTrace_append hprefix tailTrace_3064323
  have hstable : (prefixWord ++ tailWord_3064323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064323).length < 2 ^ (prefixWord ++ tailWord_3064323).sum := by decide
  have hdescent : baseEnd_3064323 < baseStart_3064323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064346 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 3, 6]
def baseStart_3064346 : Nat := 118140960795 + 3064346 * 2 ^ 59
def prefixEnd_3064346 : Nat := 4983230072969 + 3 ^ 40 * 3064346 * 2
def baseEnd_3064346 : Nat := 524494129894190988627445

theorem tailTrace_3064346 : CollatzResearch.WordTrace tailWord_3064346 prefixEnd_3064346 524494129894190988627445 := by
  unfold tailWord_3064346
  simp only [CollatzResearch.WordTrace]
  refine ⟨27941470139101316368999223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74510587037603510317331261 27941470139101316368999223)
  ·
    refine ⟨41912205208651974553498835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27941470139101316368999223 41912205208651974553498835)
    ·
      refine ⟨62868307812977961830248253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41912205208651974553498835 62868307812977961830248253)
      ·
        refine ⟨23575615429866735686343095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62868307812977961830248253 23575615429866735686343095)
        ·
          refine ⟨35363423144800103529514643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23575615429866735686343095 35363423144800103529514643)
          ·
            refine ⟨53045134717200155294271965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35363423144800103529514643 53045134717200155294271965)
            ·
              refine ⟨19891925518950058235351987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53045134717200155294271965 19891925518950058235351987)
              ·
                refine ⟨29837888278425087353027981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19891925518950058235351987 29837888278425087353027981)
                ·
                  refine ⟨11189208104409407757385493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29837888278425087353027981 11189208104409407757385493)
                  ·
                    refine ⟨524494129894190988627445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11189208104409407757385493 524494129894190988627445)
                    ·
                      rfl

theorem cell23_3064346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_3064346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064346 prefixEnd_3064346 := by exact prefixLift 3064346
  have htrace : WordTrace (prefixWord ++ tailWord_3064346) baseStart_3064346 baseEnd_3064346 := by
    simpa [prefixWord, tailWord_3064346, baseEnd_3064346] using wordTrace_append hprefix tailTrace_3064346
  have hstable : (prefixWord ++ tailWord_3064346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064346).length < 2 ^ (prefixWord ++ tailWord_3064346).sum := by decide
  have hdescent : baseEnd_3064346 < baseStart_3064346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064373 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_3064373 : Nat := 118140960795 + 3064373 * 2 ^ 59
def prefixEnd_3064373 : Nat := 4983230072969 + 3 ^ 40 * 3064373 * 2
def baseEnd_3064373 : Nat := 1573496253660244360244711

theorem tailTrace_3064373 : CollatzResearch.WordTrace tailWord_3064373 prefixEnd_3064373 1573496253660244360244711 := by
  unfold tailWord_3064373
  simp only [CollatzResearch.WordTrace]
  refine ⟨111766865327307449087229773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74511243551538299391486515 111766865327307449087229773)
  ·
    refine ⟨41912574497740293407711165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111766865327307449087229773 41912574497740293407711165)
    ·
      refine ⟨15717215436652610027891687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41912574497740293407711165 15717215436652610027891687)
      ·
        refine ⟨23575823154978915041837531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15717215436652610027891687 23575823154978915041837531)
        ·
          refine ⟨35363734732468372562756297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23575823154978915041837531 35363734732468372562756297)
          ·
            refine ⟨26522801049351279422067223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35363734732468372562756297 26522801049351279422067223)
            ·
              refine ⟨39784201574026919133100835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26522801049351279422067223 39784201574026919133100835)
              ·
                refine ⟨59676302361040378699651253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39784201574026919133100835 59676302361040378699651253)
                ·
                  refine ⟨5594653346347535503092305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59676302361040378699651253 5594653346347535503092305)
                  ·
                    refine ⟨4195990009760651627319229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5594653346347535503092305 4195990009760651627319229)
                    ·
                      refine ⟨1573496253660244360244711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4195990009760651627319229 1573496253660244360244711)
                      ·
                        rfl

theorem cell23_3064373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_3064373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064373 prefixEnd_3064373 := by exact prefixLift 3064373
  have htrace : WordTrace (prefixWord ++ tailWord_3064373) baseStart_3064373 baseEnd_3064373 := by
    simpa [prefixWord, tailWord_3064373, baseEnd_3064373] using wordTrace_append hprefix tailTrace_3064373
  have hstable : (prefixWord ++ tailWord_3064373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064373).length < 2 ^ (prefixWord ++ tailWord_3064373).sum := by decide
  have hdescent : baseEnd_3064373 < baseStart_3064373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064380 : List Nat := [2, 2, 2, 2, 3, 1, 2, 3, 2, 4]
def baseStart_3064380 : Nat := 118140960795 + 3064380 * 2 ^ 59
def prefixEnd_3064380 : Nat := 4983230072969 + 3 ^ 40 * 3064380 * 2
def baseEnd_3064380 : Nat := 524499949341608610952393

theorem tailTrace_3064380 : CollatzResearch.WordTrace tailWord_3064380 prefixEnd_3064380 524499949341608610952393 := by
  unfold tailWord_3064380
  simp only [CollatzResearch.WordTrace]
  refine ⟨55883560319141044641367297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74511413758854726188489729 55883560319141044641367297)
  ·
    refine ⟨41912670239355783481025473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55883560319141044641367297 41912670239355783481025473)
    ·
      refine ⟨31434502679516837610769105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41912670239355783481025473 31434502679516837610769105)
      ·
        refine ⟨23575877009637628208076829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31434502679516837610769105 23575877009637628208076829)
        ·
          refine ⟨8840953878614110578028811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23575877009637628208076829 8840953878614110578028811)
          ·
            refine ⟨13261430817921165867043217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8840953878614110578028811 13261430817921165867043217)
            ·
              refine ⟨9946073113440874400282413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13261430817921165867043217 9946073113440874400282413)
              ·
                refine ⟨3729777417540327900105905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9946073113440874400282413 3729777417540327900105905)
                ·
                  refine ⟨2797333063155245925079429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3729777417540327900105905 2797333063155245925079429)
                  ·
                    refine ⟨524499949341608610952393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2797333063155245925079429 524499949341608610952393)
                    ·
                      rfl

theorem cell23_3064380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_3064380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064380 prefixEnd_3064380 := by exact prefixLift 3064380
  have htrace : WordTrace (prefixWord ++ tailWord_3064380) baseStart_3064380 baseEnd_3064380 := by
    simpa [prefixWord, tailWord_3064380, baseEnd_3064380] using wordTrace_append hprefix tailTrace_3064380
  have hstable : (prefixWord ++ tailWord_3064380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064380).length < 2 ^ (prefixWord ++ tailWord_3064380).sum := by decide
  have hdescent : baseEnd_3064380 < baseStart_3064380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064383 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 4]
def baseStart_3064383 : Nat := 118140960795 + 3064383 * 2 ^ 59
def prefixEnd_3064383 : Nat := 4983230072969 + 3 ^ 40 * 3064383 * 2
def baseEnd_3064383 : Nat := 1573501388466789321119665

theorem tailTrace_3064383 : CollatzResearch.WordTrace tailWord_3064383 prefixEnd_3064383 1573501388466789321119665 := by
  unfold tailWord_3064383
  simp only [CollatzResearch.WordTrace]
  refine ⟨111767230057271220795093803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74511486704847480530062535 111767230057271220795093803)
  ·
    refine ⟨167650845085906831192640705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111767230057271220795093803 167650845085906831192640705)
    ·
      refine ⟨125738133814430123394480529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167650845085906831192640705 125738133814430123394480529)
      ·
        refine ⟨94303600360822592545860397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125738133814430123394480529 94303600360822592545860397)
        ·
          refine ⟨35363850135308472204697649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94303600360822592545860397 35363850135308472204697649)
          ·
            refine ⟨26522887601481354153523237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35363850135308472204697649 26522887601481354153523237)
            ·
              refine ⟨4973041425277753903785607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26522887601481354153523237 4973041425277753903785607)
              ·
                refine ⟨7459562137916630855678411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4973041425277753903785607 7459562137916630855678411)
                ·
                  refine ⟨11189343206874946283517617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7459562137916630855678411 11189343206874946283517617)
                  ·
                    refine ⟨8392007405156209712638213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11189343206874946283517617 8392007405156209712638213)
                    ·
                      refine ⟨1573501388466789321119665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8392007405156209712638213 1573501388466789321119665)
                      ·
                        rfl

theorem cell23_3064383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_3064383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064383 prefixEnd_3064383 := by exact prefixLift 3064383
  have htrace : WordTrace (prefixWord ++ tailWord_3064383) baseStart_3064383 baseEnd_3064383 := by
    simpa [prefixWord, tailWord_3064383, baseEnd_3064383] using wordTrace_append hprefix tailTrace_3064383
  have hstable : (prefixWord ++ tailWord_3064383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064383).length < 2 ^ (prefixWord ++ tailWord_3064383).sum := by decide
  have hdescent : baseEnd_3064383 < baseStart_3064383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064404 : List Nat := [2, 4, 1, 1, 1, 3, 1, 5, 1, 2, 2]
def baseStart_3064404 : Nat := 118140960795 + 3064404 * 2 ^ 59
def prefixEnd_3064404 : Nat := 4983230072969 + 3 ^ 40 * 3064404 * 2
def baseEnd_3064404 : Nat := 1573512171560533738957069

theorem tailTrace_3064404 : CollatzResearch.WordTrace tailWord_3064404 prefixEnd_3064404 1573512171560533738957069 := by
  unfold tailWord_3064404
  simp only [CollatzResearch.WordTrace]
  refine ⟨55883997995097570690804133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74511997326796760921072177 55883997995097570690804133)
  ·
    refine ⟨10478249624080794504525775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55883997995097570690804133 10478249624080794504525775)
    ·
      refine ⟨15717374436121191756788663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10478249624080794504525775 15717374436121191756788663)
      ·
        refine ⟨23576061654181787635182995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15717374436121191756788663 23576061654181787635182995)
        ·
          refine ⟨35364092481272681452774493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23576061654181787635182995 35364092481272681452774493)
          ·
            refine ⟨13261534680477255544790435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35364092481272681452774493 13261534680477255544790435)
            ·
              refine ⟨19892302020715883317185653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13261534680477255544790435 19892302020715883317185653)
              ·
                refine ⟨1864903314442114060986155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19892302020715883317185653 1864903314442114060986155)
                ·
                  refine ⟨2797354971663171091479233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1864903314442114060986155 2797354971663171091479233)
                  ·
                    refine ⟨2098016228747378318609425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2797354971663171091479233 2098016228747378318609425)
                    ·
                      refine ⟨1573512171560533738957069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2098016228747378318609425 1573512171560533738957069)
                      ·
                        rfl

theorem cell23_3064404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_3064404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064404 prefixEnd_3064404 := by exact prefixLift 3064404
  have htrace : WordTrace (prefixWord ++ tailWord_3064404) baseStart_3064404 baseEnd_3064404 := by
    simpa [prefixWord, tailWord_3064404, baseEnd_3064404] using wordTrace_append hprefix tailTrace_3064404
  have hstable : (prefixWord ++ tailWord_3064404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064404).length < 2 ^ (prefixWord ++ tailWord_3064404).sum := by decide
  have hdescent : baseEnd_3064404 < baseStart_3064404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064420 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 4, 1, 3]
def baseStart_3064420 : Nat := 118140960795 + 3064420 * 2 ^ 59
def prefixEnd_3064420 : Nat := 4983230072969 + 3 ^ 40 * 3064420 * 2
def baseEnd_3064420 : Nat := 1573520387251005676356995

theorem tailTrace_3064420 : CollatzResearch.WordTrace tailWord_3064420 prefixEnd_3064420 1573520387251005676356995 := by
  unfold tailWord_3064420
  simp only [CollatzResearch.WordTrace]
  refine ⟨55884289779068588057095357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74512386372091450742793809 55884289779068588057095357)
  ·
    refine ⟨20956608667150720521410759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55884289779068588057095357 20956608667150720521410759)
    ·
      refine ⟨31434913000726080782116139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20956608667150720521410759 31434913000726080782116139)
      ·
        refine ⟨47152369501089121173174209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31434913000726080782116139 47152369501089121173174209)
        ·
          refine ⟨35364277125816840879880657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47152369501089121173174209 35364277125816840879880657)
          ·
            refine ⟨26523207844362630659910493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35364277125816840879880657 26523207844362630659910493)
            ·
              refine ⟨9946202941635986497466435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26523207844362630659910493 9946202941635986497466435)
              ·
                refine ⟨14919304412453979746199653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9946202941635986497466435 14919304412453979746199653)
                ·
                  refine ⟨2797369577335121202412435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14919304412453979746199653 2797369577335121202412435)
                  ·
                    refine ⟨4196054366002681803618653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2797369577335121202412435 4196054366002681803618653)
                    ·
                      refine ⟨1573520387251005676356995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4196054366002681803618653 1573520387251005676356995)
                      ·
                        rfl

theorem cell23_3064420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_3064420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064420 prefixEnd_3064420 := by exact prefixLift 3064420
  have htrace : WordTrace (prefixWord ++ tailWord_3064420) baseStart_3064420 baseEnd_3064420 := by
    simpa [prefixWord, tailWord_3064420, baseEnd_3064420] using wordTrace_append hprefix tailTrace_3064420
  have hstable : (prefixWord ++ tailWord_3064420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064420).length < 2 ^ (prefixWord ++ tailWord_3064420).sum := by decide
  have hdescent : baseEnd_3064420 < baseStart_3064420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064477 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_3064477 : Nat := 118140960795 + 3064477 * 2 ^ 59
def prefixEnd_3064477 : Nat := 4983230072969 + 3 ^ 40 * 3064477 * 2
def baseEnd_3064477 : Nat := 1573549655648311953344233

theorem tailTrace_3064477 : CollatzResearch.WordTrace tailWord_3064477 prefixEnd_3064477 1573549655648311953344233 := by
  unfold tailWord_3064477
  simp only [CollatzResearch.WordTrace]
  refine ⟨111770658518930674849015685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74513772345953783232677123 111770658518930674849015685)
  ·
    refine ⟨20956998472299501534190441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111770658518930674849015685 20956998472299501534190441)
    ·
      refine ⟨15717748854224626150642831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20956998472299501534190441 15717748854224626150642831)
      ·
        refine ⟨23576623281336939225964247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15717748854224626150642831 23576623281336939225964247)
        ·
          refine ⟨35364934922005408838946371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23576623281336939225964247 35364934922005408838946371)
          ·
            refine ⟨53047402383008113258419557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35364934922005408838946371 53047402383008113258419557)
            ·
              refine ⟨9946387946814021235953667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53047402383008113258419557 9946387946814021235953667)
              ·
                refine ⟨14919581920221031853930501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9946387946814021235953667 14919581920221031853930501)
                ·
                  refine ⟨2797421610041443472611969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14919581920221031853930501 2797421610041443472611969)
                  ·
                    refine ⟨2098066207531082604458977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2797421610041443472611969 2098066207531082604458977)
                    ·
                      refine ⟨1573549655648311953344233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2098066207531082604458977 1573549655648311953344233)
                      ·
                        rfl

theorem cell23_3064477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_3064477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064477 prefixEnd_3064477 := by exact prefixLift 3064477
  have htrace : WordTrace (prefixWord ++ tailWord_3064477) baseStart_3064477 baseEnd_3064477 := by
    simpa [prefixWord, tailWord_3064477, baseEnd_3064477] using wordTrace_append hprefix tailTrace_3064477
  have hstable : (prefixWord ++ tailWord_3064477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064477).length < 2 ^ (prefixWord ++ tailWord_3064477).sum := by decide
  have hdescent : baseEnd_3064477 < baseStart_3064477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064560 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 3, 4]
def baseStart_3064560 : Nat := 118140960795 + 3064560 * 2 ^ 59
def prefixEnd_3064560 : Nat := 4983230072969 + 3 ^ 40 * 3064560 * 2
def baseEnd_3064560 : Nat := 524530758180878376202117

theorem tailTrace_3064560 : CollatzResearch.WordTrace tailWord_3064560 prefixEnd_3064560 524530758180878376202117 := by
  unfold tailWord_3064560
  simp only [CollatzResearch.WordTrace]
  refine ⟨55886842888814990012143567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74515790518419986682858089 55886842888814990012143567)
  ·
    refine ⟨83830264333222485018215351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55886842888814990012143567 83830264333222485018215351)
    ·
      refine ⟨125745396499833727527323027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83830264333222485018215351 125745396499833727527323027)
      ·
        refine ⟨188618094749750591290984541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125745396499833727527323027 188618094749750591290984541)
        ·
          refine ⟨70731785531156471734119203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188618094749750591290984541 70731785531156471734119203)
          ·
            refine ⟨106097678296734707601178805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70731785531156471734119203 106097678296734707601178805)
            ·
              refine ⟨9946657340318878837610513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106097678296734707601178805 9946657340318878837610513)
              ·
                refine ⟨7459993005239159128207885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9946657340318878837610513 7459993005239159128207885)
                ·
                  refine ⟨2797497376964684673077957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7459993005239159128207885 2797497376964684673077957)
                  ·
                    refine ⟨524530758180878376202117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2797497376964684673077957 524530758180878376202117)
                    ·
                      rfl

theorem cell23_3064560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 3, 4].length) (baseStart_3064560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064560 prefixEnd_3064560 := by exact prefixLift 3064560
  have htrace : WordTrace (prefixWord ++ tailWord_3064560) baseStart_3064560 baseEnd_3064560 := by
    simpa [prefixWord, tailWord_3064560, baseEnd_3064560] using wordTrace_append hprefix tailTrace_3064560
  have hstable : (prefixWord ++ tailWord_3064560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064560).length < 2 ^ (prefixWord ++ tailWord_3064560).sum := by decide
  have hdescent : baseEnd_3064560 < baseStart_3064560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064564 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3064564 : Nat := 118140960795 + 3064564 * 2 ^ 59
def prefixEnd_3064564 : Nat := 4983230072969 + 3 ^ 40 * 3064564 * 2
def baseEnd_3064564 : Nat := 524531442821751037652111

theorem tailTrace_3064564 : CollatzResearch.WordTrace tailWord_3064564 prefixEnd_3064564 524531442821751037652111 := by
  unfold tailWord_3064564
  simp only [CollatzResearch.WordTrace]
  refine ⟨55886915834807744353716373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74515887779743659138288497 55886915834807744353716373)
  ·
    refine ⟨2619699179756613016580455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55886915834807744353716373 2619699179756613016580455)
    ·
      refine ⟨3929548769634919524870683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2619699179756613016580455 3929548769634919524870683)
      ·
        refine ⟨5894323154452379287306025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929548769634919524870683 5894323154452379287306025)
        ·
          refine ⟨4420742365839284465479519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5894323154452379287306025 4420742365839284465479519)
          ·
            refine ⟨6631113548758926698219279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4420742365839284465479519 6631113548758926698219279)
            ·
              refine ⟨9946670323138390047328919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6631113548758926698219279 9946670323138390047328919)
              ·
                refine ⟨14920005484707585070993379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9946670323138390047328919 14920005484707585070993379)
                ·
                  refine ⟨22380008227061377606490069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14920005484707585070993379 22380008227061377606490069)
                  ·
                    refine ⟨524531442821751037652111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22380008227061377606490069 524531442821751037652111)
                    ·
                      rfl

theorem cell23_3064564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3064564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064564 prefixEnd_3064564 := by exact prefixLift 3064564
  have htrace : WordTrace (prefixWord ++ tailWord_3064564) baseStart_3064564 baseEnd_3064564 := by
    simpa [prefixWord, tailWord_3064564, baseEnd_3064564] using wordTrace_append hprefix tailTrace_3064564
  have hstable : (prefixWord ++ tailWord_3064564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064564).length < 2 ^ (prefixWord ++ tailWord_3064564).sum := by decide
  have hdescent : baseEnd_3064564 < baseStart_3064564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064573 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 8]
def baseStart_3064573 : Nat := 118140960795 + 3064573 * 2 ^ 59
def prefixEnd_3064573 : Nat := 4983230072969 + 3 ^ 40 * 3064573 * 2
def baseEnd_3064573 : Nat := 174844327754571508638199

theorem tailTrace_3064573 : CollatzResearch.WordTrace tailWord_3064573 prefixEnd_3064573 174844327754571508638199 := by
  unfold tailWord_3064573
  simp only [CollatzResearch.WordTrace]
  refine ⟨111774159926582883244510373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74516106617721922163006915 111774159926582883244510373)
  ·
    refine ⟨20957654986234290608345695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111774159926582883244510373 20957654986234290608345695)
    ·
      refine ⟨31436482479351435912518543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20957654986234290608345695 31436482479351435912518543)
      ·
        refine ⟨47154723719027153868777815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31436482479351435912518543 47154723719027153868777815)
        ·
          refine ⟨70732085578540730803166723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47154723719027153868777815 70732085578540730803166723)
          ·
            refine ⟨106098128367811096204750085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70732085578540730803166723 106098128367811096204750085)
            ·
              refine ⟨19893399068964580538390641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106098128367811096204750085 19893399068964580538390641)
              ·
                refine ⟨14920049301723435403792981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19893399068964580538390641 14920049301723435403792981)
                ·
                  refine ⟨174844327754571508638199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14920049301723435403792981 174844327754571508638199)
                  ·
                    rfl

theorem cell23_3064573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_3064573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064573 prefixEnd_3064573 := by exact prefixLift 3064573
  have htrace : WordTrace (prefixWord ++ tailWord_3064573) baseStart_3064573 baseEnd_3064573 := by
    simpa [prefixWord, tailWord_3064573, baseEnd_3064573] using wordTrace_append hprefix tailTrace_3064573
  have hstable : (prefixWord ++ tailWord_3064573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064573).length < 2 ^ (prefixWord ++ tailWord_3064573).sum := by decide
  have hdescent : baseEnd_3064573 < baseStart_3064573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064593 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_3064593 : Nat := 118140960795 + 3064593 * 2 ^ 59
def prefixEnd_3064593 : Nat := 4983230072969 + 3 ^ 40 * 3064593 * 2
def baseEnd_3064593 : Nat := 1573609219404233499493699

theorem tailTrace_3064593 : CollatzResearch.WordTrace tailWord_3064593 prefixEnd_3064593 1573609219404233499493699 := by
  unfold tailWord_3064593
  simp only [CollatzResearch.WordTrace]
  refine ⟨111774889386510426660238433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74516592924340284440158955 111774889386510426660238433)
  ·
    refine ⟨83831167039882819995178825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111774889386510426660238433 83831167039882819995178825)
    ·
      refine ⟨62873375279912114996384119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83831167039882819995178825 62873375279912114996384119)
      ·
        refine ⟨94310062919868172494576179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62873375279912114996384119 94310062919868172494576179)
        ·
          refine ⟨141465094379802258741864269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94310062919868172494576179 141465094379802258741864269)
          ·
            refine ⟨53049410392425847028199101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141465094379802258741864269 53049410392425847028199101)
            ·
              refine ⟨19893528897159692635574663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53049410392425847028199101 19893528897159692635574663)
              ·
                refine ⟨29840293345739538953361995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19893528897159692635574663 29840293345739538953361995)
                ·
                  refine ⟨44760440018609308430042993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29840293345739538953361995 44760440018609308430042993)
                  ·
                    refine ⟨33570330013956981322532245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44760440018609308430042993 33570330013956981322532245)
                    ·
                      refine ⟨1573609219404233499493699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33570330013956981322532245 1573609219404233499493699)
                      ·
                        rfl

theorem cell23_3064593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_3064593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064593 prefixEnd_3064593 := by exact prefixLift 3064593
  have htrace : WordTrace (prefixWord ++ tailWord_3064593) baseStart_3064593 baseEnd_3064593 := by
    simpa [prefixWord, tailWord_3064593, baseEnd_3064593] using wordTrace_append hprefix tailTrace_3064593
  have hstable : (prefixWord ++ tailWord_3064593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064593).length < 2 ^ (prefixWord ++ tailWord_3064593).sum := by decide
  have hdescent : baseEnd_3064593 < baseStart_3064593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064607 : List Nat := [1, 1, 2, 4, 2, 3, 3, 1, 6]
def baseStart_3064607 : Nat := 118140960795 + 3064607 * 2 ^ 59
def prefixEnd_3064607 : Nat := 4983230072969 + 3 ^ 40 * 3064607 * 2
def baseEnd_3064607 : Nat := 174846267570377382746515

theorem tailTrace_3064607 : CollatzResearch.WordTrace tailWord_3064607 prefixEnd_3064607 174846267570377382746515 := by
  unfold tailWord_3064607
  simp only [CollatzResearch.WordTrace]
  refine ⟨111775400008459707051248075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74516933338973138034165383 111775400008459707051248075)
  ·
    refine ⟨167663100012689560576872113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111775400008459707051248075 167663100012689560576872113)
    ·
      refine ⟨125747325009517170432654085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167663100012689560576872113 125747325009517170432654085)
      ·
        refine ⟨23577623439284469456122641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125747325009517170432654085 23577623439284469456122641)
        ·
          refine ⟨17683217579463352092091981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23577623439284469456122641 17683217579463352092091981)
          ·
            refine ⟨6631206592298757034534493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17683217579463352092091981 6631206592298757034534493)
            ·
              refine ⟨2486702472112033887950435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6631206592298757034534493 2486702472112033887950435)
              ·
                refine ⟨3730053708168050831925653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486702472112033887950435 3730053708168050831925653)
                ·
                  refine ⟨174846267570377382746515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3730053708168050831925653 174846267570377382746515)
                  ·
                    rfl

theorem cell23_3064607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 6].length) (baseStart_3064607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064607 prefixEnd_3064607 := by exact prefixLift 3064607
  have htrace : WordTrace (prefixWord ++ tailWord_3064607) baseStart_3064607 baseEnd_3064607 := by
    simpa [prefixWord, tailWord_3064607, baseEnd_3064607] using wordTrace_append hprefix tailTrace_3064607
  have hstable : (prefixWord ++ tailWord_3064607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064607).length < 2 ^ (prefixWord ++ tailWord_3064607).sum := by decide
  have hdescent : baseEnd_3064607 < baseStart_3064607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064627 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 1, 5, 2]
def baseStart_3064627 : Nat := 118140960795 + 3064627 * 2 ^ 59
def prefixEnd_3064627 : Nat := 4983230072969 + 3 ^ 40 * 3064627 * 2
def baseEnd_3064627 : Nat := 1573626677746486366468543

theorem tailTrace_3064627 : CollatzResearch.WordTrace tailWord_3064627 prefixEnd_3064627 1573626677746486366468543 := by
  unfold tailWord_3064627
  simp only [CollatzResearch.WordTrace]
  refine ⟨111776129468387250466976135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74517419645591500311317423 111776129468387250466976135)
  ·
    refine ⟨167664194202580875700464203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111776129468387250466976135 167664194202580875700464203)
    ·
      refine ⟨251496291303871313550696305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167664194202580875700464203 251496291303871313550696305)
      ·
        refine ⟨188622218477903485163022229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251496291303871313550696305 188622218477903485163022229)
        ·
          refine ⟨8841666491151725867016667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 188622218477903485163022229 8841666491151725867016667)
          ·
            refine ⟨13262499736727588800525001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8841666491151725867016667 13262499736727588800525001)
            ·
              refine ⟨9946874802545691600393751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13262499736727588800525001 9946874802545691600393751)
              ·
                refine ⟨14920312203818537400590627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9946874802545691600393751 14920312203818537400590627)
                ·
                  refine ⟨22380468305727806100885941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14920312203818537400590627 22380468305727806100885941)
                  ·
                    refine ⟨2098168903661981821958057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22380468305727806100885941 2098168903661981821958057)
                    ·
                      refine ⟨1573626677746486366468543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2098168903661981821958057 1573626677746486366468543)
                      ·
                        rfl

theorem cell23_3064627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 5, 2].length) (baseStart_3064627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064627 prefixEnd_3064627 := by exact prefixLift 3064627
  have htrace : WordTrace (prefixWord ++ tailWord_3064627) baseStart_3064627 baseEnd_3064627 := by
    simpa [prefixWord, tailWord_3064627, baseEnd_3064627] using wordTrace_append hprefix tailTrace_3064627
  have hstable : (prefixWord ++ tailWord_3064627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064627).length < 2 ^ (prefixWord ++ tailWord_3064627).sum := by decide
  have hdescent : baseEnd_3064627 < baseStart_3064627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064628 : List Nat := [2, 5, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_3064628 : Nat := 118140960795 + 3064628 * 2 ^ 59
def prefixEnd_3064628 : Nat := 4983230072969 + 3 ^ 40 * 3064628 * 2
def baseEnd_3064628 : Nat := 524542397075713620852013

theorem tailTrace_3064628 : CollatzResearch.WordTrace tailWord_3064628 prefixEnd_3064628 524542397075713620852013 := by
  unfold tailWord_3064628
  simp only [CollatzResearch.WordTrace]
  refine ⟨55888082970691813818881269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74517443960922418425175025 55888082970691813818881269)
  ·
    refine ⟨5239507778502357545520119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55888082970691813818881269 5239507778502357545520119)
    ·
      refine ⟨7859261667753536318280179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5239507778502357545520119 7859261667753536318280179)
      ·
        refine ⟨11788892501630304477420269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7859261667753536318280179 11788892501630304477420269)
        ·
          refine ⟨4420834688111364179032601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11788892501630304477420269 4420834688111364179032601)
          ·
            refine ⟨3315626016083523134274451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4420834688111364179032601 3315626016083523134274451)
            ·
              refine ⟨4973439024125284701411677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315626016083523134274451 4973439024125284701411677)
              ·
                refine ⟨1865039634046981763029379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4973439024125284701411677 1865039634046981763029379)
                ·
                  refine ⟨2797559451070472644544069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865039634046981763029379 2797559451070472644544069)
                  ·
                    refine ⟨524542397075713620852013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2797559451070472644544069 524542397075713620852013)
                    ·
                      rfl

theorem cell23_3064628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_3064628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064628 prefixEnd_3064628 := by exact prefixLift 3064628
  have htrace : WordTrace (prefixWord ++ tailWord_3064628) baseStart_3064628 baseEnd_3064628 := by
    simpa [prefixWord, tailWord_3064628, baseEnd_3064628] using wordTrace_append hprefix tailTrace_3064628
  have hstable : (prefixWord ++ tailWord_3064628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064628).length < 2 ^ (prefixWord ++ tailWord_3064628).sum := by decide
  have hdescent : baseEnd_3064628 < baseStart_3064628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064674 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3064674 : Nat := 118140960795 + 3064674 * 2 ^ 59
def prefixEnd_3064674 : Nat := 4983230072969 + 3 ^ 40 * 3064674 * 2
def baseEnd_3064674 : Nat := 1573650811337247682580827

theorem tailTrace_3064674 : CollatzResearch.WordTrace tailWord_3064674 prefixEnd_3064674 1573650811337247682580827 := by
  unfold tailWord_3064674
  simp only [CollatzResearch.WordTrace]
  refine ⟨27944460924804244373484269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74518562466144651662624717 27944460924804244373484269)
  ·
    refine ⟨10479172846801591640056601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27944460924804244373484269 10479172846801591640056601)
    ·
      refine ⟨7859379635101193730042451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10479172846801591640056601 7859379635101193730042451)
      ·
        refine ⟨11789069452651790595063677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7859379635101193730042451 11789069452651790595063677)
        ·
          refine ⟨4420901044744421473148879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11789069452651790595063677 4420901044744421473148879)
          ·
            refine ⟨6631351567116632209723319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4420901044744421473148879 6631351567116632209723319)
            ·
              refine ⟨9947027350674948314584979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6631351567116632209723319 9947027350674948314584979)
              ·
                refine ⟨14920541026012422471877469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9947027350674948314584979 14920541026012422471877469)
                ·
                  refine ⟨5595202884754658426954051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14920541026012422471877469 5595202884754658426954051)
                  ·
                    refine ⟨8392804327131987640431077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5595202884754658426954051 8392804327131987640431077)
                    ·
                      refine ⟨1573650811337247682580827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8392804327131987640431077 1573650811337247682580827)
                      ·
                        rfl

theorem cell23_3064674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3064674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064674 prefixEnd_3064674 := by exact prefixLift 3064674
  have htrace : WordTrace (prefixWord ++ tailWord_3064674) baseStart_3064674 baseEnd_3064674 := by
    simpa [prefixWord, tailWord_3064674, baseEnd_3064674] using wordTrace_append hprefix tailTrace_3064674
  have hstable : (prefixWord ++ tailWord_3064674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064674).length < 2 ^ (prefixWord ++ tailWord_3064674).sum := by decide
  have hdescent : baseEnd_3064674 < baseStart_3064674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064680 : List Nat := [2, 1, 4, 2, 1, 2, 2, 9]
def baseStart_3064680 : Nat := 118140960795 + 3064680 * 2 ^ 59
def prefixEnd_3064680 : Nat := 4983230072969 + 3 ^ 40 * 3064680 * 2
def baseEnd_3064680 : Nat := 58283477489673135522437

theorem tailTrace_3064680 : CollatzResearch.WordTrace tailWord_3064680 prefixEnd_3064680 58283477489673135522437 := by
  unfold tailWord_3064680
  simp only [CollatzResearch.WordTrace]
  refine ⟨55889031268597620259327747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74518708358130160345770329 55889031268597620259327747)
  ·
    refine ⟨83833546902896430388991621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55889031268597620259327747 83833546902896430388991621)
    ·
      refine ⟨15718790044293080697935929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83833546902896430388991621 15718790044293080697935929)
      ·
        refine ⟨11789092533219810523451947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15718790044293080697935929 11789092533219810523451947)
        ·
          refine ⟨17683638799829715785177921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11789092533219810523451947 17683638799829715785177921)
          ·
            refine ⟨13262729099872286838883441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17683638799829715785177921 13262729099872286838883441)
            ·
              refine ⟨9947046824904215129162581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13262729099872286838883441 9947046824904215129162581)
              ·
                refine ⟨58283477489673135522437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9947046824904215129162581 58283477489673135522437)
                ·
                  rfl

theorem cell23_3064680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 9].length) (baseStart_3064680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064680 prefixEnd_3064680 := by exact prefixLift 3064680
  have htrace : WordTrace (prefixWord ++ tailWord_3064680) baseStart_3064680 baseEnd_3064680 := by
    simpa [prefixWord, tailWord_3064680, baseEnd_3064680] using wordTrace_append hprefix tailTrace_3064680
  have hstable : (prefixWord ++ tailWord_3064680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064680).length < 2 ^ (prefixWord ++ tailWord_3064680).sum := by decide
  have hdescent : baseEnd_3064680 < baseStart_3064680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064694 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3064694 : Nat := 118140960795 + 3064694 * 2 ^ 59
def prefixEnd_3064694 : Nat := 4983230072969 + 3 ^ 40 * 3064694 * 2
def baseEnd_3064694 : Nat := 1573661080950337604330735

theorem tailTrace_3064694 : CollatzResearch.WordTrace tailWord_3064694 prefixEnd_3064694 1573661080950337604330735 := by
  unfold tailWord_3064694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6986160822446532556854071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74519048772763013939776757 6986160822446532556854071)
  ·
    refine ⟨10479241233669798835281107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6986160822446532556854071 10479241233669798835281107)
    ·
      refine ⟨15718861850504698252921661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10479241233669798835281107 15718861850504698252921661)
      ·
        refine ⟨5894573193939261844845623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15718861850504698252921661 5894573193939261844845623)
        ·
          refine ⟨8841859790908892767268435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5894573193939261844845623 8841859790908892767268435)
          ·
            refine ⟨13262789686363339150902653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8841859790908892767268435 13262789686363339150902653)
            ·
              refine ⟨4973546132386252181588495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13262789686363339150902653 4973546132386252181588495)
              ·
                refine ⟨7460319198579378272382743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4973546132386252181588495 7460319198579378272382743)
                ·
                  refine ⟨11190478797869067408574115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7460319198579378272382743 11190478797869067408574115)
                  ·
                    refine ⟨16785718196803601112861173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11190478797869067408574115 16785718196803601112861173)
                    ·
                      refine ⟨1573661080950337604330735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16785718196803601112861173 1573661080950337604330735)
                      ·
                        rfl

theorem cell23_3064694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3064694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064694 prefixEnd_3064694 := by exact prefixLift 3064694
  have htrace : WordTrace (prefixWord ++ tailWord_3064694) baseStart_3064694 baseEnd_3064694 := by
    simpa [prefixWord, tailWord_3064694, baseEnd_3064694] using wordTrace_append hprefix tailTrace_3064694
  have hstable : (prefixWord ++ tailWord_3064694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064694).length < 2 ^ (prefixWord ++ tailWord_3064694).sum := by decide
  have hdescent : baseEnd_3064694 < baseStart_3064694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064702 : List Nat := [4, 2, 3, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_3064702 : Nat := 118140960795 + 3064702 * 2 ^ 59
def prefixEnd_3064702 : Nat := 4983230072969 + 3 ^ 40 * 3064702 * 2
def baseEnd_3064702 : Nat := 1573665188795573573030699

theorem tailTrace_3064702 : CollatzResearch.WordTrace tailWord_3064702 prefixEnd_3064702 1573665188795573573030699 := by
  unfold tailWord_3064702
  simp only [CollatzResearch.WordTrace]
  refine ⟨13972358117889442284494545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74519243295410358850637573 13972358117889442284494545)
  ·
    refine ⟨10479268588417081713370909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13972358117889442284494545 10479268588417081713370909)
    ·
      refine ⟨3929725720656405642514091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10479268588417081713370909 3929725720656405642514091)
      ·
        refine ⟨5894588580984608463771137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929725720656405642514091 5894588580984608463771137)
        ·
          refine ⟨4420941435738456347828353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5894588580984608463771137 4420941435738456347828353)
          ·
            refine ⟨3315706076803842260871265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4420941435738456347828353 3315706076803842260871265)
            ·
              refine ⟨2486779557602881695653449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3315706076803842260871265 2486779557602881695653449)
              ·
                refine ⟨1865084668202161271740087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2486779557602881695653449 1865084668202161271740087)
                ·
                  refine ⟨2797627002303241907610131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865084668202161271740087 2797627002303241907610131)
                  ·
                    refine ⟨4196440503454862861415197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2797627002303241907610131 4196440503454862861415197)
                    ·
                      refine ⟨1573665188795573573030699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4196440503454862861415197 1573665188795573573030699)
                      ·
                        rfl

theorem cell23_3064702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_3064702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064702 prefixEnd_3064702 := by exact prefixLift 3064702
  have htrace : WordTrace (prefixWord ++ tailWord_3064702) baseStart_3064702 baseEnd_3064702 := by
    simpa [prefixWord, tailWord_3064702, baseEnd_3064702] using wordTrace_append hprefix tailTrace_3064702
  have hstable : (prefixWord ++ tailWord_3064702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064702).length < 2 ^ (prefixWord ++ tailWord_3064702).sum := by decide
  have hdescent : baseEnd_3064702 < baseStart_3064702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064724 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_3064724 : Nat := 118140960795 + 3064724 * 2 ^ 59
def prefixEnd_3064724 : Nat := 4983230072969 + 3 ^ 40 * 3064724 * 2
def baseEnd_3064724 : Nat := 1573676485369972486955597

theorem tailTrace_3064724 : CollatzResearch.WordTrace tailWord_3064724 prefixEnd_3064724 1573676485369972486955597 := by
  unfold tailWord_3064724
  simp only [CollatzResearch.WordTrace]
  refine ⟨55889833674517918016628613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74519778232690557355504817 55889833674517918016628613)
  ·
    refine ⟨10479343813972109628117865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55889833674517918016628613 10479343813972109628117865)
    ·
      refine ⟨7859507860479082221088399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10479343813972109628117865 7859507860479082221088399)
      ·
        refine ⟨11789261790718623331632599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7859507860479082221088399 11789261790718623331632599)
        ·
          refine ⟨17683892686077934997448899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11789261790718623331632599 17683892686077934997448899)
          ·
            refine ⟨26525839029116902496173349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17683892686077934997448899 26525839029116902496173349)
            ·
              refine ⟨4973594817959419218032503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26525839029116902496173349 4973594817959419218032503)
              ·
                refine ⟨7460392226939128827048755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4973594817959419218032503 7460392226939128827048755)
                ·
                  refine ⟨11190588340408693240573133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7460392226939128827048755 11190588340408693240573133)
                  ·
                    refine ⟨4196470627653259965214925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11190588340408693240573133 4196470627653259965214925)
                    ·
                      refine ⟨1573676485369972486955597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4196470627653259965214925 1573676485369972486955597)
                      ·
                        rfl

theorem cell23_3064724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_3064724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064724 prefixEnd_3064724 := by exact prefixLift 3064724
  have htrace : WordTrace (prefixWord ++ tailWord_3064724) baseStart_3064724 baseEnd_3064724 := by
    simpa [prefixWord, tailWord_3064724, baseEnd_3064724] using wordTrace_append hprefix tailTrace_3064724
  have hstable : (prefixWord ++ tailWord_3064724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064724).length < 2 ^ (prefixWord ++ tailWord_3064724).sum := by decide
  have hdescent : baseEnd_3064724 < baseStart_3064724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064740 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_3064740 : Nat := 118140960795 + 3064740 * 2 ^ 59
def prefixEnd_3064740 : Nat := 4983230072969 + 3 ^ 40 * 3064740 * 2
def baseEnd_3064740 : Nat := 524561567020148141451841

theorem tailTrace_3064740 : CollatzResearch.WordTrace tailWord_3064740 prefixEnd_3064740 524561567020148141451841 := by
  unfold tailWord_3064740
  simp only [CollatzResearch.WordTrace]
  refine ⟨55890125458488935382919837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74520167277985247177226449 55890125458488935382919837)
  ·
    refine ⟨20958797046933350768594939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55890125458488935382919837 20958797046933350768594939)
    ·
      refine ⟨31438195570400026152892409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20958797046933350768594939 31438195570400026152892409)
      ·
        refine ⟨23578646677800019614669307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31438195570400026152892409 23578646677800019614669307)
        ·
          refine ⟨35367970016700029422003961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23578646677800019614669307 35367970016700029422003961)
          ·
            refine ⟨26525977512525022066502971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35367970016700029422003961 26525977512525022066502971)
            ·
              refine ⟨39788966268787533099754457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26525977512525022066502971 39788966268787533099754457)
              ·
                refine ⟨29841724701590649824815843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39788966268787533099754457 29841724701590649824815843)
                ·
                  refine ⟨44762587052385974737223765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29841724701590649824815843 44762587052385974737223765)
                  ·
                    refine ⟨524561567020148141451841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44762587052385974737223765 524561567020148141451841)
                    ·
                      rfl

theorem cell23_3064740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_3064740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064740 prefixEnd_3064740 := by exact prefixLift 3064740
  have htrace : WordTrace (prefixWord ++ tailWord_3064740) baseStart_3064740 baseEnd_3064740 := by
    simpa [prefixWord, tailWord_3064740, baseEnd_3064740] using wordTrace_append hprefix tailTrace_3064740
  have hstable : (prefixWord ++ tailWord_3064740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064740).length < 2 ^ (prefixWord ++ tailWord_3064740).sum := by decide
  have hdescent : baseEnd_3064740 < baseStart_3064740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064817 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 4, 5]
def baseStart_3064817 : Nat := 118140960795 + 3064817 * 2 ^ 59
def prefixEnd_3064817 : Nat := 4983230072969 + 3 ^ 40 * 3064817 * 2
def baseEnd_3064817 : Nat := 524574746356946874364223

theorem tailTrace_3064817 : CollatzResearch.WordTrace tailWord_3064817 prefixEnd_3064817 524574746356946874364223 := by
  unfold tailWord_3064817
  simp only [CollatzResearch.WordTrace]
  refine ⟨111783059337698912916392705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74522039558465941944261803 111783059337698912916392705)
  ·
    refine ⟨83837294503274184687294529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111783059337698912916392705 83837294503274184687294529)
    ·
      refine ⟨62877970877455638515470897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83837294503274184687294529 62877970877455638515470897)
      ·
        refine ⟨47158478158091728886603173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62877970877455638515470897 47158478158091728886603173)
        ·
          refine ⟨8842214654642199166238095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47158478158091728886603173 8842214654642199166238095)
          ·
            refine ⟨13263321981963298749357143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8842214654642199166238095 13263321981963298749357143)
            ·
              refine ⟨19894982972944948124035715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13263321981963298749357143 19894982972944948124035715)
              ·
                refine ⟨29842474459417422186053573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19894982972944948124035715 29842474459417422186053573)
                ·
                  refine ⟨5595463961140766659885045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29842474459417422186053573 5595463961140766659885045)
                  ·
                    refine ⟨524574746356946874364223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5595463961140766659885045 524574746356946874364223)
                    ·
                      rfl

theorem cell23_3064817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_3064817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064817 prefixEnd_3064817 := by exact prefixLift 3064817
  have htrace : WordTrace (prefixWord ++ tailWord_3064817) baseStart_3064817 baseEnd_3064817 := by
    simpa [prefixWord, tailWord_3064817, baseEnd_3064817] using wordTrace_append hprefix tailTrace_3064817
  have hstable : (prefixWord ++ tailWord_3064817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064817).length < 2 ^ (prefixWord ++ tailWord_3064817).sum := by decide
  have hdescent : baseEnd_3064817 < baseStart_3064817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064837 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 4, 1, 4]
def baseStart_3064837 : Nat := 118140960795 + 3064837 * 2 ^ 59
def prefixEnd_3064837 : Nat := 4983230072969 + 3 ^ 40 * 3064837 * 2
def baseEnd_3064837 : Nat := 1573734508683930544842577

theorem tailTrace_3064837 : CollatzResearch.WordTrace tailWord_3064837 prefixEnd_3064837 1573734508683930544842577 := by
  unfold tailWord_3064837
  simp only [CollatzResearch.WordTrace]
  refine ⟨111783788797626456332120765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74522525865084304221413843 111783788797626456332120765)
  ·
    refine ⟨41918920799109921124545287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111783788797626456332120765 41918920799109921124545287)
    ·
      refine ⟨62878381198664881686817931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41918920799109921124545287 62878381198664881686817931)
      ·
        refine ⟨94317571797997322530226897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62878381198664881686817931 94317571797997322530226897)
        ·
          refine ⟨70738178848497991897670173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94317571797997322530226897 70738178848497991897670173)
          ·
            refine ⟨26526817068186746961626315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70738178848497991897670173 26526817068186746961626315)
            ·
              refine ⟨39790225602280120442439473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26526817068186746961626315 39790225602280120442439473)
              ·
                refine ⟨29842669201710090331829605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39790225602280120442439473 29842669201710090331829605)
                ·
                  refine ⟨5595500475320641937218051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29842669201710090331829605 5595500475320641937218051)
                  ·
                    refine ⟨8393250712980962905827077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5595500475320641937218051 8393250712980962905827077)
                    ·
                      refine ⟨1573734508683930544842577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8393250712980962905827077 1573734508683930544842577)
                      ·
                        rfl

theorem cell23_3064837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_3064837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064837 prefixEnd_3064837 := by exact prefixLift 3064837
  have htrace : WordTrace (prefixWord ++ tailWord_3064837) baseStart_3064837 baseEnd_3064837 := by
    simpa [prefixWord, tailWord_3064837, baseEnd_3064837] using wordTrace_append hprefix tailTrace_3064837
  have hstable : (prefixWord ++ tailWord_3064837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064837).length < 2 ^ (prefixWord ++ tailWord_3064837).sum := by decide
  have hdescent : baseEnd_3064837 < baseStart_3064837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064857 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 1, 4, 3]
def baseStart_3064857 : Nat := 118140960795 + 3064857 * 2 ^ 59
def prefixEnd_3064857 : Nat := 4983230072969 + 3 ^ 40 * 3064857 * 2
def baseEnd_3064857 : Nat := 1573744778297020466592485

theorem tailTrace_3064857 : CollatzResearch.WordTrace tailWord_3064857 prefixEnd_3064857 1573744778297020466592485 := by
  unfold tailWord_3064857
  simp only [CollatzResearch.WordTrace]
  refine ⟨111784518257553999747848825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74523012171702666498565883 111784518257553999747848825)
  ·
    refine ⟨83838388693165499810886619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111784518257553999747848825 83838388693165499810886619)
    ·
      refine ⟨125757583039748249716329929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83838388693165499810886619 125757583039748249716329929)
      ·
        refine ⟨94318187279811187287247447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125757583039748249716329929 94318187279811187287247447)
        ·
          refine ⟨141477280919716780930871171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94318187279811187287247447 141477280919716780930871171)
          ·
            refine ⟨212215921379575171396306757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141477280919716780930871171 212215921379575171396306757)
            ·
              refine ⟨39790485258670344636807517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212215921379575171396306757 39790485258670344636807517)
              ·
                refine ⟨14921431972001379238802819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39790485258670344636807517 14921431972001379238802819)
                ·
                  refine ⟨22382147958002068858204229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14921431972001379238802819 22382147958002068858204229)
                  ·
                    refine ⟨4196652742125387910913293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22382147958002068858204229 4196652742125387910913293)
                    ·
                      refine ⟨1573744778297020466592485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4196652742125387910913293 1573744778297020466592485)
                      ·
                        rfl

theorem cell23_3064857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_3064857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064857 prefixEnd_3064857 := by exact prefixLift 3064857
  have htrace : WordTrace (prefixWord ++ tailWord_3064857) baseStart_3064857 baseEnd_3064857 := by
    simpa [prefixWord, tailWord_3064857, baseEnd_3064857] using wordTrace_append hprefix tailTrace_3064857
  have hstable : (prefixWord ++ tailWord_3064857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064857).length < 2 ^ (prefixWord ++ tailWord_3064857).sum := by decide
  have hdescent : baseEnd_3064857 < baseStart_3064857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064871 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3064871 : Nat := 118140960795 + 3064871 * 2 ^ 59
def prefixEnd_3064871 : Nat := 4983230072969 + 3 ^ 40 * 3064871 * 2
def baseEnd_3064871 : Nat := 1573751967026183411817421

theorem tailTrace_3064871 : CollatzResearch.WordTrace tailWord_3064871 prefixEnd_3064871 1573751967026183411817421 := by
  unfold tailWord_3064871
  simp only [CollatzResearch.WordTrace]
  refine ⟨111785028879503280138858467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74523352586335520092572311 111785028879503280138858467)
  ·
    refine ⟨167677543319254920208287701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111785028879503280138858467 167677543319254920208287701)
    ·
      refine ⟨3929942421545037192381743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 167677543319254920208287701 3929942421545037192381743)
      ·
        refine ⟨5894913632317555788572615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929942421545037192381743 5894913632317555788572615)
        ·
          refine ⟨8842370448476333682858923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5894913632317555788572615 8842370448476333682858923)
          ·
            refine ⟨13263555672714500524288385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8842370448476333682858923 13263555672714500524288385)
            ·
              refine ⟨9947666754535875393216289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13263555672714500524288385 9947666754535875393216289)
              ·
                refine ⟨7460750065901906544912217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9947666754535875393216289 7460750065901906544912217)
                ·
                  refine ⟨5595562549426429908684163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7460750065901906544912217 5595562549426429908684163)
                  ·
                    refine ⟨8393343824139644863026245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5595562549426429908684163 8393343824139644863026245)
                    ·
                      refine ⟨1573751967026183411817421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8393343824139644863026245 1573751967026183411817421)
                      ·
                        rfl

theorem cell23_3064871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3064871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064871 prefixEnd_3064871 := by exact prefixLift 3064871
  have htrace : WordTrace (prefixWord ++ tailWord_3064871) baseStart_3064871 baseEnd_3064871 := by
    simpa [prefixWord, tailWord_3064871, baseEnd_3064871] using wordTrace_append hprefix tailTrace_3064871
  have hstable : (prefixWord ++ tailWord_3064871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064871).length < 2 ^ (prefixWord ++ tailWord_3064871).sum := by decide
  have hdescent : baseEnd_3064871 < baseStart_3064871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064881 : List Nat := [1, 2, 2, 3, 1, 2, 3, 4, 1, 4]
def baseStart_3064881 : Nat := 118140960795 + 3064881 * 2 ^ 59
def prefixEnd_3064881 : Nat := 4983230072969 + 3 ^ 40 * 3064881 * 2
def baseEnd_3064881 : Nat := 524585700610909457564125

theorem tailTrace_3064881 : CollatzResearch.WordTrace tailWord_3064881 prefixEnd_3064881 524585700610909457564125 := by
  unfold tailWord_3064881
  simp only [CollatzResearch.WordTrace]
  refine ⟨111785393609467051846722497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74523595739644701231148331 111785393609467051846722497)
  ·
    refine ⟨83839045207100288885041873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111785393609467051846722497 83839045207100288885041873)
    ·
      refine ⟨62879283905325216663781405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83839045207100288885041873 62879283905325216663781405)
      ·
        refine ⟨23579731464496956248918027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62879283905325216663781405 23579731464496956248918027)
        ·
          refine ⟨35369597196745434373377041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23579731464496956248918027 35369597196745434373377041)
          ·
            refine ⟨26527197897559075780032781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35369597196745434373377041 26527197897559075780032781)
            ·
              refine ⟨9947699211584653417512293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26527197897559075780032781 9947699211584653417512293)
              ·
                refine ⟨1865193602172122515783555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9947699211584653417512293 1865193602172122515783555)
                ·
                  refine ⟨2797790403258183773675333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865193602172122515783555 2797790403258183773675333)
                  ·
                    refine ⟨524585700610909457564125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2797790403258183773675333 524585700610909457564125)
                    ·
                      rfl

theorem cell23_3064881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_3064881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064881 prefixEnd_3064881 := by exact prefixLift 3064881
  have htrace : WordTrace (prefixWord ++ tailWord_3064881) baseStart_3064881 baseEnd_3064881 := by
    simpa [prefixWord, tailWord_3064881, baseEnd_3064881] using wordTrace_append hprefix tailTrace_3064881
  have hstable : (prefixWord ++ tailWord_3064881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064881).length < 2 ^ (prefixWord ++ tailWord_3064881).sum := by decide
  have hdescent : baseEnd_3064881 < baseStart_3064881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064887 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 3]
def baseStart_3064887 : Nat := 118140960795 + 3064887 * 2 ^ 59
def prefixEnd_3064887 : Nat := 4983230072969 + 3 ^ 40 * 3064887 * 2
def baseEnd_3064887 : Nat := 1573760182716655349217347

theorem tailTrace_3064887 : CollatzResearch.WordTrace tailWord_3064887 prefixEnd_3064887 1573760182716655349217347 := by
  unfold tailWord_3064887
  simp only [CollatzResearch.WordTrace]
  refine ⟨111785612447445314871440915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74523741631630209914293943 111785612447445314871440915)
  ·
    refine ⟨167678418671167972307161373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111785612447445314871440915 167678418671167972307161373)
    ·
      refine ⟨62879407001687989615185515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167678418671167972307161373 62879407001687989615185515)
      ·
        refine ⟨94319110502531984422778273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62879407001687989615185515 94319110502531984422778273)
        ·
          refine ⟨70739332876898988317083705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94319110502531984422778273 70739332876898988317083705)
          ·
            refine ⟨53054499657674241237812779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70739332876898988317083705 53054499657674241237812779)
            ·
              refine ⟨79581749486511361856719169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53054499657674241237812779 79581749486511361856719169)
              ·
                refine ⟨59686312114883521392539377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79581749486511361856719169 59686312114883521392539377)
                ·
                  refine ⟨44764734086162641044404533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59686312114883521392539377 44764734086162641044404533)
                  ·
                    refine ⟨4196693820577747597912925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44764734086162641044404533 4196693820577747597912925)
                    ·
                      refine ⟨1573760182716655349217347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4196693820577747597912925 1573760182716655349217347)
                      ·
                        rfl

theorem cell23_3064887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_3064887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064887 prefixEnd_3064887 := by exact prefixLift 3064887
  have htrace : WordTrace (prefixWord ++ tailWord_3064887) baseStart_3064887 baseEnd_3064887 := by
    simpa [prefixWord, tailWord_3064887, baseEnd_3064887] using wordTrace_append hprefix tailTrace_3064887
  have hstable : (prefixWord ++ tailWord_3064887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064887).length < 2 ^ (prefixWord ++ tailWord_3064887).sum := by decide
  have hdescent : baseEnd_3064887 < baseStart_3064887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064938 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_3064938 : Nat := 118140960795 + 3064938 * 2 ^ 59
def prefixEnd_3064938 : Nat := 4983230072969 + 3 ^ 40 * 3064938 * 2
def baseEnd_3064938 : Nat := 1573786370230034649679613

theorem tailTrace_3064938 : CollatzResearch.WordTrace tailWord_3064938 prefixEnd_3064938 1573786370230034649679613 := by
  unfold tailWord_3064938
  simp only [CollatzResearch.WordTrace]
  refine ⟨27946868142565137645386867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74524981713507033721031645 27946868142565137645386867)
  ·
    refine ⟨41920302213847706468080301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27946868142565137645386867 41920302213847706468080301)
    ·
      refine ⟨15720113330192889925530113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41920302213847706468080301 15720113330192889925530113)
      ·
        refine ⟨11790084997644667444147585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15720113330192889925530113 11790084997644667444147585)
        ·
          refine ⟨8842563748233500583110689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11790084997644667444147585 8842563748233500583110689)
          ·
            refine ⟨6631922811175125437333017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8842563748233500583110689 6631922811175125437333017)
            ·
              refine ⟨4973942108381344077999763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6631922811175125437333017 4973942108381344077999763)
              ·
                refine ⟨7460913162572016116999645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4973942108381344077999763 7460913162572016116999645)
                ·
                  refine ⟨2797842435964506043874867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7460913162572016116999645 2797842435964506043874867)
                  ·
                    refine ⟨4196763653946759065812301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2797842435964506043874867 4196763653946759065812301)
                    ·
                      refine ⟨1573786370230034649679613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4196763653946759065812301 1573786370230034649679613)
                      ·
                        rfl

theorem cell23_3064938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_3064938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064938 prefixEnd_3064938 := by exact prefixLift 3064938
  have htrace : WordTrace (prefixWord ++ tailWord_3064938) baseStart_3064938 baseEnd_3064938 := by
    simpa [prefixWord, tailWord_3064938, baseEnd_3064938] using wordTrace_append hprefix tailTrace_3064938
  have hstable : (prefixWord ++ tailWord_3064938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064938).length < 2 ^ (prefixWord ++ tailWord_3064938).sum := by decide
  have hdescent : baseEnd_3064938 < baseStart_3064938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064961 : List Nat := [1, 2, 4, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_3064961 : Nat := 118140960795 + 3064961 * 2 ^ 59
def prefixEnd_3064961 : Nat := 4983230072969 + 3 ^ 40 * 3064961 * 2
def baseEnd_3064961 : Nat := 1573798180285088059692007

theorem tailTrace_3064961 : CollatzResearch.WordTrace tailWord_3064961 prefixEnd_3064961 1573798180285088059692007 := by
  unfold tailWord_3064961
  simp only [CollatzResearch.WordTrace]
  refine ⟨111788311449177225509634737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74525540966118150339756491 111788311449177225509634737)
  ·
    refine ⟨83841233586882919132226053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111788311449177225509634737 83841233586882919132226053)
    ·
      refine ⟨15720231297540547337292385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83841233586882919132226053 15720231297540547337292385)
      ·
        refine ⟨11790173473155410502969289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15720231297540547337292385 11790173473155410502969289)
        ·
          refine ⟨8842630104866557877226967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11790173473155410502969289 8842630104866557877226967)
          ·
            refine ⟨13263945157299836815840451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8842630104866557877226967 13263945157299836815840451)
            ·
              refine ⟨19895917735949755223760677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13263945157299836815840451 19895917735949755223760677)
              ·
                refine ⟨3730484575490579104455127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19895917735949755223760677 3730484575490579104455127)
                ·
                  refine ⟨5595726863235868656682691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3730484575490579104455127 5595726863235868656682691)
                  ·
                    refine ⟨8393590294853802985024037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5595726863235868656682691 8393590294853802985024037)
                    ·
                      refine ⟨1573798180285088059692007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8393590294853802985024037 1573798180285088059692007)
                      ·
                        rfl

theorem cell23_3064961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_3064961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064961 prefixEnd_3064961 := by exact prefixLift 3064961
  have htrace : WordTrace (prefixWord ++ tailWord_3064961) baseStart_3064961 baseEnd_3064961 := by
    simpa [prefixWord, tailWord_3064961, baseEnd_3064961] using wordTrace_append hprefix tailTrace_3064961
  have hstable : (prefixWord ++ tailWord_3064961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064961).length < 2 ^ (prefixWord ++ tailWord_3064961).sum := by decide
  have hdescent : baseEnd_3064961 < baseStart_3064961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3064984 : List Nat := [2, 1, 2, 4, 2, 3, 9]
def baseStart_3064984 : Nat := 118140960795 + 3064984 * 2 ^ 59
def prefixEnd_3064984 : Nat := 4983230072969 + 3 ^ 40 * 3064984 * 2
def baseEnd_3064984 : Nat := 19429752967162240366721

theorem tailTrace_3064984 : CollatzResearch.WordTrace tailWord_3064984 prefixEnd_3064984 19429752967162240366721 := by
  unfold tailWord_3064984
  simp only [CollatzResearch.WordTrace]
  refine ⟨55894575164046950218861003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74526100218729266958481337 55894575164046950218861003)
  ·
    refine ⟨83841862746070425328291505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55894575164046950218861003 83841862746070425328291505)
    ·
      refine ⟨62881397059552818996218629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83841862746070425328291505 62881397059552818996218629)
      ·
        refine ⟨11790261948666153561790993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62881397059552818996218629 11790261948666153561790993)
        ·
          refine ⟨8842696461499615171343245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11790261948666153561790993 8842696461499615171343245)
          ·
            refine ⟨3316011173062355689253717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8842696461499615171343245 3316011173062355689253717)
            ·
              refine ⟨19429752967162240366721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3316011173062355689253717 19429752967162240366721)
              ·
                rfl

theorem cell23_3064984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 9].length) (baseStart_3064984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3064984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3064984 prefixEnd_3064984 := by exact prefixLift 3064984
  have htrace : WordTrace (prefixWord ++ tailWord_3064984) baseStart_3064984 baseEnd_3064984 := by
    simpa [prefixWord, tailWord_3064984, baseEnd_3064984] using wordTrace_append hprefix tailTrace_3064984
  have hstable : (prefixWord ++ tailWord_3064984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3064984).length < 2 ^ (prefixWord ++ tailWord_3064984).sum := by decide
  have hdescent : baseEnd_3064984 < baseStart_3064984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3064984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065027 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 3, 8]
def baseStart_3065027 : Nat := 118140960795 + 3065027 * 2 ^ 59
def prefixEnd_3065027 : Nat := 4983230072969 + 3 ^ 40 * 3065027 * 2
def baseEnd_3065027 : Nat := 524610690002761600488901

theorem tailTrace_3065027 : CollatzResearch.WordTrace tailWord_3065027 prefixEnd_3065027 524610690002761600488901 := by
  unfold tailWord_3065027
  simp only [CollatzResearch.WordTrace]
  refine ⟨111790718666938118781537335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74527145777958745854358223 111790718666938118781537335)
  ·
    refine ⟨167686078000407178172306003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111790718666938118781537335 167686078000407178172306003)
    ·
      refine ⟨251529117000610767258459005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167686078000407178172306003 251529117000610767258459005)
      ·
        refine ⟨94323418875229037721922127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251529117000610767258459005 94323418875229037721922127)
        ·
          refine ⟨141485128312843556582883191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94323418875229037721922127 141485128312843556582883191)
          ·
            refine ⟨212227692469265334874324787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141485128312843556582883191 212227692469265334874324787)
            ·
              refine ⟨318341538703898002311487181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212227692469265334874324787 318341538703898002311487181)
              ·
                refine ⟨119378077013961750866807693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318341538703898002311487181 119378077013961750866807693)
                ·
                  refine ⟨44766778880235656575052885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119378077013961750866807693 44766778880235656575052885)
                  ·
                    refine ⟨524610690002761600488901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44766778880235656575052885 524610690002761600488901)
                    ·
                      rfl

theorem cell23_3065027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 8].length) (baseStart_3065027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065027 prefixEnd_3065027 := by exact prefixLift 3065027
  have htrace : WordTrace (prefixWord ++ tailWord_3065027) baseStart_3065027 baseEnd_3065027 := by
    simpa [prefixWord, tailWord_3065027, baseEnd_3065027] using wordTrace_append hprefix tailTrace_3065027
  have hstable : (prefixWord ++ tailWord_3065027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065027).length < 2 ^ (prefixWord ++ tailWord_3065027).sum := by decide
  have hdescent : baseEnd_3065027 < baseStart_3065027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065028 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_3065028 : Nat := 118140960795 + 3065028 * 2 ^ 59
def prefixEnd_3065028 : Nat := 4983230072969 + 3 ^ 40 * 3065028 * 2
def baseEnd_3065028 : Nat := 1573832583488939297554199

theorem tailTrace_3065028 : CollatzResearch.WordTrace tailWord_3065028 prefixEnd_3065028 1573832583488939297554199 := by
  unfold tailWord_3065028
  simp only [CollatzResearch.WordTrace]
  refine ⟨55895377569967247976161869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74527170093289663968215825 55895377569967247976161869)
  ·
    refine ⟨20960766588737717991060701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55895377569967247976161869 20960766588737717991060701)
    ·
      refine ⟨7860287470776644246647763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20960766588737717991060701 7860287470776644246647763)
      ·
        refine ⟨11790431206164966369971645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7860287470776644246647763 11790431206164966369971645)
        ·
          refine ⟨4421411702311862388739367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11790431206164966369971645 4421411702311862388739367)
          ·
            refine ⟨6632117553467793583109051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421411702311862388739367 6632117553467793583109051)
            ·
              refine ⟨9948176330201690374663577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6632117553467793583109051 9948176330201690374663577)
              ·
                refine ⟨7461132247651267780997683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9948176330201690374663577 7461132247651267780997683)
                ·
                  refine ⟨11191698371476901671496525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7461132247651267780997683 11191698371476901671496525)
                  ·
                    refine ⟨4196886889303838126811197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11191698371476901671496525 4196886889303838126811197)
                    ·
                      refine ⟨1573832583488939297554199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4196886889303838126811197 1573832583488939297554199)
                      ·
                        rfl

theorem cell23_3065028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_3065028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065028 prefixEnd_3065028 := by exact prefixLift 3065028
  have htrace : WordTrace (prefixWord ++ tailWord_3065028) baseStart_3065028 baseEnd_3065028 := by
    simpa [prefixWord, tailWord_3065028, baseEnd_3065028] using wordTrace_append hprefix tailTrace_3065028
  have hstable : (prefixWord ++ tailWord_3065028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065028).length < 2 ^ (prefixWord ++ tailWord_3065028).sum := by decide
  have hdescent : baseEnd_3065028 < baseStart_3065028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065045 : List Nat := [1, 3, 2, 4, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3065045 : Nat := 118140960795 + 3065045 * 2 ^ 59
def prefixEnd_3065045 : Nat := 4983230072969 + 3 ^ 40 * 3065045 * 2
def baseEnd_3065045 : Nat := 1573841312660065731041621

theorem tailTrace_3065045 : CollatzResearch.WordTrace tailWord_3065045 prefixEnd_3065045 1573841312660065731041621 := by
  unfold tailWord_3065045
  simp only [CollatzResearch.WordTrace]
  refine ⟨111791375180872907855692589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74527583453915271903795059 111791375180872907855692589)
  ·
    refine ⟨41921765692827340445884721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111791375180872907855692589 41921765692827340445884721)
    ·
      refine ⟨31441324269620505334413541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41921765692827340445884721 31441324269620505334413541)
      ·
        refine ⟨5895248300553844750202539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31441324269620505334413541 5895248300553844750202539)
        ·
          refine ⟨8842872450830767125303809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5895248300553844750202539 8842872450830767125303809)
          ·
            refine ⟨6632154338123075343977857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8842872450830767125303809 6632154338123075343977857)
            ·
              refine ⟨4974115753592306507983393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6632154338123075343977857 4974115753592306507983393)
              ·
                refine ⟨3730586815194229880987545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4974115753592306507983393 3730586815194229880987545)
                ·
                  refine ⟨2797940111395672410740659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3730586815194229880987545 2797940111395672410740659)
                  ·
                    refine ⟨4196910167093508616110989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2797940111395672410740659 4196910167093508616110989)
                    ·
                      refine ⟨1573841312660065731041621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4196910167093508616110989 1573841312660065731041621)
                      ·
                        rfl

theorem cell23_3065045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3065045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065045 prefixEnd_3065045 := by exact prefixLift 3065045
  have htrace : WordTrace (prefixWord ++ tailWord_3065045) baseStart_3065045 baseEnd_3065045 := by
    simpa [prefixWord, tailWord_3065045, baseEnd_3065045] using wordTrace_append hprefix tailTrace_3065045
  have hstable : (prefixWord ++ tailWord_3065045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065045).length < 2 ^ (prefixWord ++ tailWord_3065045).sum := by decide
  have hdescent : baseEnd_3065045 < baseStart_3065045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065061 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 2, 6]
def baseStart_3065061 : Nat := 118140960795 + 3065061 * 2 ^ 59
def prefixEnd_3065061 : Nat := 4983230072969 + 3 ^ 40 * 3065061 * 2
def baseEnd_3065061 : Nat := 524616509450179222813849

theorem tailTrace_3065061 : CollatzResearch.WordTrace tailWord_3065061 prefixEnd_3065061 524616509450179222813849 := by
  unfold tailWord_3065061
  simp only [CollatzResearch.WordTrace]
  refine ⟨111791958748814942588275037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74527972499209961725516691 111791958748814942588275037)
  ·
    refine ⟨41921984530805603470603139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111791958748814942588275037 41921984530805603470603139)
    ·
      refine ⟨62882976796208405205904709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41921984530805603470603139 62882976796208405205904709)
      ·
        refine ⟨11790558149289075976107133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62882976796208405205904709 11790558149289075976107133)
        ·
          refine ⟨4421459305983403491040175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11790558149289075976107133 4421459305983403491040175)
          ·
            refine ⟨6632188958975105236560263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421459305983403491040175 6632188958975105236560263)
            ·
              refine ⟨9948283438462657854840395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6632188958975105236560263 9948283438462657854840395)
              ·
                refine ⟨14922425157693986782260593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9948283438462657854840395 14922425157693986782260593)
                ·
                  refine ⟨11191818868270490086695445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14922425157693986782260593 11191818868270490086695445)
                  ·
                    refine ⟨524616509450179222813849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11191818868270490086695445 524616509450179222813849)
                    ·
                      rfl

theorem cell23_3065061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_3065061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065061 prefixEnd_3065061 := by exact prefixLift 3065061
  have htrace : WordTrace (prefixWord ++ tailWord_3065061) baseStart_3065061 baseEnd_3065061 := by
    simpa [prefixWord, tailWord_3065061, baseEnd_3065061] using wordTrace_append hprefix tailTrace_3065061
  have hstable : (prefixWord ++ tailWord_3065061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065061).length < 2 ^ (prefixWord ++ tailWord_3065061).sum := by decide
  have hdescent : baseEnd_3065061 < baseStart_3065061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065068 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 1, 4, 2]
def baseStart_3065068 : Nat := 118140960795 + 3065068 * 2 ^ 59
def prefixEnd_3065068 : Nat := 4983230072969 + 3 ^ 40 * 3065068 * 2
def baseEnd_3065068 : Nat := 1573853122715119141054015

theorem tailTrace_3065068 : CollatzResearch.WordTrace tailWord_3065068 prefixEnd_3065068 1573853122715119141054015 := by
  unfold tailWord_3065068
  simp only [CollatzResearch.WordTrace]
  refine ⟨55896107029894791391889929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74528142706526388522519905 55896107029894791391889929)
  ·
    refine ⟨41922080272421093543917447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55896107029894791391889929 41922080272421093543917447)
    ·
      refine ⟨62883120408631640315876171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41922080272421093543917447 62883120408631640315876171)
      ·
        refine ⟨94324680612947460473814257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62883120408631640315876171 94324680612947460473814257)
        ·
          refine ⟨70743510459710595355360693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94324680612947460473814257 70743510459710595355360693)
          ·
            refine ⟨6632204105597868314565065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70743510459710595355360693 6632204105597868314565065)
            ·
              refine ⟨4974153079198401235923799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6632204105597868314565065 4974153079198401235923799)
              ·
                refine ⟨7461229618797601853885699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4974153079198401235923799 7461229618797601853885699)
                ·
                  refine ⟨11191844428196402780828549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7461229618797601853885699 11191844428196402780828549)
                  ·
                    refine ⟨2098470830286825521405353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11191844428196402780828549 2098470830286825521405353)
                    ·
                      refine ⟨1573853122715119141054015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2098470830286825521405353 1573853122715119141054015)
                      ·
                        rfl

theorem cell23_3065068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 4, 2].length) (baseStart_3065068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065068 prefixEnd_3065068 := by exact prefixLift 3065068
  have htrace : WordTrace (prefixWord ++ tailWord_3065068) baseStart_3065068 baseEnd_3065068 := by
    simpa [prefixWord, tailWord_3065068, baseEnd_3065068] using wordTrace_append hprefix tailTrace_3065068
  have hstable : (prefixWord ++ tailWord_3065068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065068).length < 2 ^ (prefixWord ++ tailWord_3065068).sum := by decide
  have hdescent : baseEnd_3065068 < baseStart_3065068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065091 : List Nat := [1, 1, 1, 3, 2, 4, 1, 5, 5]
def baseStart_3065091 : Nat := 118140960795 + 3065091 * 2 ^ 59
def prefixEnd_3065091 : Nat := 4983230072969 + 3 ^ 40 * 3065091 * 2
def baseEnd_3065091 : Nat := 174873881418908061229601

theorem tailTrace_3065091 : CollatzResearch.WordTrace tailWord_3065091 prefixEnd_3065091 174873881418908061229601 := by
  unfold tailWord_3065091
  simp only [CollatzResearch.WordTrace]
  refine ⟨111793052938706257711867127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74528701959137505141244751 111793052938706257711867127)
  ·
    refine ⟨167689579408059386567800691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111793052938706257711867127 167689579408059386567800691)
    ·
      refine ⟨251534369112089079851701037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167689579408059386567800691 251534369112089079851701037)
      ·
        refine ⟨94325388417033404944387889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251534369112089079851701037 94325388417033404944387889)
        ·
          refine ⟨70744041312775053708290917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94325388417033404944387889 70744041312775053708290917)
          ·
            refine ⟨13264507746145322570304547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70744041312775053708290917 13264507746145322570304547)
            ·
              refine ⟨19896761619217983855456821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13264507746145322570304547 19896761619217983855456821)
              ·
                refine ⟨1865321401801685986449077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19896761619217983855456821 1865321401801685986449077)
                ·
                  refine ⟨174873881418908061229601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1865321401801685986449077 174873881418908061229601)
                  ·
                    rfl

theorem cell23_3065091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 5].length) (baseStart_3065091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065091 prefixEnd_3065091 := by exact prefixLift 3065091
  have htrace : WordTrace (prefixWord ++ tailWord_3065091) baseStart_3065091 baseEnd_3065091 := by
    simpa [prefixWord, tailWord_3065091, baseEnd_3065091] using wordTrace_append hprefix tailTrace_3065091
  have hstable : (prefixWord ++ tailWord_3065091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065091).length < 2 ^ (prefixWord ++ tailWord_3065091).sum := by decide
  have hdescent : baseEnd_3065091 < baseStart_3065091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065102 : List Nat := [4, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2]
def baseStart_3065102 : Nat := 118140960795 + 3065102 * 2 ^ 59
def prefixEnd_3065102 : Nat := 4983230072969 + 3 ^ 40 * 3065102 * 2
def baseEnd_3065102 : Nat := 1573870581057372008028859

theorem tailTrace_3065102 : CollatzResearch.WordTrace tailWord_3065102 prefixEnd_3065102 1573870581057372008028859 := by
  unfold tailWord_3065102
  simp only [CollatzResearch.WordTrace]
  refine ⟨13974181767708300823814695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74528969427777604393678373 13974181767708300823814695)
  ·
    refine ⟨20961272651562451235722043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13974181767708300823814695 20961272651562451235722043)
    ·
      refine ⟨31441908977343676853583065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20961272651562451235722043 31441908977343676853583065)
      ·
        refine ⟨23581431733007757640187299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31441908977343676853583065 23581431733007757640187299)
        ·
          refine ⟨35372147599511636460280949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23581431733007757640187299 35372147599511636460280949)
          ·
            refine ⟨3316138837454215918151339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35372147599511636460280949 3316138837454215918151339)
            ·
              refine ⟨4974208256181323877227009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316138837454215918151339 4974208256181323877227009)
              ·
                refine ⟨3730656192135992907920257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4974208256181323877227009 3730656192135992907920257)
                ·
                  refine ⟨2797992144101994680940193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3730656192135992907920257 2797992144101994680940193)
                  ·
                    refine ⟨2098494108076496010705145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2797992144101994680940193 2098494108076496010705145)
                    ·
                      refine ⟨1573870581057372008028859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2098494108076496010705145 1573870581057372008028859)
                      ·
                        rfl

theorem cell23_3065102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_3065102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065102 prefixEnd_3065102 := by exact prefixLift 3065102
  have htrace : WordTrace (prefixWord ++ tailWord_3065102) baseStart_3065102 baseEnd_3065102 := by
    simpa [prefixWord, tailWord_3065102, baseEnd_3065102] using wordTrace_append hprefix tailTrace_3065102
  have hstable : (prefixWord ++ tailWord_3065102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065102).length < 2 ^ (prefixWord ++ tailWord_3065102).sum := by decide
  have hdescent : baseEnd_3065102 < baseStart_3065102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065141 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_3065141 : Nat := 118140960795 + 3065141 * 2 ^ 59
def prefixEnd_3065141 : Nat := 4983230072969 + 3 ^ 40 * 3065141 * 2
def baseEnd_3065141 : Nat := 1573890606802897355441179

theorem tailTrace_3065141 : CollatzResearch.WordTrace tailWord_3065141 prefixEnd_3065141 1573890606802897355441179 := by
  unfold tailWord_3065141
  simp only [CollatzResearch.WordTrace]
  refine ⟨111794876588525116251187277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74529917725683410834124851 111794876588525116251187277)
  ·
    refine ⟨41923078720696918594195229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111794876588525116251187277 41923078720696918594195229)
    ·
      refine ⟨15721154520261344472823211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41923078720696918594195229 15721154520261344472823211)
      ·
        refine ⟨23581731780392016709234817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15721154520261344472823211 23581731780392016709234817)
        ·
          refine ⟨17686298835294012531926113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23581731780392016709234817 17686298835294012531926113)
          ·
            refine ⟨13264724126470509398944585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17686298835294012531926113 13264724126470509398944585)
            ·
              refine ⟨9948543094852882049208439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13264724126470509398944585 9948543094852882049208439)
              ·
                refine ⟨14922814642279323073812659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9948543094852882049208439 14922814642279323073812659)
                ·
                  refine ⟨22384221963418984610718989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14922814642279323073812659 22384221963418984610718989)
                  ·
                    refine ⟨8394083236282119229019621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22384221963418984610718989 8394083236282119229019621)
                    ·
                      refine ⟨1573890606802897355441179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8394083236282119229019621 1573890606802897355441179)
                      ·
                        rfl

theorem cell23_3065141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_3065141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065141 prefixEnd_3065141 := by exact prefixLift 3065141
  have htrace : WordTrace (prefixWord ++ tailWord_3065141) baseStart_3065141 baseEnd_3065141 := by
    simpa [prefixWord, tailWord_3065141, baseEnd_3065141] using wordTrace_append hprefix tailTrace_3065141
  have hstable : (prefixWord ++ tailWord_3065141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065141).length < 2 ^ (prefixWord ++ tailWord_3065141).sum := by decide
  have hdescent : baseEnd_3065141 < baseStart_3065141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065144 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_3065144 : Nat := 118140960795 + 3065144 * 2 ^ 59
def prefixEnd_3065144 : Nat := 4983230072969 + 3 ^ 40 * 3065144 * 2
def baseEnd_3065144 : Nat := 1573892147244860843703665

theorem tailTrace_3065144 : CollatzResearch.WordTrace tailWord_3065144 prefixEnd_3065144 1573892147244860843703665 := by
  unfold tailWord_3065144
  simp only [CollatzResearch.WordTrace]
  refine ⟨55897493003757123881773243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74529990671676165175697657 55897493003757123881773243)
  ·
    refine ⟨83846239505635685822659865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55897493003757123881773243 83846239505635685822659865)
    ·
      refine ⟨62884679629226764366994899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83846239505635685822659865 62884679629226764366994899)
      ·
        refine ⟨94327019443840146550492349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62884679629226764366994899 94327019443840146550492349)
        ·
          refine ⟨35372632291440054956434631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94327019443840146550492349 35372632291440054956434631)
          ·
            refine ⟨53058948437160082434651947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35372632291440054956434631 53058948437160082434651947)
            ·
              refine ⟨79588422655740123651977921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53058948437160082434651947 79588422655740123651977921)
              ·
                refine ⟨59691316991805092738983441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79588422655740123651977921 59691316991805092738983441)
                ·
                  refine ⟨44768487743853819554237581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59691316991805092738983441 44768487743853819554237581)
                  ·
                    refine ⟨16788182903945182332839093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44768487743853819554237581 16788182903945182332839093)
                    ·
                      refine ⟨1573892147244860843703665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16788182903945182332839093 1573892147244860843703665)
                      ·
                        rfl

theorem cell23_3065144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_3065144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065144 prefixEnd_3065144 := by exact prefixLift 3065144
  have htrace : WordTrace (prefixWord ++ tailWord_3065144) baseStart_3065144 baseEnd_3065144 := by
    simpa [prefixWord, tailWord_3065144, baseEnd_3065144] using wordTrace_append hprefix tailTrace_3065144
  have hstable : (prefixWord ++ tailWord_3065144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065144).length < 2 ^ (prefixWord ++ tailWord_3065144).sum := by decide
  have hdescent : baseEnd_3065144 < baseStart_3065144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065161 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 4, 2, 3]
def baseStart_3065161 : Nat := 118140960795 + 3065161 * 2 ^ 59
def prefixEnd_3065161 : Nat := 4983230072969 + 3 ^ 40 * 3065161 * 2
def baseEnd_3065161 : Nat := 1573900876415987277191087

theorem tailTrace_3065161 : CollatzResearch.WordTrace tailWord_3065161 prefixEnd_3065161 1573900876415987277191087 := by
  unfold tailWord_3065161
  simp only [CollatzResearch.WordTrace]
  refine ⟨111795606048452659666915337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74530404032301773111276891 111795606048452659666915337)
  ·
    refine ⟨83846704536339494750186503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111795606048452659666915337 83846704536339494750186503)
    ·
      refine ⟨125770056804509242125279755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83846704536339494750186503 125770056804509242125279755)
      ·
        refine ⟨188655085206763863187919633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125770056804509242125279755 188655085206763863187919633)
        ·
          refine ⟨141491313905072897390939725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188655085206763863187919633 141491313905072897390939725)
          ·
            refine ⟨53059242714402336521602397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141491313905072897390939725 53059242714402336521602397)
            ·
              refine ⟨19897216017900876195600899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53059242714402336521602397 19897216017900876195600899)
              ·
                refine ⟨29845824026851314293401349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19897216017900876195600899 29845824026851314293401349)
                ·
                  refine ⟨5596092005034621430012753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29845824026851314293401349 5596092005034621430012753)
                  ·
                    refine ⟨4197069003775966072509565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5596092005034621430012753 4197069003775966072509565)
                    ·
                      refine ⟨1573900876415987277191087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4197069003775966072509565 1573900876415987277191087)
                      ·
                        rfl

theorem cell23_3065161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 2, 3].length) (baseStart_3065161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065161 prefixEnd_3065161 := by exact prefixLift 3065161
  have htrace : WordTrace (prefixWord ++ tailWord_3065161) baseStart_3065161 baseEnd_3065161 := by
    simpa [prefixWord, tailWord_3065161, baseEnd_3065161] using wordTrace_append hprefix tailTrace_3065161
  have hstable : (prefixWord ++ tailWord_3065161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065161).length < 2 ^ (prefixWord ++ tailWord_3065161).sum := by decide
  have hdescent : baseEnd_3065161 < baseStart_3065161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065165 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3065165 : Nat := 118140960795 + 3065165 * 2 ^ 59
def prefixEnd_3065165 : Nat := 4983230072969 + 3 ^ 40 * 3065165 * 2
def baseEnd_3065165 : Nat := 1573902930338605261541069

theorem tailTrace_3065165 : CollatzResearch.WordTrace tailWord_3065165 prefixEnd_3065165 1573902930338605261541069 := by
  unfold tailWord_3065165
  simp only [CollatzResearch.WordTrace]
  refine ⟨111795751940438168350060949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74530501293625445566707299 111795751940438168350060949)
  ·
    refine ⟨5240425872208039141409107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111795751940438168350060949 5240425872208039141409107)
    ·
      refine ⟨7860638808312058712113661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5240425872208039141409107 7860638808312058712113661)
      ·
        refine ⟨2947739553117022017042623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7860638808312058712113661 2947739553117022017042623)
        ·
          refine ⟨4421609329675533025563935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2947739553117022017042623 4421609329675533025563935)
          ·
            refine ⟨6632413994513299538345903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421609329675533025563935 6632413994513299538345903)
            ·
              refine ⟨9948620991769949307518855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6632413994513299538345903 9948620991769949307518855)
              ·
                refine ⟨14922931487654923961278283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9948620991769949307518855 14922931487654923961278283)
                ·
                  refine ⟨22384397231482385941917425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14922931487654923961278283 22384397231482385941917425)
                  ·
                    refine ⟨16788297923611789456438069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22384397231482385941917425 16788297923611789456438069)
                    ·
                      refine ⟨1573902930338605261541069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16788297923611789456438069 1573902930338605261541069)
                      ·
                        rfl

theorem cell23_3065165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3065165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065165 prefixEnd_3065165 := by exact prefixLift 3065165
  have htrace : WordTrace (prefixWord ++ tailWord_3065165) baseStart_3065165 baseEnd_3065165 := by
    simpa [prefixWord, tailWord_3065165, baseEnd_3065165] using wordTrace_append hprefix tailTrace_3065165
  have hstable : (prefixWord ++ tailWord_3065165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065165).length < 2 ^ (prefixWord ++ tailWord_3065165).sum := by decide
  have hdescent : baseEnd_3065165 < baseStart_3065165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065241 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 1, 6]
def baseStart_3065241 : Nat := 118140960795 + 3065241 * 2 ^ 59
def prefixEnd_3065241 : Nat := 4983230072969 + 3 ^ 40 * 3065241 * 2
def baseEnd_3065241 : Nat := 524647318289448988063573

theorem tailTrace_3065241 : CollatzResearch.WordTrace tailWord_3065241 prefixEnd_3065241 524647318289448988063573 := by
  unfold tailWord_3065241
  simp only [CollatzResearch.WordTrace]
  refine ⟨111798523888162833329827577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74532349258775222219885051 111798523888162833329827577)
  ·
    refine ⟨83848892916122124997370683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111798523888162833329827577 83848892916122124997370683)
    ·
      refine ⟨125773339374183187496056025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83848892916122124997370683 125773339374183187496056025)
      ·
        refine ⟨94330004530637390622042019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125773339374183187496056025 94330004530637390622042019)
        ·
          refine ⟨141495006795956085933063029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94330004530637390622042019 141495006795956085933063029)
          ·
            refine ⟨13265156887120883056224659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141495006795956085933063029 13265156887120883056224659)
            ·
              refine ⟨19897735330681324584336989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13265156887120883056224659 19897735330681324584336989)
              ·
                refine ⟨7461650749005496719126371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19897735330681324584336989 7461650749005496719126371)
                ·
                  refine ⟨11192476123508245078689557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7461650749005496719126371 11192476123508245078689557)
                  ·
                    refine ⟨524647318289448988063573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11192476123508245078689557 524647318289448988063573)
                    ·
                      rfl

theorem cell23_3065241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 6].length) (baseStart_3065241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065241 prefixEnd_3065241 := by exact prefixLift 3065241
  have htrace : WordTrace (prefixWord ++ tailWord_3065241) baseStart_3065241 baseEnd_3065241 := by
    simpa [prefixWord, tailWord_3065241, baseEnd_3065241] using wordTrace_append hprefix tailTrace_3065241
  have hstable : (prefixWord ++ tailWord_3065241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065241).length < 2 ^ (prefixWord ++ tailWord_3065241).sum := by decide
  have hdescent : baseEnd_3065241 < baseStart_3065241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065248 : List Nat := [2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 4]
def baseStart_3065248 : Nat := 118140960795 + 3065248 * 2 ^ 59
def prefixEnd_3065248 : Nat := 4983230072969 + 3 ^ 40 * 3065248 * 2
def baseEnd_3065248 : Nat := 1573945549232928436803187

theorem tailTrace_3065248 : CollatzResearch.WordTrace tailWord_3065248 prefixEnd_3065248 1573945549232928436803187 := by
  unfold tailWord_3065248
  simp only [CollatzResearch.WordTrace]
  refine ⟨55899389599568736762666199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74532519466091649016888265 55899389599568736762666199)
  ·
    refine ⟨83849084399353105143999299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55899389599568736762666199 83849084399353105143999299)
    ·
      refine ⟨125773626599029657715998949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83849084399353105143999299 125773626599029657715998949)
      ·
        refine ⟨23582554987318060821749803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125773626599029657715998949 23582554987318060821749803)
        ·
          refine ⟨35373832480977091232624705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23582554987318060821749803 35373832480977091232624705)
          ·
            refine ⟨26530374360732818424468529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35373832480977091232624705 26530374360732818424468529)
            ·
              refine ⟨19897780770549613818351397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26530374360732818424468529 19897780770549613818351397)
              ·
                refine ⟨3730833894478052590940887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19897780770549613818351397 3730833894478052590940887)
                ·
                  refine ⟨5596250841717078886411331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3730833894478052590940887 5596250841717078886411331)
                  ·
                    refine ⟨8394376262575618329616997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5596250841717078886411331 8394376262575618329616997)
                    ·
                      refine ⟨1573945549232928436803187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8394376262575618329616997 1573945549232928436803187)
                      ·
                        rfl

theorem cell23_3065248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_3065248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065248 prefixEnd_3065248 := by exact prefixLift 3065248
  have htrace : WordTrace (prefixWord ++ tailWord_3065248) baseStart_3065248 baseEnd_3065248 := by
    simpa [prefixWord, tailWord_3065248, baseEnd_3065248] using wordTrace_append hprefix tailTrace_3065248
  have hstable : (prefixWord ++ tailWord_3065248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065248).length < 2 ^ (prefixWord ++ tailWord_3065248).sum := by decide
  have hdescent : baseEnd_3065248 < baseStart_3065248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065265 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 5, 2, 2]
def baseStart_3065265 : Nat := 118140960795 + 3065265 * 2 ^ 59
def prefixEnd_3065265 : Nat := 4983230072969 + 3 ^ 40 * 3065265 * 2
def baseEnd_3065265 : Nat := 1573954278404054870290609

theorem tailTrace_3065265 : CollatzResearch.WordTrace tailWord_3065265 prefixEnd_3065265 1573954278404054870290609 := by
  unfold tailWord_3065265
  simp only [CollatzResearch.WordTrace]
  refine ⟨111799399240075885428701249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74532932826717256952467499 111799399240075885428701249)
  ·
    refine ⟨83849549430056914071525937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111799399240075885428701249 83849549430056914071525937)
    ·
      refine ⟨62887162072542685553644453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83849549430056914071525937 62887162072542685553644453)
      ·
        refine ⟨11791342888601753541308335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62887162072542685553644453 11791342888601753541308335)
        ·
          refine ⟨17687014332902630311962503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11791342888601753541308335 17687014332902630311962503)
          ·
            refine ⟨26530521499353945467943755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17687014332902630311962503 26530521499353945467943755)
            ·
              refine ⟨39795782249030918201915633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26530521499353945467943755 39795782249030918201915633)
              ·
                refine ⟨29846836686773188651436725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39795782249030918201915633 29846836686773188651436725)
                ·
                  refine ⟨2798140939384986436072193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29846836686773188651436725 2798140939384986436072193)
                  ·
                    refine ⟨2098605704538739827054145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2798140939384986436072193 2098605704538739827054145)
                    ·
                      refine ⟨1573954278404054870290609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2098605704538739827054145 1573954278404054870290609)
                      ·
                        rfl

theorem cell23_3065265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_3065265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065265 prefixEnd_3065265 := by exact prefixLift 3065265
  have htrace : WordTrace (prefixWord ++ tailWord_3065265) baseStart_3065265 baseEnd_3065265 := by
    simpa [prefixWord, tailWord_3065265, baseEnd_3065265] using wordTrace_append hprefix tailTrace_3065265
  have hstable : (prefixWord ++ tailWord_3065265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065265).length < 2 ^ (prefixWord ++ tailWord_3065265).sum := by decide
  have hdescent : baseEnd_3065265 < baseStart_3065265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065292 : List Nat := [2, 2, 1, 4, 2, 2, 3, 1, 2, 4]
def baseStart_3065292 : Nat := 118140960795 + 3065292 * 2 ^ 59
def prefixEnd_3065292 : Nat := 4983230072969 + 3 ^ 40 * 3065292 * 2
def baseEnd_3065292 : Nat := 524656047460575421550995

theorem tailTrace_3065292 : CollatzResearch.WordTrace tailWord_3065292 prefixEnd_3065292 524656047460575421550995 := by
  unfold tailWord_3065292
  simp only [CollatzResearch.WordTrace]
  refine ⟨55900192005489034519967065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74533589340652046026622753 55900192005489034519967065)
  ·
    refine ⟨41925144004116775889975299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55900192005489034519967065 41925144004116775889975299)
    ·
      refine ⟨62887716006175163834962949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41925144004116775889975299 62887716006175163834962949)
      ·
        refine ⟨11791446751157843219055553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62887716006175163834962949 11791446751157843219055553)
        ·
          refine ⟨8843585063368382414291665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11791446751157843219055553 8843585063368382414291665)
          ·
            refine ⟨6632688797526286810718749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8843585063368382414291665 6632688797526286810718749)
            ·
              refine ⟨2487258299072357554019531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6632688797526286810718749 2487258299072357554019531)
              ·
                refine ⟨3730887448608536331029297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2487258299072357554019531 3730887448608536331029297)
                ·
                  refine ⟨2798165586456402248271973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3730887448608536331029297 2798165586456402248271973)
                  ·
                    refine ⟨524656047460575421550995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2798165586456402248271973 524656047460575421550995)
                    ·
                      rfl

theorem cell23_3065292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_3065292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065292 prefixEnd_3065292 := by exact prefixLift 3065292
  have htrace : WordTrace (prefixWord ++ tailWord_3065292) baseStart_3065292 baseEnd_3065292 := by
    simpa [prefixWord, tailWord_3065292, baseEnd_3065292] using wordTrace_append hprefix tailTrace_3065292
  have hstable : (prefixWord ++ tailWord_3065292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065292).length < 2 ^ (prefixWord ++ tailWord_3065292).sum := by decide
  have hdescent : baseEnd_3065292 < baseStart_3065292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065302 : List Nat := [5, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_3065302 : Nat := 118140960795 + 3065302 * 2 ^ 59
def prefixEnd_3065302 : Nat := 4983230072969 + 3 ^ 40 * 3065302 * 2
def baseEnd_3065302 : Nat := 1573973277188271225527939

theorem tailTrace_3065302 : CollatzResearch.WordTrace tailWord_3065302 prefixEnd_3065302 1573973277188271225527939 := by
  unfold tailWord_3065302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6987546796308865046737385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74533832493961227165198773 6987546796308865046737385)
  ·
    refine ⟨5240660097231648785053039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6987546796308865046737385 5240660097231648785053039)
    ·
      refine ⟨7860990145847473177579559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5240660097231648785053039 7860990145847473177579559)
      ·
        refine ⟨11791485218771209766369339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7860990145847473177579559 11791485218771209766369339)
        ·
          refine ⟨17687227828156814649554009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11791485218771209766369339 17687227828156814649554009)
          ·
            refine ⟨13265420871117610987165507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17687227828156814649554009 13265420871117610987165507)
            ·
              refine ⟨19898131306676416480748261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13265420871117610987165507 19898131306676416480748261)
              ·
                refine ⟨3730899620001828090140299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19898131306676416480748261 3730899620001828090140299)
                ·
                  refine ⟨5596349430002742135210449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3730899620001828090140299 5596349430002742135210449)
                  ·
                    refine ⟨4197262072502056601407837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5596349430002742135210449 4197262072502056601407837)
                    ·
                      refine ⟨1573973277188271225527939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4197262072502056601407837 1573973277188271225527939)
                      ·
                        rfl

theorem cell23_3065302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_3065302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065302 prefixEnd_3065302 := by exact prefixLift 3065302
  have htrace : WordTrace (prefixWord ++ tailWord_3065302) baseStart_3065302 baseEnd_3065302 := by
    simpa [prefixWord, tailWord_3065302, baseEnd_3065302] using wordTrace_append hprefix tailTrace_3065302
  have hstable : (prefixWord ++ tailWord_3065302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065302).length < 2 ^ (prefixWord ++ tailWord_3065302).sum := by decide
  have hdescent : baseEnd_3065302 < baseStart_3065302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065311 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 5]
def baseStart_3065311 : Nat := 118140960795 + 3065311 * 2 ^ 59
def prefixEnd_3065311 : Nat := 4983230072969 + 3 ^ 40 * 3065311 * 2
def baseEnd_3065311 : Nat := 1573977898514161690315397

theorem tailTrace_3065311 : CollatzResearch.WordTrace tailWord_3065311 prefixEnd_3065311 1573977898514161690315397 := by
  unfold tailWord_3065311
  simp only [CollatzResearch.WordTrace]
  refine ⟨111801076997909235284875787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74534051331939490189917191 111801076997909235284875787)
  ·
    refine ⟨167701615496863852927313681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111801076997909235284875787 167701615496863852927313681)
    ·
      refine ⟨125776211622647889695485261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167701615496863852927313681 125776211622647889695485261)
      ·
        refine ⟨47166079358492958635806973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125776211622647889695485261 47166079358492958635806973)
        ·
          refine ⟨17687279759434859488427615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47166079358492958635806973 17687279759434859488427615)
          ·
            refine ⟨26530919639152289232641423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17687279759434859488427615 26530919639152289232641423)
            ·
              refine ⟨39796379458728433848962135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26530919639152289232641423 39796379458728433848962135)
              ·
                refine ⟨59694569188092650773443203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39796379458728433848962135 59694569188092650773443203)
                ·
                  refine ⟨89541853782138976160164805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59694569188092650773443203 89541853782138976160164805)
                  ·
                    refine ⟨16789097584151058030030901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89541853782138976160164805 16789097584151058030030901)
                    ·
                      refine ⟨1573977898514161690315397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16789097584151058030030901 1573977898514161690315397)
                      ·
                        rfl

theorem cell23_3065311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_3065311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065311 prefixEnd_3065311 := by exact prefixLift 3065311
  have htrace : WordTrace (prefixWord ++ tailWord_3065311) baseStart_3065311 baseEnd_3065311 := by
    simpa [prefixWord, tailWord_3065311, baseEnd_3065311] using wordTrace_append hprefix tailTrace_3065311
  have hstable : (prefixWord ++ tailWord_3065311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065311).length < 2 ^ (prefixWord ++ tailWord_3065311).sum := by decide
  have hdescent : baseEnd_3065311 < baseStart_3065311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065315 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 4, 1, 3]
def baseStart_3065315 : Nat := 118140960795 + 3065315 * 2 ^ 59
def prefixEnd_3065315 : Nat := 4983230072969 + 3 ^ 40 * 3065315 * 2
def baseEnd_3065315 : Nat := 1573979952436779674665379

theorem tailTrace_3065315 : CollatzResearch.WordTrace tailWord_3065315 prefixEnd_3065315 1573979952436779674665379 := by
  unfold tailWord_3065315
  simp only [CollatzResearch.WordTrace]
  refine ⟨111801222889894743968021399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74534148593263162645347599 111801222889894743968021399)
  ·
    refine ⟨167701834334842115952032099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111801222889894743968021399 167701834334842115952032099)
    ·
      refine ⟨251552751502263173928048149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167701834334842115952032099 251552751502263173928048149)
      ·
        refine ⟨11791535226668586277877257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 251552751502263173928048149 11791535226668586277877257)
        ·
          refine ⟨8843651420001439708407943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11791535226668586277877257 8843651420001439708407943)
          ·
            refine ⟨13265477130002159562611915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8843651420001439708407943 13265477130002159562611915)
            ·
              refine ⟨19898215695003239343917873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13265477130002159562611915 19898215695003239343917873)
              ·
                refine ⟨14923661771252429507938405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19898215695003239343917873 14923661771252429507938405)
                ·
                  refine ⟨2798186582109830532738451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14923661771252429507938405 2798186582109830532738451)
                  ·
                    refine ⟨4197279873164745799107677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2798186582109830532738451 4197279873164745799107677)
                    ·
                      refine ⟨1573979952436779674665379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4197279873164745799107677 1573979952436779674665379)
                      ·
                        rfl

theorem cell23_3065315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_3065315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065315 prefixEnd_3065315 := by exact prefixLift 3065315
  have htrace : WordTrace (prefixWord ++ tailWord_3065315) baseStart_3065315 baseEnd_3065315 := by
    simpa [prefixWord, tailWord_3065315, baseEnd_3065315] using wordTrace_append hprefix tailTrace_3065315
  have hstable : (prefixWord ++ tailWord_3065315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065315).length < 2 ^ (prefixWord ++ tailWord_3065315).sum := by decide
  have hdescent : baseEnd_3065315 < baseStart_3065315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065331 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 2, 6]
def baseStart_3065331 : Nat := 118140960795 + 3065331 * 2 ^ 59
def prefixEnd_3065331 : Nat := 4983230072969 + 3 ^ 40 * 3065331 * 2
def baseEnd_3065331 : Nat := 524662722709083870688435

theorem tailTrace_3065331 : CollatzResearch.WordTrace tailWord_3065331 prefixEnd_3065331 524662722709083870688435 := by
  unfold tailWord_3065331
  simp only [CollatzResearch.WordTrace]
  refine ⟨111801806457836778700603847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74534537638557852467069231 111801806457836778700603847)
  ·
    refine ⟨167702709686755168050905771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111801806457836778700603847 167702709686755168050905771)
    ·
      refine ⟨251554064530132752076358657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167702709686755168050905771 251554064530132752076358657)
      ·
        refine ⟨188665548397599564057268993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251554064530132752076358657 188665548397599564057268993)
        ·
          refine ⟨141499161298199673042951745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188665548397599564057268993 141499161298199673042951745)
          ·
            refine ⟨106124370973649754782213809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141499161298199673042951745 106124370973649754782213809)
            ·
              refine ⟨79593278230237316086660357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106124370973649754782213809 79593278230237316086660357)
              ·
                refine ⟨14923739668169496766248817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79593278230237316086660357 14923739668169496766248817)
                ·
                  refine ⟨11192804751127122574686613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14923739668169496766248817 11192804751127122574686613)
                  ·
                    refine ⟨524662722709083870688435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11192804751127122574686613 524662722709083870688435)
                    ·
                      rfl

theorem cell23_3065331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 6].length) (baseStart_3065331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065331 prefixEnd_3065331 := by exact prefixLift 3065331
  have htrace : WordTrace (prefixWord ++ tailWord_3065331) baseStart_3065331 baseEnd_3065331 := by
    simpa [prefixWord, tailWord_3065331, baseEnd_3065331] using wordTrace_append hprefix tailTrace_3065331
  have hstable : (prefixWord ++ tailWord_3065331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065331).length < 2 ^ (prefixWord ++ tailWord_3065331).sum := by decide
  have hdescent : baseEnd_3065331 < baseStart_3065331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065333 : List Nat := [1, 3, 5, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_3065333 : Nat := 118140960795 + 3065333 * 2 ^ 59
def prefixEnd_3065333 : Nat := 4983230072969 + 3 ^ 40 * 3065333 * 2
def baseEnd_3065333 : Nat := 1573989195088560604240297

theorem tailTrace_3065333 : CollatzResearch.WordTrace tailWord_3065333 prefixEnd_3065333 1573989195088560604240297 := by
  unfold tailWord_3065333
  simp only [CollatzResearch.WordTrace]
  refine ⟨111801879403829533042176653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74534586269219688694784435 111801879403829533042176653)
  ·
    refine ⟨41925704776436074890816245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111801879403829533042176653 41925704776436074890816245)
    ·
      refine ⟨3930534822790882021014023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41925704776436074890816245 3930534822790882021014023)
      ·
        refine ⟨5895802234186323031521035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3930534822790882021014023 5895802234186323031521035)
        ·
          refine ⟨8843703351279484547281553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5895802234186323031521035 8843703351279484547281553)
          ·
            refine ⟨6632777513459613410461165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8843703351279484547281553 6632777513459613410461165)
            ·
              refine ⟨2487291567547355028922937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6632777513459613410461165 2487291567547355028922937)
              ·
                refine ⟨1865468675660516271692203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2487291567547355028922937 1865468675660516271692203)
                ·
                  refine ⟨2798203013490774407538305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865468675660516271692203 2798203013490774407538305)
                  ·
                    refine ⟨2098652260118080805653729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2798203013490774407538305 2098652260118080805653729)
                    ·
                      refine ⟨1573989195088560604240297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2098652260118080805653729 1573989195088560604240297)
                      ·
                        rfl

theorem cell23_3065333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_3065333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065333 prefixEnd_3065333 := by exact prefixLift 3065333
  have htrace : WordTrace (prefixWord ++ tailWord_3065333) baseStart_3065333 baseEnd_3065333 := by
    simpa [prefixWord, tailWord_3065333, baseEnd_3065333] using wordTrace_append hprefix tailTrace_3065333
  have hstable : (prefixWord ++ tailWord_3065333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065333).length < 2 ^ (prefixWord ++ tailWord_3065333).sum := by decide
  have hdescent : baseEnd_3065333 < baseStart_3065333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065361 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 9]
def baseStart_3065361 : Nat := 118140960795 + 3065361 * 2 ^ 59
def prefixEnd_3065361 : Nat := 4983230072969 + 3 ^ 40 * 3065361 * 2
def baseEnd_3065361 : Nat := 174889285838542943854463

theorem tailTrace_3065361 : CollatzResearch.WordTrace tailWord_3065361 prefixEnd_3065361 174889285838542943854463 := by
  unfold tailWord_3065361
  simp only [CollatzResearch.WordTrace]
  refine ⟨111802900647728093824195937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74535267098485395882797291 111802900647728093824195937)
  ·
    refine ⟨83852175485796070368146953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111802900647728093824195937 83852175485796070368146953)
    ·
      refine ⟨62889131614347052776110215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83852175485796070368146953 62889131614347052776110215)
      ·
        refine ⟨94333697421520579164165323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62889131614347052776110215 94333697421520579164165323)
        ·
          refine ⟨141500546132280868746247985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94333697421520579164165323 141500546132280868746247985)
          ·
            refine ⟨106125409599210651559685989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141500546132280868746247985 106125409599210651559685989)
            ·
              refine ⟨19898514299851997167441123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106125409599210651559685989 19898514299851997167441123)
              ·
                refine ⟨29847771449777995751161685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19898514299851997167441123 29847771449777995751161685)
                ·
                  refine ⟨174889285838542943854463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29847771449777995751161685 174889285838542943854463)
                  ·
                    rfl

theorem cell23_3065361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 9].length) (baseStart_3065361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065361 prefixEnd_3065361 := by exact prefixLift 3065361
  have htrace : WordTrace (prefixWord ++ tailWord_3065361) baseStart_3065361 baseEnd_3065361 := by
    simpa [prefixWord, tailWord_3065361, baseEnd_3065361] using wordTrace_append hprefix tailTrace_3065361
  have hstable : (prefixWord ++ tailWord_3065361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065361).length < 2 ^ (prefixWord ++ tailWord_3065361).sum := by decide
  have hdescent : baseEnd_3065361 < baseStart_3065361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065395 : List Nat := [1, 1, 1, 2, 4, 4, 1, 4, 5]
def baseStart_3065395 : Nat := 118140960795 + 3065395 * 2 ^ 59
def prefixEnd_3065395 : Nat := 4983230072969 + 3 ^ 40 * 3065395 * 2
def baseEnd_3065395 : Nat := 174891225654348817962779

theorem tailTrace_3065395 : CollatzResearch.WordTrace tailWord_3065395 prefixEnd_3065395 174891225654348817962779 := by
  unfold tailWord_3065395
  simp only [CollatzResearch.WordTrace]
  refine ⟨111804140729604917630933639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74536093819736611753955759 111804140729604917630933639)
  ·
    refine ⟨167706211094407376446400459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111804140729604917630933639 167706211094407376446400459)
    ·
      refine ⟨251559316641611064669600689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167706211094407376446400459 251559316641611064669600689)
      ·
        refine ⟨188669487481208298502200517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251559316641611064669600689 188669487481208298502200517)
        ·
          refine ⟨35375528902726555969162597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188669487481208298502200517 35375528902726555969162597)
          ·
            refine ⟨6632911669261229244217987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35375528902726555969162597 6632911669261229244217987)
            ·
              refine ⟨9949367503891843866326981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6632911669261229244217987 9949367503891843866326981)
              ·
                refine ⟨1865506406979720724936309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9949367503891843866326981 1865506406979720724936309)
                ·
                  refine ⟨174891225654348817962779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1865506406979720724936309 174891225654348817962779)
                  ·
                    rfl

theorem cell23_3065395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 5].length) (baseStart_3065395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065395 prefixEnd_3065395 := by exact prefixLift 3065395
  have htrace : WordTrace (prefixWord ++ tailWord_3065395) baseStart_3065395 baseEnd_3065395 := by
    simpa [prefixWord, tailWord_3065395, baseEnd_3065395] using wordTrace_append hprefix tailTrace_3065395
  have hstable : (prefixWord ++ tailWord_3065395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065395).length < 2 ^ (prefixWord ++ tailWord_3065395).sum := by decide
  have hdescent : baseEnd_3065395 < baseStart_3065395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065506 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_3065506 : Nat := 118140960795 + 3065506 * 2 ^ 59
def prefixEnd_3065506 : Nat := 4983230072969 + 3 ^ 40 * 3065506 * 2
def baseEnd_3065506 : Nat := 524692675747262809125667

theorem tailTrace_3065506 : CollatzResearch.WordTrace tailWord_3065506 prefixEnd_3065506 524692675747262809125667 := by
  unfold tailWord_3065506
  simp only [CollatzResearch.WordTrace]
  refine ⟨27952047308050695897056093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74538792821468522392149581 27952047308050695897056093)
  ·
    refine ⟨10482017740519010961396035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27952047308050695897056093 10482017740519010961396035)
    ·
      refine ⟨15723026610778516442094053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10482017740519010961396035 15723026610778516442094053)
      ·
        refine ⟨2948067489520971832892635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15723026610778516442094053 2948067489520971832892635)
        ·
          refine ⟨4422101234281457749338953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2948067489520971832892635 4422101234281457749338953)
          ·
            refine ⟨3316575925711093312004215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4422101234281457749338953 3316575925711093312004215)
            ·
              refine ⟨4974863888566639968006323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316575925711093312004215 4974863888566639968006323)
              ·
                refine ⟨7462295832849959952009485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4974863888566639968006323 7462295832849959952009485)
                ·
                  refine ⟨2798360937318734982003557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7462295832849959952009485 2798360937318734982003557)
                  ·
                    refine ⟨524692675747262809125667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2798360937318734982003557 524692675747262809125667)
                    ·
                      rfl

theorem cell23_3065506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_3065506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065506 prefixEnd_3065506 := by exact prefixLift 3065506
  have htrace : WordTrace (prefixWord ++ tailWord_3065506) baseStart_3065506 baseEnd_3065506 := by
    simpa [prefixWord, tailWord_3065506, baseEnd_3065506] using wordTrace_append hprefix tailTrace_3065506
  have hstable : (prefixWord ++ tailWord_3065506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065506).length < 2 ^ (prefixWord ++ tailWord_3065506).sum := by decide
  have hdescent : baseEnd_3065506 < baseStart_3065506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065528 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 5, 6]
def baseStart_3065528 : Nat := 118140960795 + 3065528 * 2 ^ 59
def prefixEnd_3065528 : Nat := 4983230072969 + 3 ^ 40 * 3065528 * 2
def baseEnd_3065528 : Nat := 524696441272062447100633

theorem tailTrace_3065528 : CollatzResearch.WordTrace tailWord_3065528 prefixEnd_3065528 524696441272062447100633 := by
  unfold tailWord_3065528
  simp only [CollatzResearch.WordTrace]
  refine ⟨55904495819061540672762619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74539327758748720897016825 55904495819061540672762619)
  ·
    refine ⟨83856743728592311009143929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55904495819061540672762619 83856743728592311009143929)
    ·
      refine ⟨62892557796444233256857947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83856743728592311009143929 62892557796444233256857947)
      ·
        refine ⟨94338836694666349885286921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62892557796444233256857947 94338836694666349885286921)
        ·
          refine ⟨70754127520999762413965191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94338836694666349885286921 70754127520999762413965191)
          ·
            refine ⟨106131191281499643620947787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70754127520999762413965191 106131191281499643620947787)
            ·
              refine ⟨159196786922249465431421681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106131191281499643620947787 159196786922249465431421681)
              ·
                refine ⟨119397590191687099073566261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159196786922249465431421681 119397590191687099073566261)
                ·
                  refine ⟨11193524080470665538146837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119397590191687099073566261 11193524080470665538146837)
                  ·
                    refine ⟨524696441272062447100633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11193524080470665538146837 524696441272062447100633)
                    ·
                      rfl

theorem cell23_3065528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_3065528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065528 prefixEnd_3065528 := by exact prefixLift 3065528
  have htrace : WordTrace (prefixWord ++ tailWord_3065528) baseStart_3065528 baseEnd_3065528 := by
    simpa [prefixWord, tailWord_3065528, baseEnd_3065528] using wordTrace_append hprefix tailTrace_3065528
  have hstable : (prefixWord ++ tailWord_3065528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065528).length < 2 ^ (prefixWord ++ tailWord_3065528).sum := by decide
  have hdescent : baseEnd_3065528 < baseStart_3065528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065532 : List Nat := [2, 2, 2, 3, 1, 2, 3, 2, 1, 5]
def baseStart_3065532 : Nat := 118140960795 + 3065532 * 2 ^ 59
def prefixEnd_3065532 : Nat := 4983230072969 + 3 ^ 40 * 3065532 * 2
def baseEnd_3065532 : Nat := 524697125912935108550627

theorem tailTrace_3065532 : CollatzResearch.WordTrace tailWord_3065532 prefixEnd_3065532 524697125912935108550627 := by
  unfold tailWord_3065532
  simp only [CollatzResearch.WordTrace]
  refine ⟨55904568765054295014335425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74539425020072393352447233 55904568765054295014335425)
  ·
    refine ⟨41928426573790721260751569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55904568765054295014335425 41928426573790721260751569)
    ·
      refine ⟨31446319930343040945563677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41928426573790721260751569 31446319930343040945563677)
      ·
        refine ⟨11792369973878640354586379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31446319930343040945563677 11792369973878640354586379)
        ·
          refine ⟨17688554960817960531879569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11792369973878640354586379 17688554960817960531879569)
          ·
            refine ⟨13266416220613470398909677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17688554960817960531879569 13266416220613470398909677)
            ·
              refine ⟨4974906082730051399591129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13266416220613470398909677 4974906082730051399591129)
              ·
                refine ⟨3731179562047538549693347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4974906082730051399591129 3731179562047538549693347)
                ·
                  refine ⟨5596769343071307824540021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731179562047538549693347 5596769343071307824540021)
                  ·
                    refine ⟨524697125912935108550627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5596769343071307824540021 524697125912935108550627)
                    ·
                      rfl

theorem cell23_3065532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_3065532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065532 prefixEnd_3065532 := by exact prefixLift 3065532
  have htrace : WordTrace (prefixWord ++ tailWord_3065532) baseStart_3065532 baseEnd_3065532 := by
    simpa [prefixWord, tailWord_3065532, baseEnd_3065532] using wordTrace_append hprefix tailTrace_3065532
  have hstable : (prefixWord ++ tailWord_3065532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065532).length < 2 ^ (prefixWord ++ tailWord_3065532).sum := by decide
  have hdescent : baseEnd_3065532 < baseStart_3065532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065535 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 4]
def baseStart_3065535 : Nat := 118140960795 + 3065535 * 2 ^ 59
def prefixEnd_3065535 : Nat := 4983230072969 + 3 ^ 40 * 3065535 * 2
def baseEnd_3065535 : Nat := 1574092918180768813914367

theorem tailTrace_3065535 : CollatzResearch.WordTrace tailWord_3065535 prefixEnd_3065535 1574092918180768813914367 := by
  unfold tailWord_3065535
  simp only [CollatzResearch.WordTrace]
  refine ⟨111809246949097721541030059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74539497966065147694020039 111809246949097721541030059)
  ·
    refine ⟨167713870423646582311545089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111809246949097721541030059 167713870423646582311545089)
    ·
      refine ⟨125785402817734936733658817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167713870423646582311545089 125785402817734936733658817)
      ·
        refine ⟨94339052113301202550244113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125785402817734936733658817 94339052113301202550244113)
        ·
          refine ⟨70754289084975901912683085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94339052113301202550244113 70754289084975901912683085)
          ·
            refine ⟨26532858406865963217256157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70754289084975901912683085 26532858406865963217256157)
            ·
              refine ⟨9949821902574736206471059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26532858406865963217256157 9949821902574736206471059)
              ·
                refine ⟨14924732853862104309706589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9949821902574736206471059 14924732853862104309706589)
                ·
                  refine ⟨5596774820198289116139971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14924732853862104309706589 5596774820198289116139971)
                  ·
                    refine ⟨8395162230297433674209957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5596774820198289116139971 8395162230297433674209957)
                    ·
                      refine ⟨1574092918180768813914367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8395162230297433674209957 1574092918180768813914367)
                      ·
                        rfl

theorem cell23_3065535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_3065535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065535 prefixEnd_3065535 := by exact prefixLift 3065535
  have htrace : WordTrace (prefixWord ++ tailWord_3065535) baseStart_3065535 baseEnd_3065535 := by
    simpa [prefixWord, tailWord_3065535, baseEnd_3065535] using wordTrace_append hprefix tailTrace_3065535
  have hstable : (prefixWord ++ tailWord_3065535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065535).length < 2 ^ (prefixWord ++ tailWord_3065535).sum := by decide
  have hdescent : baseEnd_3065535 < baseStart_3065535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065552 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 7, 2, 2]
def baseStart_3065552 : Nat := 118140960795 + 3065552 * 2 ^ 59
def prefixEnd_3065552 : Nat := 4983230072969 + 3 ^ 40 * 3065552 * 2
def baseEnd_3065552 : Nat := 1574101647351895247401789

theorem tailTrace_3065552 : CollatzResearch.WordTrace tailWord_3065552 prefixEnd_3065552 1574101647351895247401789 := by
  unfold tailWord_3065552
  simp only [CollatzResearch.WordTrace]
  refine ⟨55904933495018066722199455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74539911326690755629599273 55904933495018066722199455)
  ·
    refine ⟨83857400242527100083299183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55904933495018066722199455 83857400242527100083299183)
    ·
      refine ⟨125786100363790650124948775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83857400242527100083299183 125786100363790650124948775)
      ·
        refine ⟨188679150545685975187423163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125786100363790650124948775 188679150545685975187423163)
        ·
          refine ⟨283018725818528962781134745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188679150545685975187423163 283018725818528962781134745)
          ·
            refine ⟨212264044363896722085851059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283018725818528962781134745 212264044363896722085851059)
            ·
              refine ⟨318396066545845083128776589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212264044363896722085851059 318396066545845083128776589)
              ·
                refine ⟨119398524954691906173291221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318396066545845083128776589 119398524954691906173291221)
                ·
                  refine ⟨2798402928625591550936513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 119398524954691906173291221 2798402928625591550936513)
                  ·
                    refine ⟨2098802196469193663202385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2798402928625591550936513 2098802196469193663202385)
                    ·
                      refine ⟨1574101647351895247401789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2098802196469193663202385 1574101647351895247401789)
                      ·
                        rfl

theorem cell23_3065552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 7, 2, 2].length) (baseStart_3065552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065552 prefixEnd_3065552 := by exact prefixLift 3065552
  have htrace : WordTrace (prefixWord ++ tailWord_3065552) baseStart_3065552 baseEnd_3065552 := by
    simpa [prefixWord, tailWord_3065552, baseEnd_3065552] using wordTrace_append hprefix tailTrace_3065552
  have hstable : (prefixWord ++ tailWord_3065552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065552).length < 2 ^ (prefixWord ++ tailWord_3065552).sum := by decide
  have hdescent : baseEnd_3065552 < baseStart_3065552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065562 : List Nat := [3, 1, 1, 2, 2, 3, 1, 4, 2, 4]
def baseStart_3065562 : Nat := 118140960795 + 3065562 * 2 ^ 59
def prefixEnd_3065562 : Nat := 4983230072969 + 3 ^ 40 * 3065562 * 2
def baseEnd_3065562 : Nat := 524702260719480069425581

theorem tailTrace_3065562 : CollatzResearch.WordTrace tailWord_3065562 prefixEnd_3065562 524702260719480069425581 := by
  unfold tailWord_3065562
  simp only [CollatzResearch.WordTrace]
  refine ⟨27952557929999976288065735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74540154479999936768175293 27952557929999976288065735)
  ·
    refine ⟨41928836894999964432098603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27952557929999976288065735 41928836894999964432098603)
    ·
      refine ⟨62893255342499946648147905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41928836894999964432098603 62893255342499946648147905)
      ·
        refine ⟨47169941506874959986110929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62893255342499946648147905 47169941506874959986110929)
        ·
          refine ⟨35377456130156219989583197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47169941506874959986110929 35377456130156219989583197)
          ·
            refine ⟨13266546048808582496093699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35377456130156219989583197 13266546048808582496093699)
            ·
              refine ⟨19899819073212873744140549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13266546048808582496093699 19899819073212873744140549)
              ·
                refine ⟨3731216076227413827026353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19899819073212873744140549 3731216076227413827026353)
                ·
                  refine ⟨2798412057170560370269765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3731216076227413827026353 2798412057170560370269765)
                  ·
                    refine ⟨524702260719480069425581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2798412057170560370269765 524702260719480069425581)
                    ·
                      rfl

theorem cell23_3065562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_3065562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065562 prefixEnd_3065562 := by exact prefixLift 3065562
  have htrace : WordTrace (prefixWord ++ tailWord_3065562) baseStart_3065562 baseEnd_3065562 := by
    simpa [prefixWord, tailWord_3065562, baseEnd_3065562] using wordTrace_append hprefix tailTrace_3065562
  have hstable : (prefixWord ++ tailWord_3065562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065562).length < 2 ^ (prefixWord ++ tailWord_3065562).sum := by decide
  have hdescent : baseEnd_3065562 < baseStart_3065562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065582 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_3065582 : Nat := 118140960795 + 3065582 * 2 ^ 59
def prefixEnd_3065582 : Nat := 4983230072969 + 3 ^ 40 * 3065582 * 2
def baseEnd_3065582 : Nat := 1574117051771530130026651

theorem tailTrace_3065582 : CollatzResearch.WordTrace tailWord_3065582 prefixEnd_3065582 1574117051771530130026651 := by
  unfold tailWord_3065582
  simp only [CollatzResearch.WordTrace]
  refine ⟨13976370147490931070998875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74540640786618299045327333 13976370147490931070998875)
  ·
    refine ⟨20964555221236396606498313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13976370147490931070998875 20964555221236396606498313)
    ·
      refine ⟨15723416415927297454873735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20964555221236396606498313 15723416415927297454873735)
      ·
        refine ⟨23585124623890946182310603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15723416415927297454873735 23585124623890946182310603)
        ·
          refine ⟨35377686935836419273465905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23585124623890946182310603 35377686935836419273465905)
          ·
            refine ⟨26533265201877314455099429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35377686935836419273465905 26533265201877314455099429)
            ·
              refine ⟨4974987225351996460331143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26533265201877314455099429 4974987225351996460331143)
              ·
                refine ⟨7462480838027994690496715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4974987225351996460331143 7462480838027994690496715)
                ·
                  refine ⟨11193721257041992035745073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7462480838027994690496715 11193721257041992035745073)
                  ·
                    refine ⟨8395290942781494026808805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11193721257041992035745073 8395290942781494026808805)
                    ·
                      refine ⟨1574117051771530130026651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8395290942781494026808805 1574117051771530130026651)
                      ·
                        rfl

theorem cell23_3065582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_3065582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065582 prefixEnd_3065582 := by exact prefixLift 3065582
  have htrace : WordTrace (prefixWord ++ tailWord_3065582) baseStart_3065582 baseEnd_3065582 := by
    simpa [prefixWord, tailWord_3065582, baseEnd_3065582] using wordTrace_append hprefix tailTrace_3065582
  have hstable : (prefixWord ++ tailWord_3065582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065582).length < 2 ^ (prefixWord ++ tailWord_3065582).sum := by decide
  have hdescent : baseEnd_3065582 < baseStart_3065582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065630 : List Nat := [4, 3, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3065630 : Nat := 118140960795 + 3065630 * 2 ^ 59
def prefixEnd_3065630 : Nat := 4983230072969 + 3 ^ 40 * 3065630 * 2
def baseEnd_3065630 : Nat := 524713899614315314075477

theorem tailTrace_3065630 : CollatzResearch.WordTrace tailWord_3065630 prefixEnd_3065630 524713899614315314075477 := by
  unfold tailWord_3065630
  simp only [CollatzResearch.WordTrace]
  refine ⟨13976588985469194095717293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74541807922502368510492229 13976588985469194095717293)
  ·
    refine ⟨5241220869550947785893985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13976588985469194095717293 5241220869550947785893985)
    ·
      refine ⟨3930915652163210839420489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5241220869550947785893985 3930915652163210839420489)
      ·
        refine ⟨2948186739122408129565367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3930915652163210839420489 2948186739122408129565367)
        ·
          refine ⟨4422280108683612194348051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2948186739122408129565367 4422280108683612194348051)
          ·
            refine ⟨6633420163025418291522077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4422280108683612194348051 6633420163025418291522077)
            ·
              refine ⟨2487532561134531859320779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6633420163025418291522077 2487532561134531859320779)
              ·
                refine ⟨3731298841701797788981169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2487532561134531859320779 3731298841701797788981169)
                ·
                  refine ⟨2798474131276348341735877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3731298841701797788981169 2798474131276348341735877)
                  ·
                    refine ⟨524713899614315314075477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2798474131276348341735877 524713899614315314075477)
                    ·
                      rfl

theorem cell23_3065630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3065630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065630 prefixEnd_3065630 := by exact prefixLift 3065630
  have htrace : WordTrace (prefixWord ++ tailWord_3065630) baseStart_3065630 baseEnd_3065630 := by
    simpa [prefixWord, tailWord_3065630, baseEnd_3065630] using wordTrace_append hprefix tailTrace_3065630
  have hstable : (prefixWord ++ tailWord_3065630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065630).length < 2 ^ (prefixWord ++ tailWord_3065630).sum := by decide
  have hdescent : baseEnd_3065630 < baseStart_3065630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065635 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 2, 6]
def baseStart_3065635 : Nat := 118140960795 + 3065635 * 2 ^ 59
def prefixEnd_3065635 : Nat := 4983230072969 + 3 ^ 40 * 3065635 * 2
def baseEnd_3065635 : Nat := 524714755415406140887969

theorem tailTrace_3065635 : CollatzResearch.WordTrace tailWord_3065635 prefixEnd_3065635 524714755415406140887969 := by
  unfold tailWord_3065635
  simp only [CollatzResearch.WordTrace]
  refine ⟨111812894248735438619670359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74541929499156959079780239 111812894248735438619670359)
  ·
    refine ⟨167719341373103157929505539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111812894248735438619670359 167719341373103157929505539)
    ·
      refine ⟨251579012059654736894258309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167719341373103157929505539 251579012059654736894258309)
      ·
        refine ⟨47171064761185263167673433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251579012059654736894258309 47171064761185263167673433)
        ·
          refine ⟨35378298570888947375755075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47171064761185263167673433 35378298570888947375755075)
          ·
            refine ⟨53067447856333421063632613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35378298570888947375755075 53067447856333421063632613)
            ·
              refine ⟨9950146473062516449431115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53067447856333421063632613 9950146473062516449431115)
              ·
                refine ⟨14925219709593774674146673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9950146473062516449431115 14925219709593774674146673)
                ·
                  refine ⟨11193914782195331005610005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14925219709593774674146673 11193914782195331005610005)
                  ·
                    refine ⟨524714755415406140887969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11193914782195331005610005 524714755415406140887969)
                    ·
                      rfl

theorem cell23_3065635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 6].length) (baseStart_3065635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065635 prefixEnd_3065635 := by exact prefixLift 3065635
  have htrace : WordTrace (prefixWord ++ tailWord_3065635) baseStart_3065635 baseEnd_3065635 := by
    simpa [prefixWord, tailWord_3065635, baseEnd_3065635] using wordTrace_append hprefix tailTrace_3065635
  have hstable : (prefixWord ++ tailWord_3065635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065635).length < 2 ^ (prefixWord ++ tailWord_3065635).sum := by decide
  have hdescent : baseEnd_3065635 < baseStart_3065635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065655 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_3065655 : Nat := 118140960795 + 3065655 * 2 ^ 59
def prefixEnd_3065655 : Nat := 4983230072969 + 3 ^ 40 * 3065655 * 2
def baseEnd_3065655 : Nat := 1574154535859308344413815

theorem tailTrace_3065655 : CollatzResearch.WordTrace tailWord_3065655 prefixEnd_3065655 1574154535859308344413815 := by
  unfold tailWord_3065655
  simp only [CollatzResearch.WordTrace]
  refine ⟨111813623708662982035398419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74542415805775321356932279 111813623708662982035398419)
  ·
    refine ⟨167720435562994473053097629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111813623708662982035398419 167720435562994473053097629)
    ·
      refine ⟨62895163336122927394911611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167720435562994473053097629 62895163336122927394911611)
      ·
        refine ⟨94342745004184391092367417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62895163336122927394911611 94342745004184391092367417)
        ·
          refine ⟨70757058753138293319275563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94342745004184391092367417 70757058753138293319275563)
          ·
            refine ⟨106135588129707439978913345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70757058753138293319275563 106135588129707439978913345)
            ·
              refine ⟨79601691097280579984185009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106135588129707439978913345 79601691097280579984185009)
              ·
                refine ⟨59701268322960434988138757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79601691097280579984185009 59701268322960434988138757)
                ·
                  refine ⟨11193987810555081560276017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59701268322960434988138757 11193987810555081560276017)
                  ·
                    refine ⟨8395490857916311170207013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11193987810555081560276017 8395490857916311170207013)
                    ·
                      refine ⟨1574154535859308344413815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8395490857916311170207013 1574154535859308344413815)
                      ·
                        rfl

theorem cell23_3065655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_3065655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065655 prefixEnd_3065655 := by exact prefixLift 3065655
  have htrace : WordTrace (prefixWord ++ tailWord_3065655) baseStart_3065655 baseEnd_3065655 := by
    simpa [prefixWord, tailWord_3065655, baseEnd_3065655] using wordTrace_append hprefix tailTrace_3065655
  have hstable : (prefixWord ++ tailWord_3065655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065655).length < 2 ^ (prefixWord ++ tailWord_3065655).sum := by decide
  have hdescent : baseEnd_3065655 < baseStart_3065655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065662 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_3065662 : Nat := 118140960795 + 3065662 * 2 ^ 59
def prefixEnd_3065662 : Nat := 4983230072969 + 3 ^ 40 * 3065662 * 2
def baseEnd_3065662 : Nat := 1574158130223889817026283

theorem tailTrace_3065662 : CollatzResearch.WordTrace tailWord_3065662 prefixEnd_3065662 1574158130223889817026283 := by
  unfold tailWord_3065662
  simp only [CollatzResearch.WordTrace]
  refine ⟨13976734877454702778862905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74542586013091748153935493 13976734877454702778862905)
  ·
    refine ⟨10482551158091027084147179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13976734877454702778862905 10482551158091027084147179)
    ·
      refine ⟨15723826737136540626220769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10482551158091027084147179 15723826737136540626220769)
      ·
        refine ⟨11792870052852405469665577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15723826737136540626220769 11792870052852405469665577)
        ·
          refine ⟨8844652539639304102249183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11792870052852405469665577 8844652539639304102249183)
          ·
            refine ⟨13266978809458956153373775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8844652539639304102249183 13266978809458956153373775)
            ·
              refine ⟨19900468214188434230060663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13266978809458956153373775 19900468214188434230060663)
              ·
                refine ⟨29850702321282651345090995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19900468214188434230060663 29850702321282651345090995)
                ·
                  refine ⟨44776053481923977017636493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29850702321282651345090995 44776053481923977017636493)
                  ·
                    refine ⟨16791020055721491381613685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44776053481923977017636493 16791020055721491381613685)
                    ·
                      refine ⟨1574158130223889817026283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16791020055721491381613685 1574158130223889817026283)
                      ·
                        rfl

theorem cell23_3065662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_3065662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065662 prefixEnd_3065662 := by exact prefixLift 3065662
  have htrace : WordTrace (prefixWord ++ tailWord_3065662) baseStart_3065662 baseEnd_3065662 := by
    simpa [prefixWord, tailWord_3065662, baseEnd_3065662] using wordTrace_append hprefix tailTrace_3065662
  have hstable : (prefixWord ++ tailWord_3065662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065662).length < 2 ^ (prefixWord ++ tailWord_3065662).sum := by decide
  have hdescent : baseEnd_3065662 < baseStart_3065662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065682 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 7]
def baseStart_3065682 : Nat := 118140960795 + 3065682 * 2 ^ 59
def prefixEnd_3065682 : Nat := 4983230072969 + 3 ^ 40 * 3065682 * 2
def baseEnd_3065682 : Nat := 174907599981886637641799

theorem tailTrace_3065682 : CollatzResearch.WordTrace tailWord_3065682 prefixEnd_3065682 174907599981886637641799 := by
  unfold tailWord_3065682
  simp only [CollatzResearch.WordTrace]
  refine ⟨27953652119891291411657825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74543072319710110431087533 27953652119891291411657825)
  ·
    refine ⟨20965239089918468558743369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27953652119891291411657825 20965239089918468558743369)
    ·
      refine ⟨15723929317438851419057527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20965239089918468558743369 15723929317438851419057527)
      ·
        refine ⟨23585893976158277128586291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15723929317438851419057527 23585893976158277128586291)
        ·
          refine ⟨35378840964237415692879437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23585893976158277128586291 35378840964237415692879437)
          ·
            refine ⟨13267065361589030884829789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35378840964237415692879437 13267065361589030884829789)
            ·
              refine ⟨4975149510595886581811171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13267065361589030884829789 4975149510595886581811171)
              ·
                refine ⟨7462724265893829872716757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4975149510595886581811171 7462724265893829872716757)
                ·
                  refine ⟨174907599981886637641799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7462724265893829872716757 174907599981886637641799)
                  ·
                    rfl

theorem cell23_3065682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_3065682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065682 prefixEnd_3065682 := by exact prefixLift 3065682
  have htrace : WordTrace (prefixWord ++ tailWord_3065682) baseStart_3065682 baseEnd_3065682 := by
    simpa [prefixWord, tailWord_3065682, baseEnd_3065682] using wordTrace_append hprefix tailTrace_3065682
  have hstable : (prefixWord ++ tailWord_3065682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065682).length < 2 ^ (prefixWord ++ tailWord_3065682).sum := by decide
  have hdescent : baseEnd_3065682 < baseStart_3065682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065749 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 2, 4, 2]
def baseStart_3065749 : Nat := 118140960795 + 3065749 * 2 ^ 59
def prefixEnd_3065749 : Nat := 4983230072969 + 3 ^ 40 * 3065749 * 2
def baseEnd_3065749 : Nat := 1574202803040830976638383

theorem tailTrace_3065749 : CollatzResearch.WordTrace tailWord_3065749 prefixEnd_3065749 1574202803040830976638383 := by
  unfold tailWord_3065749
  simp only [CollatzResearch.WordTrace]
  refine ⟨111817052170322436089320301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74544701446881624059546867 111817052170322436089320301)
  ·
    refine ⟨41931394563870913533495113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111817052170322436089320301 41931394563870913533495113)
    ·
      refine ⟨31448545922903185150121335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41931394563870913533495113 31448545922903185150121335)
      ·
        refine ⟨47172818884354777725182003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31448545922903185150121335 47172818884354777725182003)
        ·
          refine ⟨70759228326532166587773005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47172818884354777725182003 70759228326532166587773005)
          ·
            refine ⟨26534710622449562470414877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70759228326532166587773005 26534710622449562470414877)
            ·
              refine ⟨9950516483418585926405579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26534710622449562470414877 9950516483418585926405579)
              ·
                refine ⟨14925774725127878889608369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9950516483418585926405579 14925774725127878889608369)
                ·
                  refine ⟨11194331043845909167206277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14925774725127878889608369 11194331043845909167206277)
                  ·
                    refine ⟨2098937070721107968851177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11194331043845909167206277 2098937070721107968851177)
                    ·
                      refine ⟨1574202803040830976638383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2098937070721107968851177 1574202803040830976638383)
                      ·
                        rfl

theorem cell23_3065749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_3065749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065749 prefixEnd_3065749 := by exact prefixLift 3065749
  have htrace : WordTrace (prefixWord ++ tailWord_3065749) baseStart_3065749 baseEnd_3065749 := by
    simpa [prefixWord, tailWord_3065749, baseEnd_3065749] using wordTrace_append hprefix tailTrace_3065749
  have hstable : (prefixWord ++ tailWord_3065749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065749).length < 2 ^ (prefixWord ++ tailWord_3065749).sum := by decide
  have hdescent : baseEnd_3065749 < baseStart_3065749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065789 : List Nat := [1, 4, 1, 2, 3, 1, 3, 2, 6]
def baseStart_3065789 : Nat := 118140960795 + 3065789 * 2 ^ 59
def prefixEnd_3065789 : Nat := 4983230072969 + 3 ^ 40 * 3065789 * 2
def baseEnd_3065789 : Nat := 174913704696334535570911

theorem tailTrace_3065789 : CollatzResearch.WordTrace tailWord_3065789 prefixEnd_3065789 174913704696334535570911 := by
  unfold tailWord_3065789
  simp only [CollatzResearch.WordTrace]
  refine ⟨111818511090177522920776421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74545674060118348613850947 111818511090177522920776421)
  ·
    refine ⟨20965970829408285547645579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111818511090177522920776421 20965970829408285547645579)
    ·
      refine ⟨31448956244112428321468369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20965970829408285547645579 31448956244112428321468369)
      ·
        refine ⟨23586717183084321241101277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31448956244112428321468369 23586717183084321241101277)
        ·
          refine ⟨8845018943656620465412979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23586717183084321241101277 8845018943656620465412979)
          ·
            refine ⟨13267528415484930698119469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8845018943656620465412979 13267528415484930698119469)
            ·
              refine ⟨4975323155806849011794801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13267528415484930698119469 4975323155806849011794801)
              ·
                refine ⟨3731492366855136758846101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4975323155806849011794801 3731492366855136758846101)
                ·
                  refine ⟨174913704696334535570911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3731492366855136758846101 174913704696334535570911)
                  ·
                    rfl

theorem cell23_3065789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_3065789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065789 prefixEnd_3065789 := by exact prefixLift 3065789
  have htrace : WordTrace (prefixWord ++ tailWord_3065789) baseStart_3065789 baseEnd_3065789 := by
    simpa [prefixWord, tailWord_3065789, baseEnd_3065789] using wordTrace_append hprefix tailTrace_3065789
  have hstable : (prefixWord ++ tailWord_3065789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065789).length < 2 ^ (prefixWord ++ tailWord_3065789).sum := by decide
  have hdescent : baseEnd_3065789 < baseStart_3065789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065802 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 5, 5]
def baseStart_3065802 : Nat := 118140960795 + 3065802 * 2 ^ 59
def prefixEnd_3065802 : Nat := 4983230072969 + 3 ^ 40 * 3065802 * 2
def baseEnd_3065802 : Nat := 524743339171839756425213

theorem tailTrace_3065802 : CollatzResearch.WordTrace tailWord_3065802 prefixEnd_3065802 524743339171839756425213 := by
  unfold tailWord_3065802
  simp only [CollatzResearch.WordTrace]
  refine ⟨27954746309782606535249915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74545990159420284093999773 27954746309782606535249915)
  ·
    refine ⟨41932119464673909802874873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27954746309782606535249915 41932119464673909802874873)
    ·
      refine ⟨31449089598505432352156155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41932119464673909802874873 31449089598505432352156155)
      ·
        refine ⟨47173634397758148528234233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31449089598505432352156155 47173634397758148528234233)
        ·
          refine ⟨35380225798318611396175675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47173634397758148528234233 35380225798318611396175675)
          ·
            refine ⟨53070338697477917094263513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35380225798318611396175675 53070338697477917094263513)
            ·
              refine ⟨39802754023108437820697635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53070338697477917094263513 39802754023108437820697635)
              ·
                refine ⟨59704131034662656731046453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39802754023108437820697635 59704131034662656731046453)
                ·
                  refine ⟨5597262284499624068535605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59704131034662656731046453 5597262284499624068535605)
                  ·
                    refine ⟨524743339171839756425213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5597262284499624068535605 524743339171839756425213)
                    ·
                      rfl

theorem cell23_3065802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_3065802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065802 prefixEnd_3065802 := by exact prefixLift 3065802
  have htrace : WordTrace (prefixWord ++ tailWord_3065802) baseStart_3065802 baseEnd_3065802 := by
    simpa [prefixWord, tailWord_3065802, baseEnd_3065802] using wordTrace_append hprefix tailTrace_3065802
  have hstable : (prefixWord ++ tailWord_3065802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065802).length < 2 ^ (prefixWord ++ tailWord_3065802).sum := by decide
  have hdescent : baseEnd_3065802 < baseStart_3065802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065809 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 6, 3, 2]
def baseStart_3065809 : Nat := 118140960795 + 3065809 * 2 ^ 59
def prefixEnd_3065809 : Nat := 4983230072969 + 3 ^ 40 * 3065809 * 2
def baseEnd_3065809 : Nat := 1574233611880100741888107

theorem tailTrace_3065809 : CollatzResearch.WordTrace tailWord_3065809 prefixEnd_3065809 1574233611880100741888107 := by
  unfold tailWord_3065809
  simp only [CollatzResearch.WordTrace]
  refine ⟨111819240550105066336504481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74546160366736710891002987 111819240550105066336504481)
  ·
    refine ⟨83864430412578799752378361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111819240550105066336504481 83864430412578799752378361)
    ·
      refine ⟨62898322809434099814283771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83864430412578799752378361 62898322809434099814283771)
      ·
        refine ⟨94347484214151149721425657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62898322809434099814283771 94347484214151149721425657)
        ·
          refine ⟨70760613160613362291069243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94347484214151149721425657 70760613160613362291069243)
          ·
            refine ⟨106140919740920043436603865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70760613160613362291069243 106140919740920043436603865)
            ·
              refine ⟨79605689805690032577452899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106140919740920043436603865 79605689805690032577452899)
              ·
                refine ⟨119408534708535048866179349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79605689805690032577452899 119408534708535048866179349)
                ·
                  refine ⟨5597275064462580415602157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119408534708535048866179349 5597275064462580415602157)
                  ·
                    refine ⟨2098978149173467655850809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5597275064462580415602157 2098978149173467655850809)
                    ·
                      refine ⟨1574233611880100741888107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2098978149173467655850809 1574233611880100741888107)
                      ·
                        rfl

theorem cell23_3065809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 3, 2].length) (baseStart_3065809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065809 prefixEnd_3065809 := by exact prefixLift 3065809
  have htrace : WordTrace (prefixWord ++ tailWord_3065809) baseStart_3065809 baseEnd_3065809 := by
    simpa [prefixWord, tailWord_3065809, baseEnd_3065809] using wordTrace_append hprefix tailTrace_3065809
  have hstable : (prefixWord ++ tailWord_3065809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065809).length < 2 ^ (prefixWord ++ tailWord_3065809).sum := by decide
  have hdescent : baseEnd_3065809 < baseStart_3065809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065832 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 3, 6]
def baseStart_3065832 : Nat := 118140960795 + 3065832 * 2 ^ 59
def prefixEnd_3065832 : Nat := 4983230072969 + 3 ^ 40 * 3065832 * 2
def baseEnd_3065832 : Nat := 524748473978384717300167

theorem tailTrace_3065832 : CollatzResearch.WordTrace tailWord_3065832 prefixEnd_3065832 524748473978384717300167 := by
  unfold tailWord_3065832
  simp only [CollatzResearch.WordTrace]
  refine ⟨55910039714510870632295875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74546719619347827509727833 55910039714510870632295875)
  ·
    refine ⟨83865059571766305948443813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55910039714510870632295875 83865059571766305948443813)
    ·
      refine ⟨15724698669706182365333215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83865059571766305948443813 15724698669706182365333215)
      ·
        refine ⟨23587048004559273547999823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15724698669706182365333215 23587048004559273547999823)
        ·
          refine ⟨35380572006838910321999735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23587048004559273547999823 35380572006838910321999735)
          ·
            refine ⟨53070858010258365482999603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35380572006838910321999735 53070858010258365482999603)
            ·
              refine ⟨79606287015387548224499405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53070858010258365482999603 79606287015387548224499405)
              ·
                refine ⟨29852357630770330584187277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79606287015387548224499405 29852357630770330584187277)
                ·
                  refine ⟨11194634111538873969070229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29852357630770330584187277 11194634111538873969070229)
                  ·
                    refine ⟨524748473978384717300167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11194634111538873969070229 524748473978384717300167)
                    ·
                      rfl

theorem cell23_3065832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_3065832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065832 prefixEnd_3065832 := by exact prefixLift 3065832
  have htrace : WordTrace (prefixWord ++ tailWord_3065832) baseStart_3065832 baseEnd_3065832 := by
    simpa [prefixWord, tailWord_3065832, baseEnd_3065832] using wordTrace_append hprefix tailTrace_3065832
  have hstable : (prefixWord ++ tailWord_3065832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065832).length < 2 ^ (prefixWord ++ tailWord_3065832).sum := by decide
  have hdescent : baseEnd_3065832 < baseStart_3065832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065839 : List Nat := [1, 1, 2, 1, 4, 2, 1, 5, 1, 1, 4]
def baseStart_3065839 : Nat := 118140960795 + 3065839 * 2 ^ 59
def prefixEnd_3065839 : Nat := 4983230072969 + 3 ^ 40 * 3065839 * 2
def baseEnd_3065839 : Nat := 1574249016299735624512969

theorem tailTrace_3065839 : CollatzResearch.WordTrace tailWord_3065839 prefixEnd_3065839 1574249016299735624512969 := by
  unfold tailWord_3065839
  simp only [CollatzResearch.WordTrace]
  refine ⟨111820334739996381460096571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74546889826664254306731047 111820334739996381460096571)
  ·
    refine ⟨167730502109994572190144857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111820334739996381460096571 167730502109994572190144857)
    ·
      refine ⟨125797876582495929142608643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167730502109994572190144857 125797876582495929142608643)
      ·
        refine ⟨188696814873743893713912965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125797876582495929142608643 188696814873743893713912965)
        ·
          refine ⟨35380652788826980071358681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188696814873743893713912965 35380652788826980071358681)
          ·
            refine ⟨26535489591620235053519011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35380652788826980071358681 26535489591620235053519011)
            ·
              refine ⟨39803234387430352580278517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26535489591620235053519011 39803234387430352580278517)
              ·
                refine ⟨3731553223821595554401111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39803234387430352580278517 3731553223821595554401111)
                ·
                  refine ⟨5597329835732393331601667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731553223821595554401111 5597329835732393331601667)
                  ·
                    refine ⟨8395994753598589997402501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5597329835732393331601667 8395994753598589997402501)
                    ·
                      refine ⟨1574249016299735624512969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8395994753598589997402501 1574249016299735624512969)
                      ·
                        rfl

theorem cell23_3065839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 1, 4].length) (baseStart_3065839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065839 prefixEnd_3065839 := by exact prefixLift 3065839
  have htrace : WordTrace (prefixWord ++ tailWord_3065839) baseStart_3065839 baseEnd_3065839 := by
    simpa [prefixWord, tailWord_3065839, baseEnd_3065839] using wordTrace_append hprefix tailTrace_3065839
  have hstable : (prefixWord ++ tailWord_3065839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065839).length < 2 ^ (prefixWord ++ tailWord_3065839).sum := by decide
  have hdescent : baseEnd_3065839 < baseStart_3065839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065849 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 4, 4]
def baseStart_3065849 : Nat := 118140960795 + 3065849 * 2 ^ 59
def prefixEnd_3065849 : Nat := 4983230072969 + 3 ^ 40 * 3065849 * 2
def baseEnd_3065849 : Nat := 524751383702093528462641

theorem tailTrace_3065849 : CollatzResearch.WordTrace tailWord_3065849 prefixEnd_3065849 524751383702093528462641 := by
  unfold tailWord_3065849
  simp only [CollatzResearch.WordTrace]
  refine ⟨111820699469960153167960601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74547132979973435445307067 111820699469960153167960601)
  ·
    refine ⟨83865524602470114875970451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111820699469960153167960601 83865524602470114875970451)
    ·
      refine ⟨125798286903705172313955677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83865524602470114875970451 125798286903705172313955677)
      ·
        refine ⟨47174357588889439617733379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125798286903705172313955677 47174357588889439617733379)
        ·
          refine ⟨70761536383334159426600069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47174357588889439617733379 70761536383334159426600069)
          ·
            refine ⟨13267788071875154892487513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70761536383334159426600069 13267788071875154892487513)
            ·
              refine ⟨9950841053906366169365635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13267788071875154892487513 9950841053906366169365635)
              ·
                refine ⟨14926261580859549254048453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9950841053906366169365635 14926261580859549254048453)
                ·
                  refine ⟨2798674046411165485134085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14926261580859549254048453 2798674046411165485134085)
                  ·
                    refine ⟨524751383702093528462641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2798674046411165485134085 524751383702093528462641)
                    ·
                      rfl

theorem cell23_3065849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 4].length) (baseStart_3065849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065849 prefixEnd_3065849 := by exact prefixLift 3065849
  have htrace : WordTrace (prefixWord ++ tailWord_3065849) baseStart_3065849 baseEnd_3065849 := by
    simpa [prefixWord, tailWord_3065849, baseEnd_3065849] using wordTrace_append hprefix tailTrace_3065849
  have hstable : (prefixWord ++ tailWord_3065849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065849).length < 2 ^ (prefixWord ++ tailWord_3065849).sum := by decide
  have hdescent : baseEnd_3065849 < baseStart_3065849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065852 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_3065852 : Nat := 118140960795 + 3065852 * 2 ^ 59
def prefixEnd_3065852 : Nat := 4983230072969 + 3 ^ 40 * 3065852 * 2
def baseEnd_3065852 : Nat := 1574255691548244073650409

theorem tailTrace_3065852 : CollatzResearch.WordTrace tailWord_3065852 prefixEnd_3065852 1574255691548244073650409 := by
  unfold tailWord_3065852
  simp only [CollatzResearch.WordTrace]
  refine ⟨55910404444474642340159905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74547205925966189786879873 55910404444474642340159905)
  ·
    refine ⟨41932803333355981755119929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55910404444474642340159905 41932803333355981755119929)
    ·
      refine ⟨31449602500016986316339947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41932803333355981755119929 31449602500016986316339947)
      ·
        refine ⟨47174403750025479474509921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31449602500016986316339947 47174403750025479474509921)
        ·
          refine ⟨35380802812519109605882441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47174403750025479474509921 35380802812519109605882441)
          ·
            refine ⟨26535602109389332204411831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35380802812519109605882441 26535602109389332204411831)
            ·
              refine ⟨39803403164083998306617747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26535602109389332204411831 39803403164083998306617747)
              ·
                refine ⟨59705104746125997459926621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39803403164083998306617747 59705104746125997459926621)
                ·
                  refine ⟨22389414279797249047472483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59705104746125997459926621 22389414279797249047472483)
                  ·
                    refine ⟨33584121419695873571208725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22389414279797249047472483 33584121419695873571208725)
                    ·
                      refine ⟨1574255691548244073650409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33584121419695873571208725 1574255691548244073650409)
                      ·
                        rfl

theorem cell23_3065852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_3065852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065852 prefixEnd_3065852 := by exact prefixLift 3065852
  have htrace : WordTrace (prefixWord ++ tailWord_3065852) baseStart_3065852 baseEnd_3065852 := by
    simpa [prefixWord, tailWord_3065852, baseEnd_3065852] using wordTrace_append hprefix tailTrace_3065852
  have hstable : (prefixWord ++ tailWord_3065852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065852).length < 2 ^ (prefixWord ++ tailWord_3065852).sum := by decide
  have hdescent : baseEnd_3065852 < baseStart_3065852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065856 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 3, 2, 2]
def baseStart_3065856 : Nat := 118140960795 + 3065856 * 2 ^ 59
def prefixEnd_3065856 : Nat := 4983230072969 + 3 ^ 40 * 3065856 * 2
def baseEnd_3065856 : Nat := 1574257745470862058000391

theorem tailTrace_3065856 : CollatzResearch.WordTrace tailWord_3065856 prefixEnd_3065856 1574257745470862058000391 := by
  unfold tailWord_3065856
  simp only [CollatzResearch.WordTrace]
  refine ⟨55910477390467396681732711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74547303187289862242310281 55910477390467396681732711)
  ·
    refine ⟨83865716085701095022599067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55910477390467396681732711 83865716085701095022599067)
    ·
      refine ⟨125798574128551642533898601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83865716085701095022599067 125798574128551642533898601)
      ·
        refine ⟨94348930596413731900423951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125798574128551642533898601 94348930596413731900423951)
        ·
          refine ⟨141523395894620597850635927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94348930596413731900423951 141523395894620597850635927)
          ·
            refine ⟨212285093841930896775953891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141523395894620597850635927 212285093841930896775953891)
            ·
              refine ⟨318427640762896345163930837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212285093841930896775953891 318427640762896345163930837)
              ·
                refine ⟨7463147830380383089779629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 318427640762896345163930837 7463147830380383089779629)
                ·
                  refine ⟨2798680436392643658667361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7463147830380383089779629 2798680436392643658667361)
                  ·
                    refine ⟨2099010327294482744000521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2798680436392643658667361 2099010327294482744000521)
                    ·
                      refine ⟨1574257745470862058000391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099010327294482744000521 1574257745470862058000391)
                      ·
                        rfl

theorem cell23_3065856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 3, 2, 2].length) (baseStart_3065856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065856 prefixEnd_3065856 := by exact prefixLift 3065856
  have htrace : WordTrace (prefixWord ++ tailWord_3065856) baseStart_3065856 baseEnd_3065856 := by
    simpa [prefixWord, tailWord_3065856, baseEnd_3065856] using wordTrace_append hprefix tailTrace_3065856
  have hstable : (prefixWord ++ tailWord_3065856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065856).length < 2 ^ (prefixWord ++ tailWord_3065856).sum := by decide
  have hdescent : baseEnd_3065856 < baseStart_3065856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065890 : List Nat := [3, 3, 1, 1, 1, 2, 2, 5, 1, 2, 2]
def baseStart_3065890 : Nat := 118140960795 + 3065890 * 2 ^ 59
def prefixEnd_3065890 : Nat := 4983230072969 + 3 ^ 40 * 3065890 * 2
def baseEnd_3065890 : Nat := 1574275203813114924975235

theorem tailTrace_3065890 : CollatzResearch.WordTrace tailWord_3065890 prefixEnd_3065890 1574275203813114924975235 := by
  unfold tailWord_3065890
  simp only [CollatzResearch.WordTrace]
  refine ⟨27955548715702904292550781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74548129908541078113468749 27955548715702904292550781)
  ·
    refine ⟨10483330768388589109706543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27955548715702904292550781 10483330768388589109706543)
    ·
      refine ⟨15724996152582883664559815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10483330768388589109706543 15724996152582883664559815)
      ·
        refine ⟨23587494228874325496839723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15724996152582883664559815 23587494228874325496839723)
        ·
          refine ⟨35381241343311488245259585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23587494228874325496839723 35381241343311488245259585)
          ·
            refine ⟨26535931007483616183944689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35381241343311488245259585 26535931007483616183944689)
            ·
              refine ⟨19901948255612712137958517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26535931007483616183944689 19901948255612712137958517)
              ·
                refine ⟨1865807648963691762933611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19901948255612712137958517 1865807648963691762933611)
                ·
                  refine ⟨2798711473445537644400417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865807648963691762933611 2798711473445537644400417)
                  ·
                    refine ⟨2099033605084153233300313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2798711473445537644400417 2099033605084153233300313)
                    ·
                      refine ⟨1574275203813114924975235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099033605084153233300313 1574275203813114924975235)
                      ·
                        rfl

theorem cell23_3065890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_3065890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065890 prefixEnd_3065890 := by exact prefixLift 3065890
  have htrace : WordTrace (prefixWord ++ tailWord_3065890) baseStart_3065890 baseEnd_3065890 := by
    simpa [prefixWord, tailWord_3065890, baseEnd_3065890] using wordTrace_append hprefix tailTrace_3065890
  have hstable : (prefixWord ++ tailWord_3065890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065890).length < 2 ^ (prefixWord ++ tailWord_3065890).sum := by decide
  have hdescent : baseEnd_3065890 < baseStart_3065890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065893 : List Nat := [1, 3, 1, 2, 2, 4, 3, 1, 1, 2, 3]
def baseStart_3065893 : Nat := 118140960795 + 3065893 * 2 ^ 59
def prefixEnd_3065893 : Nat := 4983230072969 + 3 ^ 40 * 3065893 * 2
def baseEnd_3065893 : Nat := 1574276744255078413237721

theorem tailTrace_3065893 : CollatzResearch.WordTrace tailWord_3065893 prefixEnd_3065893 1574276744255078413237721 := by
  unfold tailWord_3065893
  simp only [CollatzResearch.WordTrace]
  refine ⟨111822304281800748682562333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74548202854533832455041555 111822304281800748682562333)
  ·
    refine ⟨41933364105675280755960875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111822304281800748682562333 41933364105675280755960875)
    ·
      refine ⟨62900046158512921133941313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41933364105675280755960875 62900046158512921133941313)
      ·
        refine ⟨47175034618884690850455985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62900046158512921133941313 47175034618884690850455985)
        ·
          refine ⟨35381275964163518137841989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47175034618884690850455985 35381275964163518137841989)
          ·
            refine ⟨6633989243280659650845373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35381275964163518137841989 6633989243280659650845373)
            ·
              refine ⟨2487745966230247369067015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6633989243280659650845373 2487745966230247369067015)
              ·
                refine ⟨3731618949345371053600523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2487745966230247369067015 3731618949345371053600523)
                ·
                  refine ⟨5597428424018056580400785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731618949345371053600523 5597428424018056580400785)
                  ·
                    refine ⟨4198071318013542435300589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5597428424018056580400785 4198071318013542435300589)
                    ·
                      refine ⟨1574276744255078413237721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4198071318013542435300589 1574276744255078413237721)
                      ·
                        rfl

theorem cell23_3065893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_3065893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065893 prefixEnd_3065893 := by exact prefixLift 3065893
  have htrace : WordTrace (prefixWord ++ tailWord_3065893) baseStart_3065893 baseEnd_3065893 := by
    simpa [prefixWord, tailWord_3065893, baseEnd_3065893] using wordTrace_append hprefix tailTrace_3065893
  have hstable : (prefixWord ++ tailWord_3065893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065893).length < 2 ^ (prefixWord ++ tailWord_3065893).sum := by decide
  have hdescent : baseEnd_3065893 < baseStart_3065893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065896 : List Nat := [2, 1, 5, 3, 2, 10]
def baseStart_3065896 : Nat := 118140960795 + 3065896 * 2 ^ 59
def prefixEnd_3065896 : Nat := 4983230072969 + 3 ^ 40 * 3065896 * 2
def baseEnd_3065896 : Nat := 6478511459658608648149

theorem tailTrace_3065896 : CollatzResearch.WordTrace tailWord_3065896 prefixEnd_3065896 6478511459658608648149 := by
  unfold tailWord_3065896
  simp only [CollatzResearch.WordTrace]
  refine ⟨55911206850394940097460771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74548275800526586796614361 55911206850394940097460771)
  ·
    refine ⟨83866810275592410146191157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55911206850394940097460771 83866810275592410146191157)
    ·
      refine ⟨7862513463336788451205421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83866810275592410146191157 7862513463336788451205421)
      ·
        refine ⟨2948442548751295669202033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7862513463336788451205421 2948442548751295669202033)
        ·
          refine ⟨2211331911563471751901525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2948442548751295669202033 2211331911563471751901525)
          ·
            refine ⟨6478511459658608648149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2211331911563471751901525 6478511459658608648149)
            ·
              rfl

theorem cell23_3065896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 10].length) (baseStart_3065896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065896 prefixEnd_3065896 := by exact prefixLift 3065896
  have htrace : WordTrace (prefixWord ++ tailWord_3065896) baseStart_3065896 baseEnd_3065896 := by
    simpa [prefixWord, tailWord_3065896, baseEnd_3065896] using wordTrace_append hprefix tailTrace_3065896
  have hstable : (prefixWord ++ tailWord_3065896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065896).length < 2 ^ (prefixWord ++ tailWord_3065896).sum := by decide
  have hdescent : baseEnd_3065896 < baseStart_3065896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065916 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 5, 3, 2]
def baseStart_3065916 : Nat := 118140960795 + 3065916 * 2 ^ 59
def prefixEnd_3065916 : Nat := 4983230072969 + 3 ^ 40 * 3065916 * 2
def baseEnd_3065916 : Nat := 1574288554310131823250115

theorem tailTrace_3065916 : CollatzResearch.WordTrace tailWord_3065916 prefixEnd_3065916 1574288554310131823250115 := by
  unfold tailWord_3065916
  simp only [CollatzResearch.WordTrace]
  refine ⟨55911571580358711805324801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74548762107144949073766401 55911571580358711805324801)
  ·
    refine ⟨41933678685269033853993601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55911571580358711805324801 41933678685269033853993601)
    ·
      refine ⟨31450259013951775390495201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41933678685269033853993601 31450259013951775390495201)
      ·
        refine ⟨23587694260463831542871401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31450259013951775390495201 23587694260463831542871401)
        ·
          refine ⟨17690770695347873657153551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23587694260463831542871401 17690770695347873657153551)
          ·
            refine ⟨26536156043021810485730327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17690770695347873657153551 26536156043021810485730327)
            ·
              refine ⟨39804234064532715728595491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26536156043021810485730327 39804234064532715728595491)
              ·
                refine ⟨59706351096799073592893237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39804234064532715728595491 59706351096799073592893237)
                ·
                  refine ⟨5597470415324913149333741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59706351096799073592893237 5597470415324913149333741)
                  ·
                    refine ⟨2099051405746842431000153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5597470415324913149333741 2099051405746842431000153)
                    ·
                      refine ⟨1574288554310131823250115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099051405746842431000153 1574288554310131823250115)
                      ·
                        rfl

theorem cell23_3065916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_3065916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065916 prefixEnd_3065916 := by exact prefixLift 3065916
  have htrace : WordTrace (prefixWord ++ tailWord_3065916) baseStart_3065916 baseEnd_3065916 := by
    simpa [prefixWord, tailWord_3065916, baseEnd_3065916] using wordTrace_append hprefix tailTrace_3065916
  have hstable : (prefixWord ++ tailWord_3065916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065916).length < 2 ^ (prefixWord ++ tailWord_3065916).sum := by decide
  have hdescent : baseEnd_3065916 < baseStart_3065916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065926 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_3065926 : Nat := 118140960795 + 3065926 * 2 ^ 59
def prefixEnd_3065926 : Nat := 4983230072969 + 3 ^ 40 * 3065926 * 2
def baseEnd_3065926 : Nat := 524764563038892261375023

theorem tailTrace_3065926 : CollatzResearch.WordTrace tailWord_3065926 prefixEnd_3065926 524764563038892261375023 := by
  unfold tailWord_3065926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3494484621583787353703551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74549005260454130212342421 3494484621583787353703551)
  ·
    refine ⟨5241726932375681030555327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3494484621583787353703551 5241726932375681030555327)
    ·
      refine ⟨7862590398563521545832991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5241726932375681030555327 7862590398563521545832991)
      ·
        refine ⟨11793885597845282318749487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7862590398563521545832991 11793885597845282318749487)
        ·
          refine ⟨17690828396767923478124231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11793885597845282318749487 17690828396767923478124231)
          ·
            refine ⟨26536242595151885217186347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17690828396767923478124231 26536242595151885217186347)
            ·
              refine ⟨39804363892727827825779521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26536242595151885217186347 39804363892727827825779521)
              ·
                refine ⟨29853272919545870869334641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39804363892727827825779521 29853272919545870869334641)
                ·
                  refine ⟨22389954689659403152000981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29853272919545870869334641 22389954689659403152000981)
                  ·
                    refine ⟨524764563038892261375023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22389954689659403152000981 524764563038892261375023)
                    ·
                      rfl

theorem cell23_3065926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_3065926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065926 prefixEnd_3065926 := by exact prefixLift 3065926
  have htrace : WordTrace (prefixWord ++ tailWord_3065926) baseStart_3065926 baseEnd_3065926 := by
    simpa [prefixWord, tailWord_3065926, baseEnd_3065926] using wordTrace_append hprefix tailTrace_3065926
  have hstable : (prefixWord ++ tailWord_3065926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065926).length < 2 ^ (prefixWord ++ tailWord_3065926).sum := by decide
  have hdescent : baseEnd_3065926 < baseStart_3065926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065933 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_3065933 : Nat := 118140960795 + 3065933 * 2 ^ 59
def prefixEnd_3065933 : Nat := 4983230072969 + 3 ^ 40 * 3065933 * 2
def baseEnd_3065933 : Nat := 1574297283481258256737537

theorem tailTrace_3065933 : CollatzResearch.WordTrace tailWord_3065933 prefixEnd_3065933 1574297283481258256737537 := by
  unfold tailWord_3065933
  simp only [CollatzResearch.WordTrace]
  refine ⟨111823763201655835514018453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74549175467770557009345635 111823763201655835514018453)
  ·
    refine ⟨5241738900077617289719615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111823763201655835514018453 5241738900077617289719615)
    ·
      refine ⟨7862608350116425934579423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5241738900077617289719615 7862608350116425934579423)
      ·
        refine ⟨11793912525174638901869135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7862608350116425934579423 11793912525174638901869135)
        ·
          refine ⟨17690868787761958352803703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11793912525174638901869135 17690868787761958352803703)
          ·
            refine ⟨26536303181642937529205555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17690868787761958352803703 26536303181642937529205555)
            ·
              refine ⟨39804454772464406293808333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26536303181642937529205555 39804454772464406293808333)
              ·
                refine ⟨14926670539674152360178125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39804454772464406293808333 14926670539674152360178125)
                ·
                  refine ⟨5597501452377807135066797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14926670539674152360178125 5597501452377807135066797)
                  ·
                    refine ⟨2099063044641677675650049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5597501452377807135066797 2099063044641677675650049)
                    ·
                      refine ⟨1574297283481258256737537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099063044641677675650049 1574297283481258256737537)
                      ·
                        rfl

theorem cell23_3065933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_3065933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065933 prefixEnd_3065933 := by exact prefixLift 3065933
  have htrace : WordTrace (prefixWord ++ tailWord_3065933) baseStart_3065933 baseEnd_3065933 := by
    simpa [prefixWord, tailWord_3065933, baseEnd_3065933] using wordTrace_append hprefix tailTrace_3065933
  have hstable : (prefixWord ++ tailWord_3065933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065933).length < 2 ^ (prefixWord ++ tailWord_3065933).sum := by decide
  have hdescent : baseEnd_3065933 < baseStart_3065933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065946 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2]
def baseStart_3065946 : Nat := 118140960795 + 3065946 * 2 ^ 59
def prefixEnd_3065946 : Nat := 4983230072969 + 3 ^ 40 * 3065946 * 2
def baseEnd_3065946 : Nat := 1574303958729766705874977

theorem tailTrace_3065946 : CollatzResearch.WordTrace tailWord_3065946 prefixEnd_3065946 1574303958729766705874977 := by
  unfold tailWord_3065946
  simp only [CollatzResearch.WordTrace]
  refine ⟨27956059337652184683560423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74549491567072492489494461 27956059337652184683560423)
  ·
    refine ⟨41934089006478277025340635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27956059337652184683560423 41934089006478277025340635)
    ·
      refine ⟨62901133509717415538010953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41934089006478277025340635 62901133509717415538010953)
      ·
        refine ⟨47175850132288061653508215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62901133509717415538010953 47175850132288061653508215)
        ·
          refine ⟨70763775198432092480262323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47175850132288061653508215 70763775198432092480262323)
          ·
            refine ⟨106145662797648138720393485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70763775198432092480262323 106145662797648138720393485)
            ·
              refine ⟨39804623549118052020147557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106145662797648138720393485 39804623549118052020147557)
              ·
                refine ⟨7463366915459634753777667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39804623549118052020147557 7463366915459634753777667)
                ·
                  refine ⟨11195050373189452130666501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7463366915459634753777667 11195050373189452130666501)
                  ·
                    refine ⟨2099071944973022274499969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11195050373189452130666501 2099071944973022274499969)
                    ·
                      refine ⟨1574303958729766705874977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099071944973022274499969 1574303958729766705874977)
                      ·
                        rfl

theorem cell23_3065946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_3065946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065946 prefixEnd_3065946 := by exact prefixLift 3065946
  have htrace : WordTrace (prefixWord ++ tailWord_3065946) baseStart_3065946 baseEnd_3065946 := by
    simpa [prefixWord, tailWord_3065946, baseEnd_3065946] using wordTrace_append hprefix tailTrace_3065946
  have hstable : (prefixWord ++ tailWord_3065946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065946).length < 2 ^ (prefixWord ++ tailWord_3065946).sum := by decide
  have hdescent : baseEnd_3065946 < baseStart_3065946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065959 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_3065959 : Nat := 118140960795 + 3065959 * 2 ^ 59
def prefixEnd_3065959 : Nat := 4983230072969 + 3 ^ 40 * 3065959 * 2
def baseEnd_3065959 : Nat := 1574310633978275155012417

theorem tailTrace_3065959 : CollatzResearch.WordTrace tailWord_3065959 prefixEnd_3065959 1574310633978275155012417 := by
  unfold tailWord_3065959
  simp only [CollatzResearch.WordTrace]
  refine ⟨111824711499561641954464931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74549807666374427969643287 111824711499561641954464931)
  ·
    refine ⟨167737067249342462931697397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111824711499561641954464931 167737067249342462931697397)
    ·
      refine ⟨15725350054625855899846631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167737067249342462931697397 15725350054625855899846631)
      ·
        refine ⟨23588025081938783849769947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15725350054625855899846631 23588025081938783849769947)
        ·
          refine ⟨35382037622908175774654921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23588025081938783849769947 35382037622908175774654921)
          ·
            refine ⟨26536528217181131830991191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35382037622908175774654921 26536528217181131830991191)
            ·
              refine ⟨39804792325771697746486787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26536528217181131830991191 39804792325771697746486787)
              ·
                refine ⟨59707188488657546619730181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39804792325771697746486787 59707188488657546619730181)
                ·
                  refine ⟨11195097841623289991199409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59707188488657546619730181 11195097841623289991199409)
                  ·
                    refine ⟨8396323381217467493399557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11195097841623289991199409 8396323381217467493399557)
                    ·
                      refine ⟨1574310633978275155012417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8396323381217467493399557 1574310633978275155012417)
                      ·
                        rfl

theorem cell23_3065959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_3065959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065959 prefixEnd_3065959 := by exact prefixLift 3065959
  have htrace : WordTrace (prefixWord ++ tailWord_3065959) baseStart_3065959 baseEnd_3065959 := by
    simpa [prefixWord, tailWord_3065959, baseEnd_3065959] using wordTrace_append hprefix tailTrace_3065959
  have hstable : (prefixWord ++ tailWord_3065959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065959).length < 2 ^ (prefixWord ++ tailWord_3065959).sum := by decide
  have hdescent : baseEnd_3065959 < baseStart_3065959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3065969 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 7]
def baseStart_3065969 : Nat := 118140960795 + 3065969 * 2 ^ 59
def prefixEnd_3065969 : Nat := 4983230072969 + 3 ^ 40 * 3065969 * 2
def baseEnd_3065969 : Nat := 174923974309424457320819

theorem tailTrace_3065969 : CollatzResearch.WordTrace tailWord_3065969 prefixEnd_3065969 174923974309424457320819 := by
  unfold tailWord_3065969
  simp only [CollatzResearch.WordTrace]
  refine ⟨111825076229525413662328961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74550050819683609108219307 111825076229525413662328961)
  ·
    refine ⟨83868807172144060246746721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111825076229525413662328961 83868807172144060246746721)
    ·
      refine ⟨62901605379108045185060041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83868807172144060246746721 62901605379108045185060041)
      ·
        refine ⟨47176204034331033888795031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62901605379108045185060041 47176204034331033888795031)
        ·
          refine ⟨70764306051496550833192547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47176204034331033888795031 70764306051496550833192547)
          ·
            refine ⟨106146459077244826249788821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70764306051496550833192547 106146459077244826249788821)
            ·
              refine ⟨4975615269245851230458851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106146459077244826249788821 4975615269245851230458851)
              ·
                refine ⟨7463422903868776845688277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4975615269245851230458851 7463422903868776845688277)
                ·
                  refine ⟨174923974309424457320819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7463422903868776845688277 174923974309424457320819)
                  ·
                    rfl

theorem cell23_3065969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 7].length) (baseStart_3065969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3065969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3065969 prefixEnd_3065969 := by exact prefixLift 3065969
  have htrace : WordTrace (prefixWord ++ tailWord_3065969) baseStart_3065969 baseEnd_3065969 := by
    simpa [prefixWord, tailWord_3065969, baseEnd_3065969] using wordTrace_append hprefix tailTrace_3065969
  have hstable : (prefixWord ++ tailWord_3065969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3065969).length < 2 ^ (prefixWord ++ tailWord_3065969).sum := by decide
  have hdescent : baseEnd_3065969 < baseStart_3065969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3065969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066016 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 2, 5]
def baseStart_3066016 : Nat := 118140960795 + 3066016 * 2 ^ 59
def prefixEnd_3066016 : Nat := 4983230072969 + 3 ^ 40 * 3066016 * 2
def baseEnd_3066016 : Nat := 524779967458527143999885

theorem tailTrace_3066016 : CollatzResearch.WordTrace tailWord_3066016 prefixEnd_3066016 524779967458527143999885 := by
  unfold tailWord_3066016
  simp only [CollatzResearch.WordTrace]
  refine ⟨55913395230177570344644951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74551193640236760459526601 55913395230177570344644951)
  ·
    refine ⟨83870092845266355516967427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55913395230177570344644951 83870092845266355516967427)
    ·
      refine ⟨125805139267899533275451141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83870092845266355516967427 125805139267899533275451141)
      ·
        refine ⟨23588463612731162489147089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125805139267899533275451141 23588463612731162489147089)
        ·
          refine ⟨17691347709548371866860317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23588463612731162489147089 17691347709548371866860317)
          ·
            refine ⟨6634255391080639450072619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17691347709548371866860317 6634255391080639450072619)
            ·
              refine ⟨9951383086620959175108929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6634255391080639450072619 9951383086620959175108929)
              ·
                refine ⟨7463537314965719381331697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9951383086620959175108929 7463537314965719381331697)
                ·
                  refine ⟨5597652986224289535998773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7463537314965719381331697 5597652986224289535998773)
                  ·
                    refine ⟨524779967458527143999885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5597652986224289535998773 524779967458527143999885)
                    ·
                      rfl

theorem cell23_3066016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 2, 5].length) (baseStart_3066016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066016 prefixEnd_3066016 := by exact prefixLift 3066016
  have htrace : WordTrace (prefixWord ++ tailWord_3066016) baseStart_3066016 baseEnd_3066016 := by
    simpa [prefixWord, tailWord_3066016, baseEnd_3066016] using wordTrace_append hprefix tailTrace_3066016
  have hstable : (prefixWord ++ tailWord_3066016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066016).length < 2 ^ (prefixWord ++ tailWord_3066016).sum := by decide
  have hdescent : baseEnd_3066016 < baseStart_3066016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066020 : List Nat := [2, 3, 1, 2, 4, 1, 3, 2, 5]
def baseStart_3066020 : Nat := 118140960795 + 3066020 * 2 ^ 59
def prefixEnd_3066020 : Nat := 4983230072969 + 3 ^ 40 * 3066020 * 2
def baseEnd_3066020 : Nat := 174926884033133268483293

theorem tailTrace_3066020 : CollatzResearch.WordTrace tailWord_3066020 prefixEnd_3066020 174926884033133268483293 := by
  unfold tailWord_3066020
  simp only [CollatzResearch.WordTrace]
  refine ⟨55913468176170324686217757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74551290901560432914957009 55913468176170324686217757)
  ·
    refine ⟨20967550566063871757331659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55913468176170324686217757 20967550566063871757331659)
    ·
      refine ⟨31451325849095807635997489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20967550566063871757331659 31451325849095807635997489)
      ·
        refine ⟨23588494386821855726998117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31451325849095807635997489 23588494386821855726998117)
        ·
          refine ⟨4422842697529097948812147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23588494386821855726998117 4422842697529097948812147)
          ·
            refine ⟨6634264046293646923218221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4422842697529097948812147 6634264046293646923218221)
            ·
              refine ⟨2487849017360117596206833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6634264046293646923218221 2487849017360117596206833)
              ·
                refine ⟨1865886763020088197155125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2487849017360117596206833 1865886763020088197155125)
                ·
                  refine ⟨174926884033133268483293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1865886763020088197155125 174926884033133268483293)
                  ·
                    rfl

theorem cell23_3066020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_3066020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066020 prefixEnd_3066020 := by exact prefixLift 3066020
  have htrace : WordTrace (prefixWord ++ tailWord_3066020) baseStart_3066020 baseEnd_3066020 := by
    simpa [prefixWord, tailWord_3066020, baseEnd_3066020] using wordTrace_append hprefix tailTrace_3066020
  have hstable : (prefixWord ++ tailWord_3066020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066020).length < 2 ^ (prefixWord ++ tailWord_3066020).sum := by decide
  have hdescent : baseEnd_3066020 < baseStart_3066020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066050 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3066050 : Nat := 118140960795 + 3066050 * 2 ^ 59
def prefixEnd_3066050 : Nat := 4983230072969 + 3 ^ 40 * 3066050 * 2
def baseEnd_3066050 : Nat := 524785786905944766324833

theorem tailTrace_3066050 : CollatzResearch.WordTrace tailWord_3066050 prefixEnd_3066050 524785786905944766324833 := by
  unfold tailWord_3066050
  simp only [CollatzResearch.WordTrace]
  refine ⟨27957007635557991124006901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74552020361487976330685069 27957007635557991124006901)
  ·
    refine ⟨2620969465833561667875647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27957007635557991124006901 2620969465833561667875647)
    ·
      refine ⟨3931454198750342501813471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2620969465833561667875647 3931454198750342501813471)
      ·
        refine ⟨5897181298125513752720207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3931454198750342501813471 5897181298125513752720207)
        ·
          refine ⟨8845771947188270629080311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5897181298125513752720207 8845771947188270629080311)
          ·
            refine ⟨13268657920782405943620467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8845771947188270629080311 13268657920782405943620467)
            ·
              refine ⟨19902986881173608915430701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13268657920782405943620467 19902986881173608915430701)
              ·
                refine ⟨7463620080440103343286513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19902986881173608915430701 7463620080440103343286513)
                ·
                  refine ⟨5597715060330077507464885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7463620080440103343286513 5597715060330077507464885)
                  ·
                    refine ⟨524785786905944766324833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5597715060330077507464885 524785786905944766324833)
                    ·
                      rfl

theorem cell23_3066050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3066050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066050 prefixEnd_3066050 := by exact prefixLift 3066050
  have htrace : WordTrace (prefixWord ++ tailWord_3066050) baseStart_3066050 baseEnd_3066050 := by
    simpa [prefixWord, tailWord_3066050, baseEnd_3066050] using wordTrace_append hprefix tailTrace_3066050
  have hstable : (prefixWord ++ tailWord_3066050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066050).length < 2 ^ (prefixWord ++ tailWord_3066050).sum := by decide
  have hdescent : baseEnd_3066050 < baseStart_3066050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066063 : List Nat := [1, 1, 2, 1, 1, 3, 4, 5, 1, 4]
def baseStart_3066063 : Nat := 118140960795 + 3066063 * 2 ^ 59
def prefixEnd_3066063 : Nat := 4983230072969 + 3 ^ 40 * 3066063 * 2
def baseEnd_3066063 : Nat := 524788011988780916037313

theorem tailTrace_3066063 : CollatzResearch.WordTrace tailWord_3066063 prefixEnd_3066063 524788011988780916037313 := by
  unfold tailWord_3066063
  simp only [CollatzResearch.WordTrace]
  refine ⟨111828504691184867716250843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74552336460789911810833895 111828504691184867716250843)
  ·
    refine ⟨167742757036777301574376265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111828504691184867716250843 167742757036777301574376265)
    ·
      refine ⟨125807067777582976180782199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167742757036777301574376265 125807067777582976180782199)
      ·
        refine ⟨188710601666374464271173299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125807067777582976180782199 188710601666374464271173299)
        ·
          refine ⟨283065902499561696406759949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188710601666374464271173299 283065902499561696406759949)
          ·
            refine ⟨106149713437335636152534981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283065902499561696406759949 106149713437335636152534981)
            ·
              refine ⟨19903071269500431778600309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106149713437335636152534981 19903071269500431778600309)
              ·
                refine ⟨1865912931515665479243779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19903071269500431778600309 1865912931515665479243779)
                ·
                  refine ⟨2798869397273498218865669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865912931515665479243779 2798869397273498218865669)
                  ·
                    refine ⟨524788011988780916037313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2798869397273498218865669 524788011988780916037313)
                    ·
                      rfl

theorem cell23_3066063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 1, 4].length) (baseStart_3066063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066063 prefixEnd_3066063 := by exact prefixLift 3066063
  have htrace : WordTrace (prefixWord ++ tailWord_3066063) baseStart_3066063 baseEnd_3066063 := by
    simpa [prefixWord, tailWord_3066063, baseEnd_3066063] using wordTrace_append hprefix tailTrace_3066063
  have hstable : (prefixWord ++ tailWord_3066063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066063).length < 2 ^ (prefixWord ++ tailWord_3066063).sum := by decide
  have hdescent : baseEnd_3066063 < baseStart_3066063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066070 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3066070 : Nat := 118140960795 + 3066070 * 2 ^ 59
def prefixEnd_3066070 : Nat := 4983230072969 + 3 ^ 40 * 3066070 * 2
def baseEnd_3066070 : Nat := 1574367630330924220724407

theorem tailTrace_3066070 : CollatzResearch.WordTrace tailWord_3066070 prefixEnd_3066070 1574367630330924220724407 := by
  unfold tailWord_3066070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6989297500134969244484729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74552506668106338607837109 6989297500134969244484729)
  ·
    refine ⟨5241973125101226933363547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6989297500134969244484729 5241973125101226933363547)
    ·
      refine ⟨7862959687651840400045321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5241973125101226933363547 7862959687651840400045321)
      ·
        refine ⟨5897219765738880300033991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7862959687651840400045321 5897219765738880300033991)
        ·
          refine ⟨8845829648608320450050987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5897219765738880300033991 8845829648608320450050987)
          ·
            refine ⟨13268744472912480675076481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8845829648608320450050987 13268744472912480675076481)
            ·
              refine ⟨9951558354684360506307361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13268744472912480675076481 9951558354684360506307361)
              ·
                refine ⟨7463668766013270379730521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9951558354684360506307361 7463668766013270379730521)
                ·
                  refine ⟨5597751574509952784797891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7463668766013270379730521 5597751574509952784797891)
                  ·
                    refine ⟨8396627361764929177196837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5597751574509952784797891 8396627361764929177196837)
                    ·
                      refine ⟨1574367630330924220724407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8396627361764929177196837 1574367630330924220724407)
                      ·
                        rfl

theorem cell23_3066070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3066070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066070 prefixEnd_3066070 := by exact prefixLift 3066070
  have htrace : WordTrace (prefixWord ++ tailWord_3066070) baseStart_3066070 baseEnd_3066070 := by
    simpa [prefixWord, tailWord_3066070, baseEnd_3066070] using wordTrace_append hprefix tailTrace_3066070
  have hstable : (prefixWord ++ tailWord_3066070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066070).length < 2 ^ (prefixWord ++ tailWord_3066070).sum := by decide
  have hdescent : baseEnd_3066070 < baseStart_3066070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066079 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 6]
def baseStart_3066079 : Nat := 118140960795 + 3066079 * 2 ^ 59
def prefixEnd_3066079 : Nat := 4983230072969 + 3 ^ 40 * 3066079 * 2
def baseEnd_3066079 : Nat := 1574372251656814685511865

theorem tailTrace_3066079 : CollatzResearch.WordTrace tailWord_3066079 prefixEnd_3066079 1574372251656814685511865 := by
  unfold tailWord_3066079
  simp only [CollatzResearch.WordTrace]
  refine ⟨111829088259126902448833291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74552725506084601632555527 111829088259126902448833291)
  ·
    refine ⟨167743632388690353673249937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111829088259126902448833291 167743632388690353673249937)
    ·
      refine ⟨125807724291517765254937453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167743632388690353673249937 125807724291517765254937453)
      ·
        refine ⟨47177896609319161970601545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125807724291517765254937453 47177896609319161970601545)
        ·
          refine ⟨35383422456989371477951159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47177896609319161970601545 35383422456989371477951159)
          ·
            refine ⟨53075133685484057216926739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35383422456989371477951159 53075133685484057216926739)
            ·
              refine ⟨79612700528226085825390109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53075133685484057216926739 79612700528226085825390109)
              ·
                refine ⟨29854762698084782184521291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79612700528226085825390109 29854762698084782184521291)
                ·
                  refine ⟨44782144047127173276781937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29854762698084782184521291 44782144047127173276781937)
                  ·
                    refine ⟨33586608035345379957586453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44782144047127173276781937 33586608035345379957586453)
                    ·
                      refine ⟨1574372251656814685511865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33586608035345379957586453 1574372251656814685511865)
                      ·
                        rfl

theorem cell23_3066079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_3066079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066079 prefixEnd_3066079 := by exact prefixLift 3066079
  have htrace : WordTrace (prefixWord ++ tailWord_3066079) baseStart_3066079 baseEnd_3066079 := by
    simpa [prefixWord, tailWord_3066079, baseEnd_3066079] using wordTrace_append hprefix tailTrace_3066079
  have hstable : (prefixWord ++ tailWord_3066079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066079).length < 2 ^ (prefixWord ++ tailWord_3066079).sum := by decide
  have hdescent : baseEnd_3066079 < baseStart_3066079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066099 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 7]
def baseStart_3066099 : Nat := 118140960795 + 3066099 * 2 ^ 59
def prefixEnd_3066099 : Nat := 4983230072969 + 3 ^ 40 * 3066099 * 2
def baseEnd_3066099 : Nat := 1574382521269904607261773

theorem tailTrace_3066099 : CollatzResearch.WordTrace tailWord_3066099 prefixEnd_3066099 1574382521269904607261773 := by
  unfold tailWord_3066099
  simp only [CollatzResearch.WordTrace]
  refine ⟨111829817719054445864561351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74553211812702963909707567 111829817719054445864561351)
  ·
    refine ⟨167744726578581668796842027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111829817719054445864561351 167744726578581668796842027)
    ·
      refine ⟨251617089867872503195263041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167744726578581668796842027 251617089867872503195263041)
      ·
        refine ⟨188712817400904377396447281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251617089867872503195263041 188712817400904377396447281)
        ·
          refine ⟨141534613050678283047335461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188712817400904377396447281 141534613050678283047335461)
          ·
            refine ⟨26537739947002178071375399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141534613050678283047335461 26537739947002178071375399)
            ·
              refine ⟨39806609920503267107063099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26537739947002178071375399 39806609920503267107063099)
              ·
                refine ⟨59709914880754900660594649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39806609920503267107063099 59709914880754900660594649)
                ·
                  refine ⟨44782436160566175495445987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59709914880754900660594649 44782436160566175495445987)
                  ·
                    refine ⟨67173654240849263243168981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44782436160566175495445987 67173654240849263243168981)
                    ·
                      refine ⟨1574382521269904607261773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67173654240849263243168981 1574382521269904607261773)
                      ·
                        rfl

theorem cell23_3066099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_3066099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066099 prefixEnd_3066099 := by exact prefixLift 3066099
  have htrace : WordTrace (prefixWord ++ tailWord_3066099) baseStart_3066099 baseEnd_3066099 := by
    simpa [prefixWord, tailWord_3066099, baseEnd_3066099] using wordTrace_append hprefix tailTrace_3066099
  have hstable : (prefixWord ++ tailWord_3066099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066099).length < 2 ^ (prefixWord ++ tailWord_3066099).sum := by decide
  have hdescent : baseEnd_3066099 < baseStart_3066099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066106 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 3, 5]
def baseStart_3066106 : Nat := 118140960795 + 3066106 * 2 ^ 59
def prefixEnd_3066106 : Nat := 4983230072969 + 3 ^ 40 * 3066106 * 2
def baseEnd_3066106 : Nat := 524795371878162026624747

theorem tailTrace_3066106 : CollatzResearch.WordTrace tailWord_3066106 prefixEnd_3066106 524795371878162026624747 := by
  unfold tailWord_3066106
  simp only [CollatzResearch.WordTrace]
  refine ⟨27957518257507271515016543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74553382020019390706710781 27957518257507271515016543)
  ·
    refine ⟨41936277386260907272524815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27957518257507271515016543 41936277386260907272524815)
    ·
      refine ⟨62904416079391360908787223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41936277386260907272524815 62904416079391360908787223)
      ·
        refine ⟨94356624119087041363180835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62904416079391360908787223 94356624119087041363180835)
        ·
          refine ⟨141534936178630562044771253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94356624119087041363180835 141534936178630562044771253)
          ·
            refine ⟨13268900266746615191697305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141534936178630562044771253 13268900266746615191697305)
            ·
              refine ⟨9951675200059961393772979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13268900266746615191697305 9951675200059961393772979)
              ·
                refine ⟨14927512800089942090659469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9951675200059961393772979 14927512800089942090659469)
                ·
                  refine ⟨5597817300033728283997301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14927512800089942090659469 5597817300033728283997301)
                  ·
                    refine ⟨524795371878162026624747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5597817300033728283997301 524795371878162026624747)
                    ·
                      rfl

theorem cell23_3066106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_3066106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066106 prefixEnd_3066106 := by exact prefixLift 3066106
  have htrace : WordTrace (prefixWord ++ tailWord_3066106) baseStart_3066106 baseEnd_3066106 := by
    simpa [prefixWord, tailWord_3066106, baseEnd_3066106] using wordTrace_append hprefix tailTrace_3066106
  have hstable : (prefixWord ++ tailWord_3066106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066106).length < 2 ^ (prefixWord ++ tailWord_3066106).sum := by decide
  have hdescent : baseEnd_3066106 < baseStart_3066106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066113 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_3066113 : Nat := 118140960795 + 3066113 * 2 ^ 59
def prefixEnd_3066113 : Nat := 4983230072969 + 3 ^ 40 * 3066113 * 2
def baseEnd_3066113 : Nat := 1574389709999067552486709

theorem tailTrace_3066113 : CollatzResearch.WordTrace tailWord_3066113 prefixEnd_3066113 1574389709999067552486709 := by
  unfold tailWord_3066113
  simp only [CollatzResearch.WordTrace]
  refine ⟨111830328341003726255570993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74553552227335817503713995 111830328341003726255570993)
  ·
    refine ⟨83872746255752794691678245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111830328341003726255570993 83872746255752794691678245)
    ·
      refine ⟨15726139922953649004689671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83872746255752794691678245 15726139922953649004689671)
      ·
        refine ⟨23589209884430473507034507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15726139922953649004689671 23589209884430473507034507)
        ·
          refine ⟨35383814826645710260551761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23589209884430473507034507 35383814826645710260551761)
          ·
            refine ⟨26537861119984282695413821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35383814826645710260551761 26537861119984282695413821)
            ·
              refine ⟨9951697919994106010780183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26537861119984282695413821 9951697919994106010780183)
              ·
                refine ⟨14927546879991159016170275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9951697919994106010780183 14927546879991159016170275)
                ·
                  refine ⟨22391320319986738524255413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14927546879991159016170275 22391320319986738524255413)
                  ·
                    refine ⟨2099186279998756736648945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22391320319986738524255413 2099186279998756736648945)
                    ·
                      refine ⟨1574389709999067552486709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099186279998756736648945 1574389709999067552486709)
                      ·
                        rfl

theorem cell23_3066113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_3066113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066113 prefixEnd_3066113 := by exact prefixLift 3066113
  have htrace : WordTrace (prefixWord ++ tailWord_3066113) baseStart_3066113 baseEnd_3066113 := by
    simpa [prefixWord, tailWord_3066113, baseEnd_3066113] using wordTrace_append hprefix tailTrace_3066113
  have hstable : (prefixWord ++ tailWord_3066113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066113).length < 2 ^ (prefixWord ++ tailWord_3066113).sum := by decide
  have hdescent : baseEnd_3066113 < baseStart_3066113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066157 : List Nat := [1, 5, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3066157 : Nat := 118140960795 + 3066157 * 2 ^ 59
def prefixEnd_3066157 : Nat := 4983230072969 + 3 ^ 40 * 3066157 * 2
def baseEnd_3066157 : Nat := 524804101049288460112169

theorem tailTrace_3066157 : CollatzResearch.WordTrace tailWord_3066157 prefixEnd_3066157 524804101049288460112169 := by
  unfold tailWord_3066157
  simp only [CollatzResearch.WordTrace]
  refine ⟨111831933152844321770172725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74554622101896214513448483 111831933152844321770172725)
  ·
    refine ⟨10484243733079155165953693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111831933152844321770172725 10484243733079155165953693)
    ·
      refine ⟨3931591399904683187232635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10484243733079155165953693 3931591399904683187232635)
      ·
        refine ⟨5897387099857024780848953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3931591399904683187232635 5897387099857024780848953)
        ·
          refine ⟨4423040324892768585636715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5897387099857024780848953 4423040324892768585636715)
          ·
            refine ⟨6634560487339152878455073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423040324892768585636715 6634560487339152878455073)
            ·
              refine ⟨4975920365504364658841305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6634560487339152878455073 4975920365504364658841305)
              ·
                refine ⟨3731940274128273494130979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4975920365504364658841305 3731940274128273494130979)
                ·
                  refine ⟨5597910411192410241196469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731940274128273494130979 5597910411192410241196469)
                  ·
                    refine ⟨524804101049288460112169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5597910411192410241196469 524804101049288460112169)
                    ·
                      rfl

theorem cell23_3066157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3066157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066157 prefixEnd_3066157 := by exact prefixLift 3066157
  have htrace : WordTrace (prefixWord ++ tailWord_3066157) baseStart_3066157 baseEnd_3066157 := by
    simpa [prefixWord, tailWord_3066157, baseEnd_3066157] using wordTrace_append hprefix tailTrace_3066157
  have hstable : (prefixWord ++ tailWord_3066157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066157).length < 2 ^ (prefixWord ++ tailWord_3066157).sum := by decide
  have hdescent : baseEnd_3066157 < baseStart_3066157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066236 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_3066236 : Nat := 118140960795 + 3066236 * 2 ^ 59
def prefixEnd_3066236 : Nat := 4983230072969 + 3 ^ 40 * 3066236 * 2
def baseEnd_3066236 : Nat := 1574452868119570571248643

theorem tailTrace_3066236 : CollatzResearch.WordTrace tailWord_3066236 prefixEnd_3066236 1574452868119570571248643 := by
  unfold tailWord_3066236
  simp only [CollatzResearch.WordTrace]
  refine ⟨55917407259779059131149281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74556543013038745508199041 55917407259779059131149281)
  ·
    refine ⟨41938055444834294348361961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55917407259779059131149281 41938055444834294348361961)
    ·
      refine ⟨31453541583625720761271471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41938055444834294348361961 31453541583625720761271471)
      ·
        refine ⟨47180312375438581141907207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31453541583625720761271471 47180312375438581141907207)
        ·
          refine ⟨70770468563157871712860811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47180312375438581141907207 70770468563157871712860811)
          ·
            refine ⟨106155702844736807569291217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70770468563157871712860811 106155702844736807569291217)
            ·
              refine ⟨79616777133552605676968413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106155702844736807569291217 79616777133552605676968413)
              ·
                refine ⟨29856291425082227128863155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79616777133552605676968413 29856291425082227128863155)
                ·
                  refine ⟨44784437137623340693294733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29856291425082227128863155 44784437137623340693294733)
                  ·
                    refine ⟨16794163926608752759985525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44784437137623340693294733 16794163926608752759985525)
                    ·
                      refine ⟨1574452868119570571248643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16794163926608752759985525 1574452868119570571248643)
                      ·
                        rfl

theorem cell23_3066236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_3066236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066236 prefixEnd_3066236 := by exact prefixLift 3066236
  have htrace : WordTrace (prefixWord ++ tailWord_3066236) baseStart_3066236 baseEnd_3066236 := by
    simpa [prefixWord, tailWord_3066236, baseEnd_3066236] using wordTrace_append hprefix tailTrace_3066236
  have hstable : (prefixWord ++ tailWord_3066236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066236).length < 2 ^ (prefixWord ++ tailWord_3066236).sum := by decide
  have hdescent : baseEnd_3066236 < baseStart_3066236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066260 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_3066260 : Nat := 118140960795 + 3066260 * 2 ^ 59
def prefixEnd_3066260 : Nat := 4983230072969 + 3 ^ 40 * 3066260 * 2
def baseEnd_3066260 : Nat := 524821730551759492449511

theorem tailTrace_3066260 : CollatzResearch.WordTrace tailWord_3066260 prefixEnd_3066260 524821730551759492449511 := by
  unfold tailWord_3066260
  simp only [CollatzResearch.WordTrace]
  refine ⟨55917844935735585180586117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74557126580980780240781489 55917844935735585180586117)
  ·
    refine ⟨10484595925450422221359897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55917844935735585180586117 10484595925450422221359897)
    ·
      refine ⟨7863446944087816666019923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10484595925450422221359897 7863446944087816666019923)
      ·
        refine ⟨11795170416131724999029885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7863446944087816666019923 11795170416131724999029885)
        ·
          refine ⟨4423188906049396874636207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11795170416131724999029885 4423188906049396874636207)
          ·
            refine ⟨6634783359074095311954311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423188906049396874636207 6634783359074095311954311)
            ·
              refine ⟨9952175038611142967931467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6634783359074095311954311 9952175038611142967931467)
              ·
                refine ⟨14928262557916714451897201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9952175038611142967931467 14928262557916714451897201)
                ·
                  refine ⟨11196196918437535838922901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14928262557916714451897201 11196196918437535838922901)
                  ·
                    refine ⟨524821730551759492449511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11196196918437535838922901 524821730551759492449511)
                    ·
                      rfl

theorem cell23_3066260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_3066260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066260 prefixEnd_3066260 := by exact prefixLift 3066260
  have htrace : WordTrace (prefixWord ++ tailWord_3066260) baseStart_3066260 baseEnd_3066260 := by
    simpa [prefixWord, tailWord_3066260, baseEnd_3066260] using wordTrace_append hprefix tailTrace_3066260
  have hstable : (prefixWord ++ tailWord_3066260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066260).length < 2 ^ (prefixWord ++ tailWord_3066260).sum := by decide
  have hdescent : baseEnd_3066260 < baseStart_3066260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066290 : List Nat := [3, 2, 1, 1, 1, 1, 6, 3, 5]
def baseStart_3066290 : Nat := 118140960795 + 3066290 * 2 ^ 59
def prefixEnd_3066290 : Nat := 4983230072969 + 3 ^ 40 * 3066290 * 2
def baseEnd_3066290 : Nat := 174942288452768151108155

theorem tailTrace_3066290 : CollatzResearch.WordTrace tailWord_3066290 prefixEnd_3066290 174942288452768151108155 := by
  unfold tailWord_3066290
  simp only [CollatzResearch.WordTrace]
  refine ⟨27959196015340621371191081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74557856040908323656509549 27959196015340621371191081)
  ·
    refine ⟨20969397011505466028393311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27959196015340621371191081 20969397011505466028393311)
    ·
      refine ⟨31454095517258199042589967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20969397011505466028393311 31454095517258199042589967)
      ·
        refine ⟨47181143275887298563884951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31454095517258199042589967 47181143275887298563884951)
        ·
          refine ⟨70771714913830947845827427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47181143275887298563884951 70771714913830947845827427)
          ·
            refine ⟨106157572370746421768741141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70771714913830947845827427 106157572370746421768741141)
            ·
              refine ⟨4976136204878738520409741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106157572370746421768741141 4976136204878738520409741)
              ·
                refine ⟨1866051076829526945153653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4976136204878738520409741 1866051076829526945153653)
                ·
                  refine ⟨174942288452768151108155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1866051076829526945153653 174942288452768151108155)
                  ·
                    rfl

theorem cell23_3066290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_3066290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066290 prefixEnd_3066290 := by exact prefixLift 3066290
  have htrace : WordTrace (prefixWord ++ tailWord_3066290) baseStart_3066290 baseEnd_3066290 := by
    simpa [prefixWord, tailWord_3066290, baseEnd_3066290] using wordTrace_append hprefix tailTrace_3066290
  have hstable : (prefixWord ++ tailWord_3066290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066290).length < 2 ^ (prefixWord ++ tailWord_3066290).sum := by decide
  have hdescent : baseEnd_3066290 < baseStart_3066290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066300 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_3066300 : Nat := 118140960795 + 3066300 * 2 ^ 59
def prefixEnd_3066300 : Nat := 4983230072969 + 3 ^ 40 * 3066300 * 2
def baseEnd_3066300 : Nat := 1574485730881458320848349

theorem tailTrace_3066300 : CollatzResearch.WordTrace tailWord_3066300 prefixEnd_3066300 1574485730881458320848349 := by
  unfold tailWord_3066300
  simp only [CollatzResearch.WordTrace]
  refine ⟨55918574395663128596314177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74558099194217504795085569 55918574395663128596314177)
  ·
    refine ⟨41938930796747346447235633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55918574395663128596314177 41938930796747346447235633)
    ·
      refine ⟨31454198097560509835426725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41938930796747346447235633 31454198097560509835426725)
      ·
        refine ⟨5897662143292595594142511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31454198097560509835426725 5897662143292595594142511)
        ·
          refine ⟨8846493214938893391213767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5897662143292595594142511 8846493214938893391213767)
          ·
            refine ⟨13269739822408340086820651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8846493214938893391213767 13269739822408340086820651)
            ·
              refine ⟨19904609733612510130230977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13269739822408340086820651 19904609733612510130230977)
              ·
                refine ⟨14928457300209382597673233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19904609733612510130230977 14928457300209382597673233)
                ·
                  refine ⟨11196342975157036948254925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14928457300209382597673233 11196342975157036948254925)
                  ·
                    refine ⟨4198628615683888855595597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11196342975157036948254925 4198628615683888855595597)
                    ·
                      refine ⟨1574485730881458320848349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4198628615683888855595597 1574485730881458320848349)
                      ·
                        rfl

theorem cell23_3066300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_3066300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066300 prefixEnd_3066300 := by exact prefixLift 3066300
  have htrace : WordTrace (prefixWord ++ tailWord_3066300) baseStart_3066300 baseEnd_3066300 := by
    simpa [prefixWord, tailWord_3066300, baseEnd_3066300] using wordTrace_append hprefix tailTrace_3066300
  have hstable : (prefixWord ++ tailWord_3066300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066300).length < 2 ^ (prefixWord ++ tailWord_3066300).sum := by decide
  have hdescent : baseEnd_3066300 < baseStart_3066300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066333 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_3066333 : Nat := 118140960795 + 3066333 * 2 ^ 59
def prefixEnd_3066333 : Nat := 4983230072969 + 3 ^ 40 * 3066333 * 2
def baseEnd_3066333 : Nat := 524834225247685563911899

theorem tailTrace_3066333 : CollatzResearch.WordTrace tailWord_3066333 prefixEnd_3066333 524834225247685563911899 := by
  unfold tailWord_3066333
  simp only [CollatzResearch.WordTrace]
  refine ⟨111838352400206703828579653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74558901600137802552386435 111838352400206703828579653)
  ·
    refine ⟨20969691075038756967858685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111838352400206703828579653 20969691075038756967858685)
    ·
      refine ⟨7863634153139533862947007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20969691075038756967858685 7863634153139533862947007)
      ·
        refine ⟨11795451229709300794420511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7863634153139533862947007 11795451229709300794420511)
        ·
          refine ⟨17693176844563951191630767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11795451229709300794420511 17693176844563951191630767)
          ·
            refine ⟨26539765266845926787446151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17693176844563951191630767 26539765266845926787446151)
            ·
              refine ⟨39809647900268890181169227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26539765266845926787446151 39809647900268890181169227)
              ·
                refine ⟨59714471850403335271753841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39809647900268890181169227 59714471850403335271753841)
                ·
                  refine ⟨44785853887802501453815381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59714471850403335271753841 44785853887802501453815381)
                  ·
                    refine ⟨524834225247685563911899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44785853887802501453815381 524834225247685563911899)
                    ·
                      rfl

theorem cell23_3066333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_3066333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066333 prefixEnd_3066333 := by exact prefixLift 3066333
  have htrace : WordTrace (prefixWord ++ tailWord_3066333) baseStart_3066333 baseEnd_3066333 := by
    simpa [prefixWord, tailWord_3066333, baseEnd_3066333] using wordTrace_append hprefix tailTrace_3066333
  have hstable : (prefixWord ++ tailWord_3066333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066333).length < 2 ^ (prefixWord ++ tailWord_3066333).sum := by decide
  have hdescent : baseEnd_3066333 < baseStart_3066333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066360 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 2, 2, 3]
def baseStart_3066360 : Nat := 118140960795 + 3066360 * 2 ^ 59
def prefixEnd_3066360 : Nat := 4983230072969 + 3 ^ 40 * 3066360 * 2
def baseEnd_3066360 : Nat := 1574516539720728086098073

theorem tailTrace_3066360 : CollatzResearch.WordTrace tailWord_3066360 prefixEnd_3066360 1574516539720728086098073 := by
  unfold tailWord_3066360
  simp only [CollatzResearch.WordTrace]
  refine ⟨55919668585554443719906267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74559558114072591626541689 55919668585554443719906267)
  ·
    refine ⟨83879502878331665579859401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55919668585554443719906267 83879502878331665579859401)
    ·
      refine ⟨62909627158748749184894551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83879502878331665579859401 62909627158748749184894551)
      ·
        refine ⟨94364440738123123777341827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62909627158748749184894551 94364440738123123777341827)
        ·
          refine ⟨141546661107184685666012741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94364440738123123777341827 141546661107184685666012741)
          ·
            refine ⟨26539998957597128562377389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141546661107184685666012741 26539998957597128562377389)
            ·
              refine ⟨9952499609098923210891521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26539998957597128562377389 9952499609098923210891521)
              ·
                refine ⟨7464374706824192408168641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9952499609098923210891521 7464374706824192408168641)
                ·
                  refine ⟨5598281030118144306126481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7464374706824192408168641 5598281030118144306126481)
                  ·
                    refine ⟨4198710772588608229594861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5598281030118144306126481 4198710772588608229594861)
                    ·
                      refine ⟨1574516539720728086098073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4198710772588608229594861 1574516539720728086098073)
                      ·
                        rfl

theorem cell23_3066360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_3066360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066360 prefixEnd_3066360 := by exact prefixLift 3066360
  have htrace : WordTrace (prefixWord ++ tailWord_3066360) baseStart_3066360 baseEnd_3066360 := by
    simpa [prefixWord, tailWord_3066360, baseEnd_3066360] using wordTrace_append hprefix tailTrace_3066360
  have hstable : (prefixWord ++ tailWord_3066360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066360).length < 2 ^ (prefixWord ++ tailWord_3066360).sum := by decide
  have hdescent : baseEnd_3066360 < baseStart_3066360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066380 : List Nat := [2, 2, 1, 2, 4, 2, 1, 3, 6]
def baseStart_3066380 : Nat := 118140960795 + 3066380 * 2 ^ 59
def prefixEnd_3066380 : Nat := 4983230072969 + 3 ^ 40 * 3066380 * 2
def baseEnd_3066380 : Nat := 174947423259313111983109

theorem tailTrace_3066380 : CollatzResearch.WordTrace tailWord_3066380 prefixEnd_3066380 174947423259313111983109 := by
  unfold tailWord_3066380
  simp only [CollatzResearch.WordTrace]
  refine ⟨55920033315518215427770297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74560044420690953903693729 55920033315518215427770297)
  ·
    refine ⟨41940024986638661570827723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55920033315518215427770297 41940024986638661570827723)
    ·
      refine ⟨62910037479957992356241585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41940024986638661570827723 62910037479957992356241585)
      ·
        refine ⟨47182528109968494267181189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62910037479957992356241585 47182528109968494267181189)
        ·
          refine ⟨8846724020619092675096473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47182528109968494267181189 8846724020619092675096473)
          ·
            refine ⟨6635043015464319506322355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8846724020619092675096473 6635043015464319506322355)
            ·
              refine ⟨9952564523196479259483533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6635043015464319506322355 9952564523196479259483533)
              ·
                refine ⟨3732211696198679722306325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9952564523196479259483533 3732211696198679722306325)
                ·
                  refine ⟨174947423259313111983109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3732211696198679722306325 174947423259313111983109)
                  ·
                    rfl

theorem cell23_3066380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 6].length) (baseStart_3066380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066380 prefixEnd_3066380 := by exact prefixLift 3066380
  have htrace : WordTrace (prefixWord ++ tailWord_3066380) baseStart_3066380 baseEnd_3066380 := by
    simpa [prefixWord, tailWord_3066380, baseEnd_3066380] using wordTrace_append hprefix tailTrace_3066380
  have hstable : (prefixWord ++ tailWord_3066380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066380).length < 2 ^ (prefixWord ++ tailWord_3066380).sum := by decide
  have hdescent : baseEnd_3066380 < baseStart_3066380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066393 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 3, 5]
def baseStart_3066393 : Nat := 118140960795 + 3066393 * 2 ^ 59
def prefixEnd_3066393 : Nat := 4983230072969 + 3 ^ 40 * 3066393 * 2
def baseEnd_3066393 : Nat := 524844494860775485661807

theorem tailTrace_3066393 : CollatzResearch.WordTrace tailWord_3066393 prefixEnd_3066393 524844494860775485661807 := by
  unfold tailWord_3066393
  simp only [CollatzResearch.WordTrace]
  refine ⟨111840540779989334075763833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74560360519992889383842555 111840540779989334075763833)
  ·
    refine ⟨83880405584992000556822875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111840540779989334075763833 83880405584992000556822875)
    ·
      refine ⟨125820608377488000835234313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83880405584992000556822875 125820608377488000835234313)
      ·
        refine ⟨94365456283116000626425735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125820608377488000835234313 94365456283116000626425735)
        ·
          refine ⟨141548184424674000939638603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94365456283116000626425735 141548184424674000939638603)
          ·
            refine ⟨212322276637011001409457905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141548184424674000939638603 212322276637011001409457905)
            ·
              refine ⟨159241707477758251057093429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212322276637011001409457905 159241707477758251057093429)
              ·
                refine ⟨14928910076039836036602509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159241707477758251057093429 14928910076039836036602509)
                ·
                  refine ⟨5598341278514938513725941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14928910076039836036602509 5598341278514938513725941)
                  ·
                    refine ⟨524844494860775485661807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5598341278514938513725941 524844494860775485661807)
                    ·
                      rfl

theorem cell23_3066393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 5].length) (baseStart_3066393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066393 prefixEnd_3066393 := by exact prefixLift 3066393
  have htrace : WordTrace (prefixWord ++ tailWord_3066393) baseStart_3066393 baseEnd_3066393 := by
    simpa [prefixWord, tailWord_3066393, baseEnd_3066393] using wordTrace_append hprefix tailTrace_3066393
  have hstable : (prefixWord ++ tailWord_3066393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066393).length < 2 ^ (prefixWord ++ tailWord_3066393).sum := by decide
  have hdescent : baseEnd_3066393 < baseStart_3066393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066417 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 2, 3, 2]
def baseStart_3066417 : Nat := 118140960795 + 3066417 * 2 ^ 59
def prefixEnd_3066417 : Nat := 4983230072969 + 3 ^ 40 * 3066417 * 2
def baseEnd_3066417 : Nat := 1574545808118034363085311

theorem tailTrace_3066417 : CollatzResearch.WordTrace tailWord_3066417 prefixEnd_3066417 1574545808118034363085311 := by
  unfold tailWord_3066417
  simp only [CollatzResearch.WordTrace]
  refine ⟨111841416131902386174637505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74560944087934924116425003 111841416131902386174637505)
  ·
    refine ⟨83881062098926789630978129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111841416131902386174637505 83881062098926789630978129)
    ·
      refine ⟨62910796574195092223233597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83881062098926789630978129 62910796574195092223233597)
      ·
        refine ⟨23591548715323159583712599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62910796574195092223233597 23591548715323159583712599)
        ·
          refine ⟨35387323072984739375568899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23591548715323159583712599 35387323072984739375568899)
          ·
            refine ⟨53080984609477109063353349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35387323072984739375568899 53080984609477109063353349)
            ·
              refine ⟨9952684614276957949378753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53080984609477109063353349 9952684614276957949378753)
              ·
                refine ⟨7464513460707718462034065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9952684614276957949378753 7464513460707718462034065)
                ·
                  refine ⟨5598385095530788846525549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7464513460707718462034065 5598385095530788846525549)
                  ·
                    refine ⟨2099394410824045817447081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5598385095530788846525549 2099394410824045817447081)
                    ·
                      refine ⟨1574545808118034363085311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099394410824045817447081 1574545808118034363085311)
                      ·
                        rfl

theorem cell23_3066417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_3066417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066417 prefixEnd_3066417 := by exact prefixLift 3066417
  have htrace : WordTrace (prefixWord ++ tailWord_3066417) baseStart_3066417 baseEnd_3066417 := by
    simpa [prefixWord, tailWord_3066417, baseEnd_3066417] using wordTrace_append hprefix tailTrace_3066417
  have hstable : (prefixWord ++ tailWord_3066417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066417).length < 2 ^ (prefixWord ++ tailWord_3066417).sum := by decide
  have hdescent : baseEnd_3066417 < baseStart_3066417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066423 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 3, 6]
def baseStart_3066423 : Nat := 118140960795 + 3066423 * 2 ^ 59
def prefixEnd_3066423 : Nat := 4983230072969 + 3 ^ 40 * 3066423 * 2
def baseEnd_3066423 : Nat := 524849629667320446536761

theorem tailTrace_3066423 : CollatzResearch.WordTrace tailWord_3066423 prefixEnd_3066423 524849629667320446536761 := by
  unfold tailWord_3066423
  simp only [CollatzResearch.WordTrace]
  refine ⟨111841634969880649199355923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74561089979920432799570615 111841634969880649199355923)
  ·
    refine ⟨167762452454820973799033885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111841634969880649199355923 167762452454820973799033885)
    ·
      refine ⟨62910919670557865174637707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167762452454820973799033885 62910919670557865174637707)
      ·
        refine ⟨94366379505836797761956561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62910919670557865174637707 94366379505836797761956561)
        ·
          refine ⟨70774784629377598321467421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94366379505836797761956561 70774784629377598321467421)
          ·
            refine ⟨26540544236016599370550283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70774784629377598321467421 26540544236016599370550283)
            ·
              refine ⟨39810816354024899055825425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26540544236016599370550283 39810816354024899055825425)
              ·
                refine ⟨29858112265518674291869069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39810816354024899055825425 29858112265518674291869069)
                ·
                  refine ⟨11196792099569502859450901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29858112265518674291869069 11196792099569502859450901)
                  ·
                    refine ⟨524849629667320446536761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11196792099569502859450901 524849629667320446536761)
                    ·
                      rfl

theorem cell23_3066423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_3066423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066423 prefixEnd_3066423 := by exact prefixLift 3066423
  have htrace : WordTrace (prefixWord ++ tailWord_3066423) baseStart_3066423 baseEnd_3066423 := by
    simpa [prefixWord, tailWord_3066423, baseEnd_3066423] using wordTrace_append hprefix tailTrace_3066423
  have hstable : (prefixWord ++ tailWord_3066423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066423).length < 2 ^ (prefixWord ++ tailWord_3066423).sum := by decide
  have hdescent : baseEnd_3066423 < baseStart_3066423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066424 : List Nat := [2, 1, 2, 1, 4, 1, 3, 4, 1, 1, 3]
def baseStart_3066424 : Nat := 118140960795 + 3066424 * 2 ^ 59
def prefixEnd_3066424 : Nat := 4983230072969 + 3 ^ 40 * 3066424 * 2
def baseEnd_3066424 : Nat := 1574549402482615835697779

theorem tailTrace_3066424 : CollatzResearch.WordTrace tailWord_3066424 prefixEnd_3066424 1574549402482615835697779 := by
  unfold tailWord_3066424
  simp only [CollatzResearch.WordTrace]
  refine ⟨55920835721438513185071163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74561114295251350913428217 55920835721438513185071163)
  ·
    refine ⟨83881253582157769777606745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55920835721438513185071163 83881253582157769777606745)
    ·
      refine ⟨62910940186618327333205059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83881253582157769777606745 62910940186618327333205059)
      ·
        refine ⟨94366410279927490999807589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62910940186618327333205059 94366410279927490999807589)
        ·
          refine ⟨17693701927486404562463923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94366410279927490999807589 17693701927486404562463923)
          ·
            refine ⟨26540552891229606843695885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17693701927486404562463923 26540552891229606843695885)
            ·
              refine ⟨9952707334211102566385957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26540552891229606843695885 9952707334211102566385957)
              ·
                refine ⟨1866132625164581731197367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9952707334211102566385957 1866132625164581731197367)
                ·
                  refine ⟨2799198937746872596796051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866132625164581731197367 2799198937746872596796051)
                  ·
                    refine ⟨4198798406620308895194077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2799198937746872596796051 4198798406620308895194077)
                    ·
                      refine ⟨1574549402482615835697779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4198798406620308895194077 1574549402482615835697779)
                      ·
                        rfl

theorem cell23_3066424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 1, 1, 3].length) (baseStart_3066424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066424 prefixEnd_3066424 := by exact prefixLift 3066424
  have htrace : WordTrace (prefixWord ++ tailWord_3066424) baseStart_3066424 baseEnd_3066424 := by
    simpa [prefixWord, tailWord_3066424, baseEnd_3066424] using wordTrace_append hprefix tailTrace_3066424
  have hstable : (prefixWord ++ tailWord_3066424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066424).length < 2 ^ (prefixWord ++ tailWord_3066424).sum := by decide
  have hdescent : baseEnd_3066424 < baseStart_3066424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066443 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 6]
def baseStart_3066443 : Nat := 118140960795 + 3066443 * 2 ^ 59
def prefixEnd_3066443 : Nat := 4983230072969 + 3 ^ 40 * 3066443 * 2
def baseEnd_3066443 : Nat := 1574559158615051261360191

theorem tailTrace_3066443 : CollatzResearch.WordTrace tailWord_3066443 prefixEnd_3066443 1574559158615051261360191 := by
  unfold tailWord_3066443
  simp only [CollatzResearch.WordTrace]
  refine ⟨111842364429808192615083983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74561576286538795076722655 111842364429808192615083983)
  ·
    refine ⟨167763546644712288922625975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111842364429808192615083983 167763546644712288922625975)
    ·
      refine ⟨251645319967068433383938963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167763546644712288922625975 251645319967068433383938963)
      ·
        refine ⟨377467979950602650075908445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251645319967068433383938963 377467979950602650075908445)
        ·
          refine ⟨141550492481475993778465667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 377467979950602650075908445 141550492481475993778465667)
          ·
            refine ⟨212325738722213990667698501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141550492481475993778465667 212325738722213990667698501)
            ·
              refine ⟨39811076010415123250193469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212325738722213990667698501 39811076010415123250193469)
              ·
                refine ⟨14929153503905671218822551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39811076010415123250193469 14929153503905671218822551)
                ·
                  refine ⟨22393730255858506828233827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14929153503905671218822551 22393730255858506828233827)
                  ·
                    refine ⟨33590595383787760242350741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22393730255858506828233827 33590595383787760242350741)
                    ·
                      refine ⟨1574559158615051261360191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33590595383787760242350741 1574559158615051261360191)
                      ·
                        rfl

theorem cell23_3066443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 6].length) (baseStart_3066443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066443 prefixEnd_3066443 := by exact prefixLift 3066443
  have htrace : WordTrace (prefixWord ++ tailWord_3066443) baseStart_3066443 baseEnd_3066443 := by
    simpa [prefixWord, tailWord_3066443, baseEnd_3066443] using wordTrace_append hprefix tailTrace_3066443
  have hstable : (prefixWord ++ tailWord_3066443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066443).length < 2 ^ (prefixWord ++ tailWord_3066443).sum := by decide
  have hdescent : baseEnd_3066443 < baseStart_3066443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066447 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 5, 2, 2]
def baseStart_3066447 : Nat := 118140960795 + 3066447 * 2 ^ 59
def prefixEnd_3066447 : Nat := 4983230072969 + 3 ^ 40 * 3066447 * 2
def baseEnd_3066447 : Nat := 1574561212537669245710173

theorem tailTrace_3066447 : CollatzResearch.WordTrace tailWord_3066447 prefixEnd_3066447 1574561212537669245710173 := by
  unfold tailWord_3066447
  simp only [CollatzResearch.WordTrace]
  refine ⟨111842510321793701298229595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74561673547862467532153063 111842510321793701298229595)
  ·
    refine ⟨167763765482690551947344393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111842510321793701298229595 167763765482690551947344393)
    ·
      refine ⟨125822824112017913960508295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167763765482690551947344393 125822824112017913960508295)
      ·
        refine ⟨188734236168026870940762443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125822824112017913960508295 188734236168026870940762443)
        ·
          refine ⟨283101354252040306411143665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188734236168026870940762443 283101354252040306411143665)
          ·
            refine ⟨212326015689030229808357749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283101354252040306411143665 212326015689030229808357749)
            ·
              refine ⟨19905563970846584044533539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212326015689030229808357749 19905563970846584044533539)
              ·
                refine ⟨29858345956269876066800309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19905563970846584044533539 29858345956269876066800309)
                ·
                  refine ⟨2799219933400300881262529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29858345956269876066800309 2799219933400300881262529)
                  ·
                    refine ⟨2099414950050225660946897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2799219933400300881262529 2099414950050225660946897)
                    ·
                      refine ⟨1574561212537669245710173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099414950050225660946897 1574561212537669245710173)
                      ·
                        rfl

theorem cell23_3066447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 2, 2].length) (baseStart_3066447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066447 prefixEnd_3066447 := by exact prefixLift 3066447
  have htrace : WordTrace (prefixWord ++ tailWord_3066447) baseStart_3066447 baseEnd_3066447 := by
    simpa [prefixWord, tailWord_3066447, baseEnd_3066447] using wordTrace_append hprefix tailTrace_3066447
  have hstable : (prefixWord ++ tailWord_3066447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066447).length < 2 ^ (prefixWord ++ tailWord_3066447).sum := by decide
  have hdescent : baseEnd_3066447 < baseStart_3066447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066453 : List Nat := [1, 3, 2, 2, 1, 1, 2, 11]
def baseStart_3066453 : Nat := 118140960795 + 3066453 * 2 ^ 59
def prefixEnd_3066453 : Nat := 4983230072969 + 3 ^ 40 * 3066453 * 2
def baseEnd_3066453 : Nat := 58317196052651711934635

theorem tailTrace_3066453 : CollatzResearch.WordTrace tailWord_3066453 prefixEnd_3066453 58317196052651711934635 := by
  unfold tailWord_3066453
  simp only [CollatzResearch.WordTrace]
  refine ⟨111842729159771964322948013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74561819439847976215298675 111842729159771964322948013)
  ·
    refine ⟨41941023434914486621105505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111842729159771964322948013 41941023434914486621105505)
    ·
      refine ⟨31455767576185864965829129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41941023434914486621105505 31455767576185864965829129)
      ·
        refine ⟨23591825682139398724371847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31455767576185864965829129 23591825682139398724371847)
        ·
          refine ⟨35387738523209098086557771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23591825682139398724371847 35387738523209098086557771)
          ·
            refine ⟨53081607784813647129836657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35387738523209098086557771 53081607784813647129836657)
            ·
              refine ⟨39811205838610235347377493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53081607784813647129836657 39811205838610235347377493)
              ·
                refine ⟨58317196052651711934635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 39811205838610235347377493 58317196052651711934635)
                ·
                  rfl

theorem cell23_3066453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 11].length) (baseStart_3066453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066453 prefixEnd_3066453 := by exact prefixLift 3066453
  have htrace : WordTrace (prefixWord ++ tailWord_3066453) baseStart_3066453 baseEnd_3066453 := by
    simpa [prefixWord, tailWord_3066453, baseEnd_3066453] using wordTrace_append hprefix tailTrace_3066453
  have hstable : (prefixWord ++ tailWord_3066453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066453).length < 2 ^ (prefixWord ++ tailWord_3066453).sum := by decide
  have hdescent : baseEnd_3066453 < baseStart_3066453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066467 : List Nat := [1, 1, 1, 5, 1, 2, 3, 3, 1, 2, 3]
def baseStart_3066467 : Nat := 118140960795 + 3066467 * 2 ^ 59
def prefixEnd_3066467 : Nat := 4983230072969 + 3 ^ 40 * 3066467 * 2
def baseEnd_3066467 : Nat := 1574571482150759167460081

theorem tailTrace_3066467 : CollatzResearch.WordTrace tailWord_3066467 prefixEnd_3066467 1574571482150759167460081 := by
  unfold tailWord_3066467
  simp only [CollatzResearch.WordTrace]
  refine ⟨111843239781721244713957655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74562159854480829809305103 111843239781721244713957655)
  ·
    refine ⟨167764859672581867070936483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111843239781721244713957655 167764859672581867070936483)
    ·
      refine ⟨251647289508872800606404725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167764859672581867070936483 251647289508872800606404725)
      ·
        refine ⟨23591933391456825056850443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251647289508872800606404725 23591933391456825056850443)
        ·
          refine ⟨35387900087185237585275665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23591933391456825056850443 35387900087185237585275665)
          ·
            refine ⟨26540925065388928188956749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35387900087185237585275665 26540925065388928188956749)
            ·
              refine ⟨9952846899520848070858781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26540925065388928188956749 9952846899520848070858781)
              ·
                refine ⟨3732317587320318026572043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9952846899520848070858781 3732317587320318026572043)
                ·
                  refine ⟨5598476380980477039858065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3732317587320318026572043 5598476380980477039858065)
                  ·
                    refine ⟨4198857285735357779893549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5598476380980477039858065 4198857285735357779893549)
                    ·
                      refine ⟨1574571482150759167460081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4198857285735357779893549 1574571482150759167460081)
                      ·
                        rfl

theorem cell23_3066467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_3066467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066467 prefixEnd_3066467 := by exact prefixLift 3066467
  have htrace : WordTrace (prefixWord ++ tailWord_3066467) baseStart_3066467 baseEnd_3066467 := by
    simpa [prefixWord, tailWord_3066467, baseEnd_3066467] using wordTrace_append hprefix tailTrace_3066467
  have hstable : (prefixWord ++ tailWord_3066467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066467).length < 2 ^ (prefixWord ++ tailWord_3066467).sum := by decide
  have hdescent : baseEnd_3066467 < baseStart_3066467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066473 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 6]
def baseStart_3066473 : Nat := 118140960795 + 3066473 * 2 ^ 59
def prefixEnd_3066473 : Nat := 4983230072969 + 3 ^ 40 * 3066473 * 2
def baseEnd_3066473 : Nat := 1574574563034686143985053

theorem tailTrace_3066473 : CollatzResearch.WordTrace tailWord_3066473 prefixEnd_3066473 1574574563034686143985053 := by
  unfold tailWord_3066473
  simp only [CollatzResearch.WordTrace]
  refine ⟨111843458619699507738676073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74562305746466338492450715 111843458619699507738676073)
  ·
    refine ⟨83882593964774630804007055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111843458619699507738676073 83882593964774630804007055)
    ·
      refine ⟨125823890947161946206010583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83882593964774630804007055 125823890947161946206010583)
      ·
        refine ⟨188735836420742919309015875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125823890947161946206010583 188735836420742919309015875)
        ·
          refine ⟨283103754631114378963523813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188735836420742919309015875 283103754631114378963523813)
          ·
            refine ⟨53081953993333946055660715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283103754631114378963523813 53081953993333946055660715)
            ·
              refine ⟨79622930990000919083491073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53081953993333946055660715 79622930990000919083491073)
              ·
                refine ⟨59717198242500689312618305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79622930990000919083491073 59717198242500689312618305)
                ·
                  refine ⟨44787898681875516984463729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59717198242500689312618305 44787898681875516984463729)
                  ·
                    refine ⟨33590924011406637738347797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44787898681875516984463729 33590924011406637738347797)
                    ·
                      refine ⟨1574574563034686143985053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33590924011406637738347797 1574574563034686143985053)
                      ·
                        rfl

theorem cell23_3066473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_3066473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066473 prefixEnd_3066473 := by exact prefixLift 3066473
  have htrace : WordTrace (prefixWord ++ tailWord_3066473) baseStart_3066473 baseEnd_3066473 := by
    simpa [prefixWord, tailWord_3066473, baseEnd_3066473] using wordTrace_append hprefix tailTrace_3066473
  have hstable : (prefixWord ++ tailWord_3066473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066473).length < 2 ^ (prefixWord ++ tailWord_3066473).sum := by decide
  have hdescent : baseEnd_3066473 < baseStart_3066473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066483 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 2, 7]
def baseStart_3066483 : Nat := 118140960795 + 3066483 * 2 ^ 59
def prefixEnd_3066483 : Nat := 4983230072969 + 3 ^ 40 * 3066483 * 2
def baseEnd_3066483 : Nat := 524859899280410368286669

theorem tailTrace_3066483 : CollatzResearch.WordTrace tailWord_3066483 prefixEnd_3066483 524859899280410368286669 := by
  unfold tailWord_3066483
  simp only [CollatzResearch.WordTrace]
  refine ⟨111843823349663279446540103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74562548899775519631026735 111843823349663279446540103)
  ·
    refine ⟨167765735024494919169810155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111843823349663279446540103 167765735024494919169810155)
    ·
      refine ⟨251648602536742378754715233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167765735024494919169810155 251648602536742378754715233)
      ·
        refine ⟨188736451902556784066036425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251648602536742378754715233 188736451902556784066036425)
        ·
          refine ⟨141552338926917588049527319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188736451902556784066036425 141552338926917588049527319)
          ·
            refine ⟨212328508390376382074290979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141552338926917588049527319 212328508390376382074290979)
            ·
              refine ⟨318492762585564573111436469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212328508390376382074290979 318492762585564573111436469)
              ·
                refine ⟨29858696492396678729197169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 318492762585564573111436469 29858696492396678729197169)
                ·
                  refine ⟨22394022369297509046897877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29858696492396678729197169 22394022369297509046897877)
                  ·
                    refine ⟨524859899280410368286669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22394022369297509046897877 524859899280410368286669)
                    ·
                      rfl

theorem cell23_3066483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 7].length) (baseStart_3066483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066483 prefixEnd_3066483 := by exact prefixLift 3066483
  have htrace : WordTrace (prefixWord ++ tailWord_3066483) baseStart_3066483 baseEnd_3066483 := by
    simpa [prefixWord, tailWord_3066483, baseEnd_3066483] using wordTrace_append hprefix tailTrace_3066483
  have hstable : (prefixWord ++ tailWord_3066483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066483).length < 2 ^ (prefixWord ++ tailWord_3066483).sum := by decide
  have hdescent : baseEnd_3066483 < baseStart_3066483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066510 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_3066510 : Nat := 118140960795 + 3066510 * 2 ^ 59
def prefixEnd_3066510 : Nat := 4983230072969 + 3 ^ 40 * 3066510 * 2
def baseEnd_3066510 : Nat := 1574593561818902499222383

theorem tailTrace_3066510 : CollatzResearch.WordTrace tailWord_3066510 prefixEnd_3066510 1574593561818902499222383 := by
  unfold tailWord_3066510
  simp only [CollatzResearch.WordTrace]
  refine ⟨13980601015070682882221623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74563205413710308705181989 13980601015070682882221623)
  ·
    refine ⟨20970901522606024323332435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13980601015070682882221623 20970901522606024323332435)
    ·
      refine ⟨31456352283909036484998653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20970901522606024323332435 31456352283909036484998653)
      ·
        refine ⟨11796132106465888681874495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31456352283909036484998653 11796132106465888681874495)
        ·
          refine ⟨17694198159698833022811743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11796132106465888681874495 17694198159698833022811743)
          ·
            refine ⟨26541297239548249534217615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17694198159698833022811743 26541297239548249534217615)
            ·
              refine ⟨39811945859322374301326423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26541297239548249534217615 39811945859322374301326423)
              ·
                refine ⟨59717918788983561451989635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39811945859322374301326423 59717918788983561451989635)
                ·
                  refine ⟨89576878183475342177984453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59717918788983561451989635 89576878183475342177984453)
                  ·
                    refine ⟨16795664659401626658372085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89576878183475342177984453 16795664659401626658372085)
                    ·
                      refine ⟨1574593561818902499222383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16795664659401626658372085 1574593561818902499222383)
                      ·
                        rfl

theorem cell23_3066510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_3066510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066510 prefixEnd_3066510 := by exact prefixLift 3066510
  have htrace : WordTrace (prefixWord ++ tailWord_3066510) baseStart_3066510 baseEnd_3066510 := by
    simpa [prefixWord, tailWord_3066510, baseEnd_3066510] using wordTrace_append hprefix tailTrace_3066510
  have hstable : (prefixWord ++ tailWord_3066510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066510).length < 2 ^ (prefixWord ++ tailWord_3066510).sum := by decide
  have hdescent : baseEnd_3066510 < baseStart_3066510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066514 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_3066514 : Nat := 118140960795 + 3066514 * 2 ^ 59
def prefixEnd_3066514 : Nat := 4983230072969 + 3 ^ 40 * 3066514 * 2
def baseEnd_3066514 : Nat := 1574595615741520483572365

theorem tailTrace_3066514 : CollatzResearch.WordTrace tailWord_3066514 prefixEnd_3066514 1574595615741520483572365 := by
  unfold tailWord_3066514
  simp only [CollatzResearch.WordTrace]
  refine ⟨27961238503137742935229649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74563302675033981160612397 27961238503137742935229649)
  ·
    refine ⟨20970928877353307201422237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27961238503137742935229649 20970928877353307201422237)
    ·
      refine ⟨7864098329007490200533339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20970928877353307201422237 7864098329007490200533339)
      ·
        refine ⟨11796147493511235300800009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7864098329007490200533339 11796147493511235300800009)
        ·
          refine ⟨8847110620133426475600007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11796147493511235300800009 8847110620133426475600007)
          ·
            refine ⟨13270665930200139713400011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8847110620133426475600007 13270665930200139713400011)
            ·
              refine ⟨19905998895300209570100017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13270665930200139713400011 19905998895300209570100017)
              ·
                refine ⟨14929499171475157177575013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19905998895300209570100017 14929499171475157177575013)
                ·
                  refine ⟨2799281094651591970795315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14929499171475157177575013 2799281094651591970795315)
                  ·
                    refine ⟨4198921641977387956192973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2799281094651591970795315 4198921641977387956192973)
                    ·
                      refine ⟨1574595615741520483572365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4198921641977387956192973 1574595615741520483572365)
                      ·
                        rfl

theorem cell23_3066514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_3066514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066514 prefixEnd_3066514 := by exact prefixLift 3066514
  have htrace : WordTrace (prefixWord ++ tailWord_3066514) baseStart_3066514 baseEnd_3066514 := by
    simpa [prefixWord, tailWord_3066514, baseEnd_3066514] using wordTrace_append hprefix tailTrace_3066514
  have hstable : (prefixWord ++ tailWord_3066514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066514).length < 2 ^ (prefixWord ++ tailWord_3066514).sum := by decide
  have hdescent : baseEnd_3066514 < baseStart_3066514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066523 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 9]
def baseStart_3066523 : Nat := 118140960795 + 3066523 * 2 ^ 59
def prefixEnd_3066523 : Nat := 4983230072969 + 3 ^ 40 * 3066523 * 2
def baseEnd_3066523 : Nat := 1574600237067410948359823

theorem tailTrace_3066523 : CollatzResearch.WordTrace tailWord_3066523 prefixEnd_3066523 1574600237067410948359823 := by
  unfold tailWord_3066523
  simp only [CollatzResearch.WordTrace]
  refine ⟨111845282269518366277996223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74563521513012244185330815 111845282269518366277996223)
  ·
    refine ⟨167767923404277549416994335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111845282269518366277996223 167767923404277549416994335)
    ·
      refine ⟨251651885106416324125491503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167767923404277549416994335 251651885106416324125491503)
      ·
        refine ⟨377477827659624486188237255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251651885106416324125491503 377477827659624486188237255)
        ·
          refine ⟨566216741489436729282355883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377477827659624486188237255 566216741489436729282355883)
          ·
            refine ⟨849325112234155093923533825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566216741489436729282355883 849325112234155093923533825)
            ·
              refine ⟨636993834175616320442650369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849325112234155093923533825 636993834175616320442650369)
              ·
                refine ⟨477745375631712240331987777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636993834175616320442650369 477745375631712240331987777)
                ·
                  refine ⟨358309031723784180248990833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477745375631712240331987777 358309031723784180248990833)
                  ·
                    refine ⟨268731773792838135186743125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 358309031723784180248990833 268731773792838135186743125)
                    ·
                      refine ⟨1574600237067410948359823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 268731773792838135186743125 1574600237067410948359823)
                      ·
                        rfl

theorem cell23_3066523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_3066523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066523 prefixEnd_3066523 := by exact prefixLift 3066523
  have htrace : WordTrace (prefixWord ++ tailWord_3066523) baseStart_3066523 baseEnd_3066523 := by
    simpa [prefixWord, tailWord_3066523, baseEnd_3066523] using wordTrace_append hprefix tailTrace_3066523
  have hstable : (prefixWord ++ tailWord_3066523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066523).length < 2 ^ (prefixWord ++ tailWord_3066523).sum := by decide
  have hdescent : baseEnd_3066523 < baseStart_3066523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066577 : List Nat := [1, 2, 2, 1, 2, 3, 2, 5, 5]
def baseStart_3066577 : Nat := 118140960795 + 3066577 * 2 ^ 59
def prefixEnd_3066577 : Nat := 4983230072969 + 3 ^ 40 * 3066577 * 2
def baseEnd_3066577 : Nat := 174958662780305970787175

theorem tailTrace_3066577 : CollatzResearch.WordTrace tailWord_3066577 prefixEnd_3066577 174958662780305970787175 := by
  unfold tailWord_3066577
  simp only [CollatzResearch.WordTrace]
  refine ⟨111847251811322733500461985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74564834540881822333641323 111847251811322733500461985)
  ·
    refine ⟨83885438858492050125346489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111847251811322733500461985 83885438858492050125346489)
    ·
      refine ⟨62914079143869037594009867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83885438858492050125346489 62914079143869037594009867)
      ·
        refine ⟨94371118715803556391014801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62914079143869037594009867 94371118715803556391014801)
        ·
          refine ⟨70778339036852667293261101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94371118715803556391014801 70778339036852667293261101)
          ·
            refine ⟨26541877138819750234972913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70778339036852667293261101 26541877138819750234972913)
            ·
              refine ⟨19906407854114812676229685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26541877138819750234972913 19906407854114812676229685)
              ·
                refine ⟨1866225736323263688396533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19906407854114812676229685 1866225736323263688396533)
                ·
                  refine ⟨174958662780305970787175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1866225736323263688396533 174958662780305970787175)
                  ·
                    rfl

theorem cell23_3066577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 5].length) (baseStart_3066577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066577 prefixEnd_3066577 := by exact prefixLift 3066577
  have htrace : WordTrace (prefixWord ++ tailWord_3066577) baseStart_3066577 baseEnd_3066577 := by
    simpa [prefixWord, tailWord_3066577, baseEnd_3066577] using wordTrace_append hprefix tailTrace_3066577
  have hstable : (prefixWord ++ tailWord_3066577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066577).length < 2 ^ (prefixWord ++ tailWord_3066577).sum := by decide
  have hdescent : baseEnd_3066577 < baseStart_3066577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066588 : List Nat := [2, 2, 5, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_3066588 : Nat := 118140960795 + 3066588 * 2 ^ 59
def prefixEnd_3066588 : Nat := 4983230072969 + 3 ^ 40 * 3066588 * 2
def baseEnd_3066588 : Nat := 1574633613309953194047025

theorem tailTrace_3066588 : CollatzResearch.WordTrace tailWord_3066588 prefixEnd_3066588 1574633613309953194047025 := by
  unfold tailWord_3066588
  simp only [CollatzResearch.WordTrace]
  refine ⟨55923826507141441189556209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74565102009521921586074945 55923826507141441189556209)
  ·
    refine ⟨41942869880356080892167157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55923826507141441189556209 41942869880356080892167157)
    ·
      refine ⟨3932144051283382583640671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41942869880356080892167157 3932144051283382583640671)
      ·
        refine ⟨5898216076925073875461007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3932144051283382583640671 5898216076925073875461007)
        ·
          refine ⟨8847324115387610813191511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5898216076925073875461007 8847324115387610813191511)
          ·
            refine ⟨13270986173081416219787267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8847324115387610813191511 13270986173081416219787267)
            ·
              refine ⟨19906479259622124329680901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13270986173081416219787267 19906479259622124329680901)
              ·
                refine ⟨3732464861179148311815169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19906479259622124329680901 3732464861179148311815169)
                ·
                  refine ⟨2799348645884361233861377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3732464861179148311815169 2799348645884361233861377)
                  ·
                    refine ⟨2099511484413270925396033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2799348645884361233861377 2099511484413270925396033)
                    ·
                      refine ⟨1574633613309953194047025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099511484413270925396033 1574633613309953194047025)
                      ·
                        rfl

theorem cell23_3066588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_3066588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066588 prefixEnd_3066588 := by exact prefixLift 3066588
  have htrace : WordTrace (prefixWord ++ tailWord_3066588) baseStart_3066588 baseEnd_3066588 := by
    simpa [prefixWord, tailWord_3066588, baseEnd_3066588] using wordTrace_append hprefix tailTrace_3066588
  have hstable : (prefixWord ++ tailWord_3066588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066588).length < 2 ^ (prefixWord ++ tailWord_3066588).sum := by decide
  have hdescent : baseEnd_3066588 < baseStart_3066588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066614 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_3066614 : Nat := 118140960795 + 3066614 * 2 ^ 59
def prefixEnd_3066614 : Nat := 4983230072969 + 3 ^ 40 * 3066614 * 2
def baseEnd_3066614 : Nat := 1574646963806970092321905

theorem tailTrace_3066614 : CollatzResearch.WordTrace tailWord_3066614 prefixEnd_3066614 1574646963806970092321905 := by
  unfold tailWord_3066614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6990537582011793051222431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74565734208125792546372597 6990537582011793051222431)
  ·
    refine ⟨10485806373017689576833647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6990537582011793051222431 10485806373017689576833647)
    ·
      refine ⟨15728709559526534365250471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10485806373017689576833647 15728709559526534365250471)
      ·
        refine ⟨23593064339289801547875707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15728709559526534365250471 23593064339289801547875707)
        ·
          refine ⟨35389596508934702321813561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23593064339289801547875707 35389596508934702321813561)
          ·
            refine ⟨26542197381701026741360171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35389596508934702321813561 26542197381701026741360171)
            ·
              refine ⟨39813296072551540112040257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26542197381701026741360171 39813296072551540112040257)
              ·
                refine ⟨29859972054413655084030193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39813296072551540112040257 29859972054413655084030193)
                ·
                  refine ⟨22394979040810241313022645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29859972054413655084030193 22394979040810241313022645)
                  ·
                    refine ⟨2099529285075960123095873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22394979040810241313022645 2099529285075960123095873)
                    ·
                      refine ⟨1574646963806970092321905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099529285075960123095873 1574646963806970092321905)
                      ·
                        rfl

theorem cell23_3066614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_3066614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066614 prefixEnd_3066614 := by exact prefixLift 3066614
  have htrace : WordTrace (prefixWord ++ tailWord_3066614) baseStart_3066614 baseEnd_3066614 := by
    simpa [prefixWord, tailWord_3066614, baseEnd_3066614] using wordTrace_append hprefix tailTrace_3066614
  have hstable : (prefixWord ++ tailWord_3066614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066614).length < 2 ^ (prefixWord ++ tailWord_3066614).sum := by decide
  have hdescent : baseEnd_3066614 < baseStart_3066614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066627 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 3, 6, 2]
def baseStart_3066627 : Nat := 118140960795 + 3066627 * 2 ^ 59
def prefixEnd_3066627 : Nat := 4983230072969 + 3 ^ 40 * 3066627 * 2
def baseEnd_3066627 : Nat := 1574653639055478541459345

theorem tailTrace_3066627 : CollatzResearch.WordTrace tailWord_3066627 prefixEnd_3066627 1574653639055478541459345 := by
  unfold tailWord_3066627
  simp only [CollatzResearch.WordTrace]
  refine ⟨111849075461141592039782135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74566050307427728026521423 111849075461141592039782135)
  ·
    refine ⟨167773613191712388059673203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111849075461141592039782135 167773613191712388059673203)
    ·
      refine ⟨251660419787568582089509805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167773613191712388059673203 251660419787568582089509805)
      ·
        refine ⟨94372657420338218283566177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251660419787568582089509805 94372657420338218283566177)
        ·
          refine ⟨70779493065253663712674633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94372657420338218283566177 70779493065253663712674633)
          ·
            refine ⟨53084619798940247784505975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70779493065253663712674633 53084619798940247784505975)
            ·
              refine ⟨79626929698410371676758963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53084619798940247784505975 79626929698410371676758963)
              ·
                refine ⟨119440394547615557515138445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79626929698410371676758963 119440394547615557515138445)
                ·
                  refine ⟨44790147955355834068176917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119440394547615557515138445 44790147955355834068176917)
                  ·
                    refine ⟨2099538185407304721945793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44790147955355834068176917 2099538185407304721945793)
                    ·
                      refine ⟨1574653639055478541459345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099538185407304721945793 1574653639055478541459345)
                      ·
                        rfl

theorem cell23_3066627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 6, 2].length) (baseStart_3066627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066627 prefixEnd_3066627 := by exact prefixLift 3066627
  have htrace : WordTrace (prefixWord ++ tailWord_3066627) baseStart_3066627 baseEnd_3066627 := by
    simpa [prefixWord, tailWord_3066627, baseEnd_3066627] using wordTrace_append hprefix tailTrace_3066627
  have hstable : (prefixWord ++ tailWord_3066627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066627).length < 2 ^ (prefixWord ++ tailWord_3066627).sum := by decide
  have hdescent : baseEnd_3066627 < baseStart_3066627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066704 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 4, 3, 2]
def baseStart_3066704 : Nat := 118140960795 + 3066704 * 2 ^ 59
def prefixEnd_3066704 : Nat := 4983230072969 + 3 ^ 40 * 3066704 * 2
def baseEnd_3066704 : Nat := 1574693177065874740196491

theorem tailTrace_3066704 : CollatzResearch.WordTrace tailWord_3066704 prefixEnd_3066704 1574693177065874740196491 := by
  unfold tailWord_3066704
  simp only [CollatzResearch.WordTrace]
  refine ⟨55925941940931317095167583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74567922587908422793556777 55925941940931317095167583)
  ·
    refine ⟨83888912911396975642751375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55925941940931317095167583 83888912911396975642751375)
    ·
      refine ⟨125833369367095463464127063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83888912911396975642751375 125833369367095463464127063)
      ·
        refine ⟨188750054050643195196190595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125833369367095463464127063 188750054050643195196190595)
        ·
          refine ⟨283125081075964792794285893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188750054050643195196190595 283125081075964792794285893)
          ·
            refine ⟨53085952701743398648928605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283125081075964792794285893 53085952701743398648928605)
            ·
              refine ⟨19907232263153774493348227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53085952701743398648928605 19907232263153774493348227)
              ·
                refine ⟨29860848394730661740022341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19907232263153774493348227 29860848394730661740022341)
                ·
                  refine ⟨5598909074011999076254189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29860848394730661740022341 5598909074011999076254189)
                  ·
                    refine ⟨2099590902754499653595321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5598909074011999076254189 2099590902754499653595321)
                    ·
                      refine ⟨1574693177065874740196491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099590902754499653595321 1574693177065874740196491)
                      ·
                        rfl

theorem cell23_3066704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 4, 3, 2].length) (baseStart_3066704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066704 prefixEnd_3066704 := by exact prefixLift 3066704
  have htrace : WordTrace (prefixWord ++ tailWord_3066704) baseStart_3066704 baseEnd_3066704 := by
    simpa [prefixWord, tailWord_3066704, baseEnd_3066704] using wordTrace_append hprefix tailTrace_3066704
  have hstable : (prefixWord ++ tailWord_3066704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066704).length < 2 ^ (prefixWord ++ tailWord_3066704).sum := by decide
  have hdescent : baseEnd_3066704 < baseStart_3066704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066711 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 3, 1, 3]
def baseStart_3066711 : Nat := 118140960795 + 3066711 * 2 ^ 59
def prefixEnd_3066711 : Nat := 4983230072969 + 3 ^ 40 * 3066711 * 2
def baseEnd_3066711 : Nat := 1574696771430456212808959

theorem tailTrace_3066711 : CollatzResearch.WordTrace tailWord_3066711 prefixEnd_3066711 1574696771430456212808959 := by
  unfold tailWord_3066711
  simp only [CollatzResearch.WordTrace]
  refine ⟨111852139192837274385839987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74568092795224849590559991 111852139192837274385839987)
  ·
    refine ⟨167778208789255911578759981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111852139192837274385839987 167778208789255911578759981)
    ·
      refine ⟨62916828295970966842034993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167778208789255911578759981 62916828295970966842034993)
      ·
        refine ⟨47187621221978225131526245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62916828295970966842034993 47187621221978225131526245)
        ·
          refine ⟨8847678979120917212161171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47187621221978225131526245 8847678979120917212161171)
          ·
            refine ⟨13271518468681375818241757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8847678979120917212161171 13271518468681375818241757)
            ·
              refine ⟨4976819425755515931840659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13271518468681375818241757 4976819425755515931840659)
              ·
                refine ⟨7465229138633273897760989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4976819425755515931840659 7465229138633273897760989)
                ·
                  refine ⟨2799460926987477711660371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7465229138633273897760989 2799460926987477711660371)
                  ·
                    refine ⟨4199191390481216567490557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2799460926987477711660371 4199191390481216567490557)
                    ·
                      refine ⟨1574696771430456212808959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4199191390481216567490557 1574696771430456212808959)
                      ·
                        rfl

theorem cell23_3066711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_3066711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066711 prefixEnd_3066711 := by exact prefixLift 3066711
  have htrace : WordTrace (prefixWord ++ tailWord_3066711) baseStart_3066711 baseEnd_3066711 := by
    simpa [prefixWord, tailWord_3066711, baseEnd_3066711] using wordTrace_append hprefix tailTrace_3066711
  have hstable : (prefixWord ++ tailWord_3066711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066711).length < 2 ^ (prefixWord ++ tailWord_3066711).sum := by decide
  have hdescent : baseEnd_3066711 < baseStart_3066711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066747 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 4]
def baseStart_3066747 : Nat := 118140960795 + 3066747 * 2 ^ 59
def prefixEnd_3066747 : Nat := 4983230072969 + 3 ^ 40 * 3066747 * 2
def baseEnd_3066747 : Nat := 1574715256734018071958793

theorem tailTrace_3066747 : CollatzResearch.WordTrace tailWord_3066747 prefixEnd_3066747 1574715256734018071958793 := by
  unfold tailWord_3066747
  simp only [CollatzResearch.WordTrace]
  refine ⟨111853452220706852534150495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74568968147137901689433663 111853452220706852534150495)
  ·
    refine ⟨167780178331060278801225743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111853452220706852534150495 167780178331060278801225743)
    ·
      refine ⟨251670267496590418201838615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167780178331060278801225743 251670267496590418201838615)
      ·
        refine ⟨377505401244885627302757923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251670267496590418201838615 377505401244885627302757923)
        ·
          refine ⟨566258101867328440954136885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377505401244885627302757923 566258101867328440954136885)
          ·
            refine ⟨53086697050062041339450333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 566258101867328440954136885 53086697050062041339450333)
            ·
              refine ⟨19907511393773265502293875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53086697050062041339450333 19907511393773265502293875)
              ·
                refine ⟨29861267090659898253440813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19907511393773265502293875 29861267090659898253440813)
                ·
                  refine ⟨11197975158997461845040305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29861267090659898253440813 11197975158997461845040305)
                  ·
                    refine ⟨8398481369248096383780229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11197975158997461845040305 8398481369248096383780229)
                    ·
                      refine ⟨1574715256734018071958793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8398481369248096383780229 1574715256734018071958793)
                      ·
                        rfl

theorem cell23_3066747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 4].length) (baseStart_3066747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066747 prefixEnd_3066747 := by exact prefixLift 3066747
  have htrace : WordTrace (prefixWord ++ tailWord_3066747) baseStart_3066747 baseEnd_3066747 := by
    simpa [prefixWord, tailWord_3066747, baseEnd_3066747] using wordTrace_append hprefix tailTrace_3066747
  have hstable : (prefixWord ++ tailWord_3066747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066747).length < 2 ^ (prefixWord ++ tailWord_3066747).sum := by decide
  have hdescent : baseEnd_3066747 < baseStart_3066747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066761 : List Nat := [1, 2, 1, 1, 5, 3, 2, 2, 2, 4]
def baseStart_3066761 : Nat := 118140960795 + 3066761 * 2 ^ 59
def prefixEnd_3066761 : Nat := 4983230072969 + 3 ^ 40 * 3066761 * 2
def baseEnd_3066761 : Nat := 524907481821060339061243

theorem tailTrace_3066761 : CollatzResearch.WordTrace tailWord_3066761 prefixEnd_3066761 524907481821060339061243 := by
  unfold tailWord_3066761
  simp only [CollatzResearch.WordTrace]
  refine ⟨111853962842656132925160137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74569308561770755283440091 111853962842656132925160137)
  ·
    refine ⟨83890472131992099693870103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111853962842656132925160137 83890472131992099693870103)
    ·
      refine ⟨125835708197988149540805155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83890472131992099693870103 125835708197988149540805155)
      ·
        refine ⟨188753562296982224311207733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125835708197988149540805155 188753562296982224311207733)
        ·
          refine ⟨17695646465342083529175725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188753562296982224311207733 17695646465342083529175725)
          ·
            refine ⟨6635867424503281323440897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17695646465342083529175725 6635867424503281323440897)
            ·
              refine ⟨4976900568377460992580673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6635867424503281323440897 4976900568377460992580673)
              ·
                refine ⟨3732675426283095744435505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4976900568377460992580673 3732675426283095744435505)
                ·
                  refine ⟨2799506569712321808326629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3732675426283095744435505 2799506569712321808326629)
                  ·
                    refine ⟨524907481821060339061243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2799506569712321808326629 524907481821060339061243)
                    ·
                      rfl

theorem cell23_3066761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 4].length) (baseStart_3066761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066761 prefixEnd_3066761 := by exact prefixLift 3066761
  have htrace : WordTrace (prefixWord ++ tailWord_3066761) baseStart_3066761 baseEnd_3066761 := by
    simpa [prefixWord, tailWord_3066761, baseEnd_3066761] using wordTrace_append hprefix tailTrace_3066761
  have hstable : (prefixWord ++ tailWord_3066761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066761).length < 2 ^ (prefixWord ++ tailWord_3066761).sum := by decide
  have hdescent : baseEnd_3066761 < baseStart_3066761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066762 : List Nat := [3, 1, 2, 4, 1, 3, 2, 2, 1, 1, 3]
def baseStart_3066762 : Nat := 118140960795 + 3066762 * 2 ^ 59
def prefixEnd_3066762 : Nat := 4983230072969 + 3 ^ 40 * 3066762 * 2
def baseEnd_3066762 : Nat := 1574722958943835513271225

theorem tailTrace_3066762 : CollatzResearch.WordTrace tailWord_3066762 prefixEnd_3066762 1574722958943835513271225 := by
  unfold tailWord_3066762
  simp only [CollatzResearch.WordTrace]
  refine ⟨27963499828913127523986635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74569332877101673397297693 27963499828913127523986635)
  ·
    refine ⟨41945249743369691285979953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27963499828913127523986635 41945249743369691285979953)
    ·
      refine ⟨31458937307527268464484965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41945249743369691285979953 31458937307527268464484965)
      ·
        refine ⟨5898550745161362837090931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31458937307527268464484965 5898550745161362837090931)
        ·
          refine ⟨8847826117742044255636397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5898550745161362837090931 8847826117742044255636397)
          ·
            refine ⟨3317934794153266595863649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8847826117742044255636397 3317934794153266595863649)
            ·
              refine ⟨2488451095614949946897737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3317934794153266595863649 2488451095614949946897737)
              ·
                refine ⟨1866338321711212460173303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2488451095614949946897737 1866338321711212460173303)
                ·
                  refine ⟨2799507482566818690259955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866338321711212460173303 2799507482566818690259955)
                  ·
                    refine ⟨4199261223850228035389933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2799507482566818690259955 4199261223850228035389933)
                    ·
                      refine ⟨1574722958943835513271225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4199261223850228035389933 1574722958943835513271225)
                      ·
                        rfl

theorem cell23_3066762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_3066762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066762 prefixEnd_3066762 := by exact prefixLift 3066762
  have htrace : WordTrace (prefixWord ++ tailWord_3066762) baseStart_3066762 baseEnd_3066762 := by
    simpa [prefixWord, tailWord_3066762, baseEnd_3066762] using wordTrace_append hprefix tailTrace_3066762
  have hstable : (prefixWord ++ tailWord_3066762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066762).length < 2 ^ (prefixWord ++ tailWord_3066762).sum := by decide
  have hdescent : baseEnd_3066762 < baseStart_3066762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066784 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 3]
def baseStart_3066784 : Nat := 118140960795 + 3066784 * 2 ^ 59
def prefixEnd_3066784 : Nat := 4983230072969 + 3 ^ 40 * 3066784 * 2
def baseEnd_3066784 : Nat := 1574734255518234427196123

theorem tailTrace_3066784 : CollatzResearch.WordTrace tailWord_3066784 prefixEnd_3066784 1574734255518234427196123 := by
  unfold tailWord_3066784
  simp only [CollatzResearch.WordTrace]
  refine ⟨55927400860786403926623703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74569867814381871902164937 55927400860786403926623703)
  ·
    refine ⟨83891101291179605889935555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55927400860786403926623703 83891101291179605889935555)
    ·
      refine ⟨125836651936769408834903333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83891101291179605889935555 125836651936769408834903333)
      ·
        refine ⟨23594372238144264156544375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125836651936769408834903333 23594372238144264156544375)
        ·
          refine ⟨35391558357216396234816563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23594372238144264156544375 35391558357216396234816563)
          ·
            refine ⟨53087337535824594352224845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35391558357216396234816563 53087337535824594352224845)
            ·
              refine ⟨19907751575934222882084317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53087337535824594352224845 19907751575934222882084317)
              ·
                refine ⟨7465406840975333580781619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19907751575934222882084317 7465406840975333580781619)
                ·
                  refine ⟨11198110261463000371172429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7465406840975333580781619 11198110261463000371172429)
                  ·
                    refine ⟨4199291348048625139189661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11198110261463000371172429 4199291348048625139189661)
                    ·
                      refine ⟨1574734255518234427196123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4199291348048625139189661 1574734255518234427196123)
                      ·
                        rfl

theorem cell23_3066784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_3066784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066784 prefixEnd_3066784 := by exact prefixLift 3066784
  have htrace : WordTrace (prefixWord ++ tailWord_3066784) baseStart_3066784 baseEnd_3066784 := by
    simpa [prefixWord, tailWord_3066784, baseEnd_3066784] using wordTrace_append hprefix tailTrace_3066784
  have hstable : (prefixWord ++ tailWord_3066784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066784).length < 2 ^ (prefixWord ++ tailWord_3066784).sum := by decide
  have hdescent : baseEnd_3066784 < baseStart_3066784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066791 : List Nat := [1, 1, 6, 1, 3, 1, 3, 7]
def baseStart_3066791 : Nat := 118140960795 + 3066791 * 2 ^ 59
def prefixEnd_3066791 : Nat := 4983230072969 + 3 ^ 40 * 3066791 * 2
def baseEnd_3066791 : Nat := 58323624069733922215133

theorem tailTrace_3066791 : CollatzResearch.WordTrace tailWord_3066791 prefixEnd_3066791 58323624069733922215133 := by
  unfold tailWord_3066791
  simp only [CollatzResearch.WordTrace]
  refine ⟨111855057032547448048752227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74570038021698298699168151 111855057032547448048752227)
  ·
    refine ⟨167782585548821172073128341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111855057032547448048752227 167782585548821172073128341)
    ·
      refine ⟨7864808697600992440927891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 167782585548821172073128341 7864808697600992440927891)
      ·
        refine ⟨11797213046401488661391837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7864808697600992440927891 11797213046401488661391837)
        ·
          refine ⟨4423954892400558248021939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11797213046401488661391837 4423954892400558248021939)
          ·
            refine ⟨6635932338600837372032909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423954892400558248021939 6635932338600837372032909)
            ·
              refine ⟨2488474626975314014512341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6635932338600837372032909 2488474626975314014512341)
              ·
                refine ⟨58323624069733922215133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2488474626975314014512341 58323624069733922215133)
                ·
                  rfl

theorem cell23_3066791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 7].length) (baseStart_3066791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066791 prefixEnd_3066791 := by exact prefixLift 3066791
  have htrace : WordTrace (prefixWord ++ tailWord_3066791) baseStart_3066791 baseEnd_3066791 := by
    simpa [prefixWord, tailWord_3066791, baseEnd_3066791] using wordTrace_append hprefix tailTrace_3066791
  have hstable : (prefixWord ++ tailWord_3066791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066791).length < 2 ^ (prefixWord ++ tailWord_3066791).sum := by decide
  have hdescent : baseEnd_3066791 < baseStart_3066791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066822 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3066822 : Nat := 118140960795 + 3066822 * 2 ^ 59
def prefixEnd_3066822 : Nat := 4983230072969 + 3 ^ 40 * 3066822 * 2
def baseEnd_3066822 : Nat := 1574753767783105278520949

theorem tailTrace_3066822 : CollatzResearch.WordTrace tailWord_3066822 prefixEnd_3066822 1574753767783105278520949 := by
  unfold tailWord_3066822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495505865482348135722835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74570791796956760228753813 3495505865482348135722835)
  ·
    refine ⟨5243258798223522203584253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3495505865482348135722835 5243258798223522203584253)
    ·
      refine ⟨1966222049333820826344095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5243258798223522203584253 1966222049333820826344095)
      ·
        refine ⟨2949333074000731239516143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1966222049333820826344095 2949333074000731239516143)
        ·
          refine ⟨4423999611001096859274215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2949333074000731239516143 4423999611001096859274215)
          ·
            refine ⟨6635999416501645288911323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423999611001096859274215 6635999416501645288911323)
            ·
              refine ⟨9953999124752467933366985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6635999416501645288911323 9953999124752467933366985)
              ·
                refine ⟨7465499343564350950025239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9953999124752467933366985 7465499343564350950025239)
                ·
                  refine ⟨11198249015346526425037859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7465499343564350950025239 11198249015346526425037859)
                  ·
                    refine ⟨16797373523019789637556789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11198249015346526425037859 16797373523019789637556789)
                    ·
                      refine ⟨1574753767783105278520949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16797373523019789637556789 1574753767783105278520949)
                      ·
                        rfl

theorem cell23_3066822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3066822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066822 prefixEnd_3066822 := by exact prefixLift 3066822
  have htrace : WordTrace (prefixWord ++ tailWord_3066822) baseStart_3066822 baseEnd_3066822 := by
    simpa [prefixWord, tailWord_3066822, baseEnd_3066822] using wordTrace_append hprefix tailTrace_3066822
  have hstable : (prefixWord ++ tailWord_3066822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066822).length < 2 ^ (prefixWord ++ tailWord_3066822).sum := by decide
  have hdescent : baseEnd_3066822 < baseStart_3066822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066829 : List Nat := [1, 6, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3066829 : Nat := 118140960795 + 3066829 * 2 ^ 59
def prefixEnd_3066829 : Nat := 4983230072969 + 3 ^ 40 * 3066829 * 2
def baseEnd_3066829 : Nat := 524919120715895583711139

theorem tailTrace_3066829 : CollatzResearch.WordTrace tailWord_3066829 prefixEnd_3066829 524919120715895583711139 := by
  unfold tailWord_3066829
  simp only [CollatzResearch.WordTrace]
  refine ⟨111856443006409780538635541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74570962004273187025757027 111856443006409780538635541)
  ·
    refine ⟨5243270765925458462748541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111856443006409780538635541 5243270765925458462748541)
    ·
      refine ⟨1966226537222046923530703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5243270765925458462748541 1966226537222046923530703)
      ·
        refine ⟨2949339805833070385296055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1966226537222046923530703 2949339805833070385296055)
        ·
          refine ⟨4424009708749605577944083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2949339805833070385296055 4424009708749605577944083)
          ·
            refine ⟨6636014563124408366916125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4424009708749605577944083 6636014563124408366916125)
            ·
              refine ⟨2488505461171653137593547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6636014563124408366916125 2488505461171653137593547)
              ·
                refine ⟨3732758191757479706390321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2488505461171653137593547 3732758191757479706390321)
                ·
                  refine ⟨2799568643818109779792741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3732758191757479706390321 2799568643818109779792741)
                  ·
                    refine ⟨524919120715895583711139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2799568643818109779792741 524919120715895583711139)
                    ·
                      rfl

theorem cell23_3066829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3066829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066829 prefixEnd_3066829 := by exact prefixLift 3066829
  have htrace : WordTrace (prefixWord ++ tailWord_3066829) baseStart_3066829 baseEnd_3066829 := by
    simpa [prefixWord, tailWord_3066829, baseEnd_3066829] using wordTrace_append hprefix tailTrace_3066829
  have hstable : (prefixWord ++ tailWord_3066829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066829).length < 2 ^ (prefixWord ++ tailWord_3066829).sum := by decide
  have hdescent : baseEnd_3066829 < baseStart_3066829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066845 : List Nat := [1, 4, 3, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_3066845 : Nat := 118140960795 + 3066845 * 2 ^ 59
def prefixEnd_3066845 : Nat := 4983230072969 + 3 ^ 40 * 3066845 * 2
def baseEnd_3066845 : Nat := 1574765577838158688533343

theorem tailTrace_3066845 : CollatzResearch.WordTrace tailWord_3066845 prefixEnd_3066845 1574765577838158688533343 := by
  unfold tailWord_3066845
  simp only [CollatzResearch.WordTrace]
  refine ⟨111857026574351815271217989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74571351049567876847478659 111857026574351815271217989)
  ·
    refine ⟨20973192482690965363353373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111857026574351815271217989 20973192482690965363353373)
    ·
      refine ⟨7864947181009112011257515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20973192482690965363353373 7864947181009112011257515)
      ·
        refine ⟨11797420771513668016886273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7864947181009112011257515 11797420771513668016886273)
        ·
          refine ⟨8848065578635251012664705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11797420771513668016886273 8848065578635251012664705)
          ·
            refine ⟨6636049183976438259498529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8848065578635251012664705 6636049183976438259498529)
            ·
              refine ⟨4977036887982328694623897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6636049183976438259498529 4977036887982328694623897)
              ·
                refine ⟨3732777665986746520967923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4977036887982328694623897 3732777665986746520967923)
                ·
                  refine ⟨5599166498980119781451885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3732777665986746520967923 5599166498980119781451885)
                  ·
                    refine ⟨2099687437117544918044457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5599166498980119781451885 2099687437117544918044457)
                    ·
                      refine ⟨1574765577838158688533343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099687437117544918044457 1574765577838158688533343)
                      ·
                        rfl

theorem cell23_3066845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_3066845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066845 prefixEnd_3066845 := by exact prefixLift 3066845
  have htrace : WordTrace (prefixWord ++ tailWord_3066845) baseStart_3066845 baseEnd_3066845 := by
    simpa [prefixWord, tailWord_3066845, baseEnd_3066845] using wordTrace_append hprefix tailTrace_3066845
  have hstable : (prefixWord ++ tailWord_3066845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066845).length < 2 ^ (prefixWord ++ tailWord_3066845).sum := by decide
  have hdescent : baseEnd_3066845 < baseStart_3066845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066858 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_3066858 : Nat := 118140960795 + 3066858 * 2 ^ 59
def prefixEnd_3066858 : Nat := 4983230072969 + 3 ^ 40 * 3066858 * 2
def baseEnd_3066858 : Nat := 1574772253086667137670783

theorem tailTrace_3066858 : CollatzResearch.WordTrace tailWord_3066858 prefixEnd_3066858 1574772253086667137670783 := by
  unfold tailWord_3066858
  simp only [CollatzResearch.WordTrace]
  refine ⟨27964375180826179622860307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74571667148869812327627485 27964375180826179622860307)
  ·
    refine ⟨41946562771239269434290461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27964375180826179622860307 41946562771239269434290461)
    ·
      refine ⟨15729961039214726037858923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41946562771239269434290461 15729961039214726037858923)
      ·
        refine ⟨23594941558822089056788385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15729961039214726037858923 23594941558822089056788385)
        ·
          refine ⟨17696206169116566792591289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23594941558822089056788385 17696206169116566792591289)
          ·
            refine ⟨13272154626837425094443467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17696206169116566792591289 13272154626837425094443467)
            ·
              refine ⟨19908231940256137641665201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13272154626837425094443467 19908231940256137641665201)
              ·
                refine ⟨14931173955192103231248901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19908231940256137641665201 14931173955192103231248901)
                ·
                  refine ⟨2799595116598519355859169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14931173955192103231248901 2799595116598519355859169)
                  ·
                    refine ⟨2099696337448889516894377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2799595116598519355859169 2099696337448889516894377)
                    ·
                      refine ⟨1574772253086667137670783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099696337448889516894377 1574772253086667137670783)
                      ·
                        rfl

theorem cell23_3066858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_3066858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066858 prefixEnd_3066858 := by exact prefixLift 3066858
  have htrace : WordTrace (prefixWord ++ tailWord_3066858) baseStart_3066858 baseEnd_3066858 := by
    simpa [prefixWord, tailWord_3066858, baseEnd_3066858] using wordTrace_append hprefix tailTrace_3066858
  have hstable : (prefixWord ++ tailWord_3066858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066858).length < 2 ^ (prefixWord ++ tailWord_3066858).sum := by decide
  have hdescent : baseEnd_3066858 < baseStart_3066858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066867 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 6]
def baseStart_3066867 : Nat := 118140960795 + 3066867 * 2 ^ 59
def prefixEnd_3066867 : Nat := 4983230072969 + 3 ^ 40 * 3066867 * 2
def baseEnd_3066867 : Nat := 1574776874412557602458241

theorem tailTrace_3066867 : CollatzResearch.WordTrace tailWord_3066867 prefixEnd_3066867 1574776874412557602458241 := by
  unfold tailWord_3066867
  simp only [CollatzResearch.WordTrace]
  refine ⟨111857828980272113028518855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74571885986848075352345903 111857828980272113028518855)
  ·
    refine ⟨167786743470408169542778283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111857828980272113028518855 167786743470408169542778283)
    ·
      refine ⟨251680115205612254314167425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167786743470408169542778283 251680115205612254314167425)
      ·
        refine ⟨188760086404209190735625569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251680115205612254314167425 188760086404209190735625569)
        ·
          refine ⟨141570064803156893051719177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188760086404209190735625569 141570064803156893051719177)
          ·
            refine ⟨106177548602367669788789383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141570064803156893051719177 106177548602367669788789383)
            ·
              refine ⟨159266322903551504683184075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106177548602367669788789383 159266322903551504683184075)
              ·
                refine ⟨238899484355327257024776113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159266322903551504683184075 238899484355327257024776113)
                ·
                  refine ⟨179174613266495442768582085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238899484355327257024776113 179174613266495442768582085)
                  ·
                    refine ⟨33595239987467895519109141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179174613266495442768582085 33595239987467895519109141)
                    ·
                      refine ⟨1574776874412557602458241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33595239987467895519109141 1574776874412557602458241)
                      ·
                        rfl

theorem cell23_3066867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_3066867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066867 prefixEnd_3066867 := by exact prefixLift 3066867
  have htrace : WordTrace (prefixWord ++ tailWord_3066867) baseStart_3066867 baseEnd_3066867 := by
    simpa [prefixWord, tailWord_3066867, baseEnd_3066867] using wordTrace_append hprefix tailTrace_3066867
  have hstable : (prefixWord ++ tailWord_3066867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066867).length < 2 ^ (prefixWord ++ tailWord_3066867).sum := by decide
  have hdescent : baseEnd_3066867 < baseStart_3066867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066874 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3]
def baseStart_3066874 : Nat := 118140960795 + 3066874 * 2 ^ 59
def prefixEnd_3066874 : Nat := 4983230072969 + 3 ^ 40 * 3066874 * 2
def baseEnd_3066874 : Nat := 1574780468777139075070709

theorem tailTrace_3066874 : CollatzResearch.WordTrace tailWord_3066874 prefixEnd_3066874 1574780468777139075070709 := by
  unfold tailWord_3066874
  simp only [CollatzResearch.WordTrace]
  refine ⟨27964521072811688306005919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74572056194164502149349117 27964521072811688306005919)
  ·
    refine ⟨41946781609217532459008879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27964521072811688306005919 41946781609217532459008879)
    ·
      refine ⟨62920172413826298688513319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41946781609217532459008879 62920172413826298688513319)
      ·
        refine ⟨94380258620739448032769979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62920172413826298688513319 94380258620739448032769979)
        ·
          refine ⟨141570387931109172049154969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94380258620739448032769979 141570387931109172049154969)
          ·
            refine ⟨106177790948331879036866227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141570387931109172049154969 106177790948331879036866227)
            ·
              refine ⟨159266686422497818555299341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106177790948331879036866227 159266686422497818555299341)
              ·
                refine ⟨59725007408436681958237253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159266686422497818555299341 59725007408436681958237253)
                ·
                  refine ⟨11198438889081877867169485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59725007408436681958237253 11198438889081877867169485)
                  ·
                    refine ⟨4199414583405704200188557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11198438889081877867169485 4199414583405704200188557)
                    ·
                      refine ⟨1574780468777139075070709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4199414583405704200188557 1574780468777139075070709)
                      ·
                        rfl

theorem cell23_3066874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_3066874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066874 prefixEnd_3066874 := by exact prefixLift 3066874
  have htrace : WordTrace (prefixWord ++ tailWord_3066874) baseStart_3066874 baseEnd_3066874 := by
    simpa [prefixWord, tailWord_3066874, baseEnd_3066874] using wordTrace_append hprefix tailTrace_3066874
  have hstable : (prefixWord ++ tailWord_3066874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066874).length < 2 ^ (prefixWord ++ tailWord_3066874).sum := by decide
  have hdescent : baseEnd_3066874 < baseStart_3066874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066881 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 7]
def baseStart_3066881 : Nat := 118140960795 + 3066881 * 2 ^ 59
def prefixEnd_3066881 : Nat := 4983230072969 + 3 ^ 40 * 3066881 * 2
def baseEnd_3066881 : Nat := 174976007015746727520353

theorem tailTrace_3066881 : CollatzResearch.WordTrace tailWord_3066881 prefixEnd_3066881 174976007015746727520353 := by
  unfold tailWord_3066881
  simp only [CollatzResearch.WordTrace]
  refine ⟨111858339602221393419528497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74572226401480928946352331 111858339602221393419528497)
  ·
    refine ⟨83893754701666045064646373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111858339602221393419528497 83893754701666045064646373)
    ·
      refine ⟨15730079006562383449621195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83893754701666045064646373 15730079006562383449621195)
      ·
        refine ⟨23595118509843575174431793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15730079006562383449621195 23595118509843575174431793)
        ·
          refine ⟨17696338882382681380823845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23595118509843575174431793 17696338882382681380823845)
          ·
            refine ⟨3318063540446752758904471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17696338882382681380823845 3318063540446752758904471)
            ·
              refine ⟨4977095310670129138356707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3318063540446752758904471 4977095310670129138356707)
              ·
                refine ⟨7465642966005193707535061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4977095310670129138356707 7465642966005193707535061)
                ·
                  refine ⟨174976007015746727520353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7465642966005193707535061 174976007015746727520353)
                  ·
                    rfl

theorem cell23_3066881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 7].length) (baseStart_3066881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066881 prefixEnd_3066881 := by exact prefixLift 3066881
  have htrace : WordTrace (prefixWord ++ tailWord_3066881) baseStart_3066881 baseEnd_3066881 := by
    simpa [prefixWord, tailWord_3066881, baseEnd_3066881] using wordTrace_append hprefix tailTrace_3066881
  have hstable : (prefixWord ++ tailWord_3066881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066881).length < 2 ^ (prefixWord ++ tailWord_3066881).sum := by decide
  have hdescent : baseEnd_3066881 < baseStart_3066881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066892 : List Nat := [2, 2, 1, 2, 3, 4, 2, 1, 2, 2, 2]
def baseStart_3066892 : Nat := 118140960795 + 3066892 * 2 ^ 59
def prefixEnd_3066892 : Nat := 4983230072969 + 3 ^ 40 * 3066892 * 2
def baseEnd_3066892 : Nat := 1574789711428920004645627

theorem tailTrace_3066892 : CollatzResearch.WordTrace tailWord_3066892 prefixEnd_3066892 1574789711428920004645627 := by
  unfold tailWord_3066892
  simp only [CollatzResearch.WordTrace]
  refine ⟨55929370402590771149089465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74572493870121028198785953 55929370402590771149089465)
  ·
    refine ⟨41947027801943078361817099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55929370402590771149089465 41947027801943078361817099)
    ·
      refine ⟨62920541702914617542725649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41947027801943078361817099 62920541702914617542725649)
      ·
        refine ⟨47190406277185963157044237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62920541702914617542725649 47190406277185963157044237)
        ·
          refine ⟨17696402353944736183891589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47190406277185963157044237 17696402353944736183891589)
          ·
            refine ⟨3318075441364638034479673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17696402353944736183891589 3318075441364638034479673)
            ·
              refine ⟨2488556581023478525859755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3318075441364638034479673 2488556581023478525859755)
              ·
                refine ⟨3732834871535217788789633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2488556581023478525859755 3732834871535217788789633)
                ·
                  refine ⟨2799626153651413341592225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3732834871535217788789633 2799626153651413341592225)
                  ·
                    refine ⟨2099719615238560006194169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2799626153651413341592225 2099719615238560006194169)
                    ·
                      refine ⟨1574789711428920004645627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099719615238560006194169 1574789711428920004645627)
                      ·
                        rfl

theorem cell23_3066892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_3066892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066892 prefixEnd_3066892 := by exact prefixLift 3066892
  have htrace : WordTrace (prefixWord ++ tailWord_3066892) baseStart_3066892 baseEnd_3066892 := by
    simpa [prefixWord, tailWord_3066892, baseEnd_3066892] using wordTrace_append hprefix tailTrace_3066892
  have hstable : (prefixWord ++ tailWord_3066892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066892).length < 2 ^ (prefixWord ++ tailWord_3066892).sum := by decide
  have hdescent : baseEnd_3066892 < baseStart_3066892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066911 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 2, 5]
def baseStart_3066911 : Nat := 118140960795 + 3066911 * 2 ^ 59
def prefixEnd_3066911 : Nat := 4983230072969 + 3 ^ 40 * 3066911 * 2
def baseEnd_3066911 : Nat := 524933155853785143436013

theorem tailTrace_3066911 : CollatzResearch.WordTrace tailWord_3066911 prefixEnd_3066911 524933155853785143436013 := by
  unfold tailWord_3066911
  simp only [CollatzResearch.WordTrace]
  refine ⟨111859433792112708543120587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74572955861408472362080391 111859433792112708543120587)
  ·
    refine ⟨167789150688169062814680881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111859433792112708543120587 167789150688169062814680881)
    ·
      refine ⟨125841863016126797111010661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167789150688169062814680881 125841863016126797111010661)
      ·
        refine ⟨23595349315523774458314499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125841863016126797111010661 23595349315523774458314499)
        ·
          refine ⟨35393023973285661687471749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23595349315523774458314499 35393023973285661687471749)
          ·
            refine ⟨6636191994991061566400953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35393023973285661687471749 6636191994991061566400953)
            ·
              refine ⟨4977143996243296174800715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6636191994991061566400953 4977143996243296174800715)
              ·
                refine ⟨7465715994364944262201073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4977143996243296174800715 7465715994364944262201073)
                ·
                  refine ⟨5599286995773708196650805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7465715994364944262201073 5599286995773708196650805)
                  ·
                    refine ⟨524933155853785143436013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5599286995773708196650805 524933155853785143436013)
                    ·
                      rfl

theorem cell23_3066911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 5].length) (baseStart_3066911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066911 prefixEnd_3066911 := by exact prefixLift 3066911
  have htrace : WordTrace (prefixWord ++ tailWord_3066911) baseStart_3066911 baseEnd_3066911 := by
    simpa [prefixWord, tailWord_3066911, baseEnd_3066911] using wordTrace_append hprefix tailTrace_3066911
  have hstable : (prefixWord ++ tailWord_3066911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066911).length < 2 ^ (prefixWord ++ tailWord_3066911).sum := by decide
  have hdescent : baseEnd_3066911 < baseStart_3066911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066931 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 2, 4, 2]
def baseStart_3066931 : Nat := 118140960795 + 3066931 * 2 ^ 59
def prefixEnd_3066931 : Nat := 4983230072969 + 3 ^ 40 * 3066931 * 2
def baseEnd_3066931 : Nat := 1574809737174445352057947

theorem tailTrace_3066931 : CollatzResearch.WordTrace tailWord_3066931 prefixEnd_3066931 1574809737174445352057947 := by
  unfold tailWord_3066931
  simp only [CollatzResearch.WordTrace]
  refine ⟨111860163252040251958848647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74573442168026834639232431 111860163252040251958848647)
  ·
    refine ⟨167790244878060377938272971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111860163252040251958848647 167790244878060377938272971)
    ·
      refine ⟨251685367317090566907409457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167790244878060377938272971 251685367317090566907409457)
      ·
        refine ⟨188764025487817925180557093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251685367317090566907409457 188764025487817925180557093)
        ·
          refine ⟨35393254778965860971354455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188764025487817925180557093 35393254778965860971354455)
          ·
            refine ⟨53089882168448791457031683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35393254778965860971354455 53089882168448791457031683)
            ·
              refine ⟨79634823252673187185547525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53089882168448791457031683 79634823252673187185547525)
              ·
                refine ⟨14931529359876222597290161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79634823252673187185547525 14931529359876222597290161)
                ·
                  refine ⟨11198647019907166947967621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14931529359876222597290161 11198647019907166947967621)
                  ·
                    refine ⟨2099746316232593802743929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11198647019907166947967621 2099746316232593802743929)
                    ·
                      refine ⟨1574809737174445352057947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099746316232593802743929 1574809737174445352057947)
                      ·
                        rfl

theorem cell23_3066931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 4, 2].length) (baseStart_3066931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066931 prefixEnd_3066931 := by exact prefixLift 3066931
  have htrace : WordTrace (prefixWord ++ tailWord_3066931) baseStart_3066931 baseEnd_3066931 := by
    simpa [prefixWord, tailWord_3066931, baseEnd_3066931] using wordTrace_append hprefix tailTrace_3066931
  have hstable : (prefixWord ++ tailWord_3066931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066931).length < 2 ^ (prefixWord ++ tailWord_3066931).sum := by decide
  have hdescent : baseEnd_3066931 < baseStart_3066931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3066932 : List Nat := [2, 5, 1, 2, 1, 3, 2, 2, 5]
def baseStart_3066932 : Nat := 118140960795 + 3066932 * 2 ^ 59
def prefixEnd_3066932 : Nat := 4983230072969 + 3 ^ 40 * 3066932 * 2
def baseEnd_3066932 : Nat := 174978916739455538682827

theorem tailTrace_3066932 : CollatzResearch.WordTrace tailWord_3066932 prefixEnd_3066932 174978916739455538682827 := by
  unfold tailWord_3066932
  simp only [CollatzResearch.WordTrace]
  refine ⟨55930099862518314564817525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74573466483357752753090033 55930099862518314564817525)
  ·
    refine ⟨5243446862111091990451643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55930099862518314564817525 5243446862111091990451643)
    ·
      refine ⟨7865170293166637985677465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5243446862111091990451643 7865170293166637985677465)
      ·
        refine ⟨5898877719874978489258099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7865170293166637985677465 5898877719874978489258099)
        ·
          refine ⟨8848316579812467733887149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5898877719874978489258099 8848316579812467733887149)
          ·
            refine ⟨3318118717429675400207681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8848316579812467733887149 3318118717429675400207681)
            ·
              refine ⟨2488589038072256550155761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3318118717429675400207681 2488589038072256550155761)
              ·
                refine ⟨1866441778554192412616821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2488589038072256550155761 1866441778554192412616821)
                ·
                  refine ⟨174978916739455538682827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1866441778554192412616821 174978916739455538682827)
                  ·
                    rfl

theorem cell23_3066932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_3066932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3066932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3066932 prefixEnd_3066932 := by exact prefixLift 3066932
  have htrace : WordTrace (prefixWord ++ tailWord_3066932) baseStart_3066932 baseEnd_3066932 := by
    simpa [prefixWord, tailWord_3066932, baseEnd_3066932] using wordTrace_append hprefix tailTrace_3066932
  have hstable : (prefixWord ++ tailWord_3066932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3066932).length < 2 ^ (prefixWord ++ tailWord_3066932).sum := by decide
  have hdescent : baseEnd_3066932 < baseStart_3066932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3066932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067018 : List Nat := [3, 1, 2, 3, 1, 1, 4, 2, 1, 5]
def baseStart_3067018 : Nat := 118140960795 + 3067018 * 2 ^ 59
def prefixEnd_3067018 : Nat := 4983230072969 + 3 ^ 40 * 3067018 * 2
def baseEnd_3067018 : Nat := 524951469997128837223349

theorem tailTrace_3067018 : CollatzResearch.WordTrace tailWord_3067018 prefixEnd_3067018 524951469997128837223349 := by
  unfold tailWord_3067018
  simp only [CollatzResearch.WordTrace]
  refine ⟨27965834100681266454316427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74575557601816710544843805 27965834100681266454316427)
  ·
    refine ⟨41948751151021899681474641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27965834100681266454316427 41948751151021899681474641)
    ·
      refine ⟨31461563363266424761105981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41948751151021899681474641 31461563363266424761105981)
      ·
        refine ⟨11798086261224909285414743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31461563363266424761105981 11798086261224909285414743)
        ·
          refine ⟨17697129391837363928122115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11798086261224909285414743 17697129391837363928122115)
          ·
            refine ⟨26545694087756045892183173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17697129391837363928122115 26545694087756045892183173)
            ·
              refine ⟨4977317641454258604784345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26545694087756045892183173 4977317641454258604784345)
              ·
                refine ⟨3732988231090693953588259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4977317641454258604784345 3732988231090693953588259)
                ·
                  refine ⟨5599482346636040930382389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3732988231090693953588259 5599482346636040930382389)
                  ·
                    refine ⟨524951469997128837223349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5599482346636040930382389 524951469997128837223349)
                    ·
                      rfl

theorem cell23_3067018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_3067018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067018 prefixEnd_3067018 := by exact prefixLift 3067018
  have htrace : WordTrace (prefixWord ++ tailWord_3067018) baseStart_3067018 baseEnd_3067018 := by
    simpa [prefixWord, tailWord_3067018, baseEnd_3067018] using wordTrace_append hprefix tailTrace_3067018
  have hstable : (prefixWord ++ tailWord_3067018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067018).length < 2 ^ (prefixWord ++ tailWord_3067018).sum := by decide
  have hdescent : baseEnd_3067018 < baseStart_3067018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067032 : List Nat := [2, 1, 2, 4, 2, 1, 3, 3, 1, 1, 3]
def baseStart_3067032 : Nat := 118140960795 + 3067032 * 2 ^ 59
def prefixEnd_3067032 : Nat := 4983230072969 + 3 ^ 40 * 3067032 * 2
def baseEnd_3067032 : Nat := 1574861598720549456894983

theorem tailTrace_3067032 : CollatzResearch.WordTrace tailWord_3067032 prefixEnd_3067032 1574861598720549456894983 := by
  unfold tailWord_3067032
  simp only [CollatzResearch.WordTrace]
  refine ⟨55931923512337173104137675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74575898016449564138850233 55931923512337173104137675)
  ·
    refine ⟨83897885268505759656206513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55931923512337173104137675 83897885268505759656206513)
    ·
      refine ⟨62923413951379319742154885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83897885268505759656206513 62923413951379319742154885)
      ·
        refine ⟨11798140115883622451654041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62923413951379319742154885 11798140115883622451654041)
        ·
          refine ⟨8848605086912716838740531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11798140115883622451654041 8848605086912716838740531)
          ·
            refine ⟨13272907630369075258110797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8848605086912716838740531 13272907630369075258110797)
            ·
              refine ⟨4977340361388403221791549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13272907630369075258110797 4977340361388403221791549)
              ·
                refine ⟨1866502635520651208171831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4977340361388403221791549 1866502635520651208171831)
                ·
                  refine ⟨2799753953280976812257747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866502635520651208171831 2799753953280976812257747)
                  ·
                    refine ⟨4199630929921465218386621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2799753953280976812257747 4199630929921465218386621)
                    ·
                      refine ⟨1574861598720549456894983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4199630929921465218386621 1574861598720549456894983)
                      ·
                        rfl

theorem cell23_3067032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_3067032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067032 prefixEnd_3067032 := by exact prefixLift 3067032
  have htrace : WordTrace (prefixWord ++ tailWord_3067032) baseStart_3067032 baseEnd_3067032 := by
    simpa [prefixWord, tailWord_3067032, baseEnd_3067032] using wordTrace_append hprefix tailTrace_3067032
  have hstable : (prefixWord ++ tailWord_3067032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067032).length < 2 ^ (prefixWord ++ tailWord_3067032).sum := by decide
  have hdescent : baseEnd_3067032 < baseStart_3067032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067042 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_3067042 : Nat := 118140960795 + 3067042 * 2 ^ 59
def prefixEnd_3067042 : Nat := 4983230072969 + 3 ^ 40 * 3067042 * 2
def baseEnd_3067042 : Nat := 1574866733527094417769937

theorem tailTrace_3067042 : CollatzResearch.WordTrace tailWord_3067042 prefixEnd_3067042 1574866733527094417769937 := by
  unfold tailWord_3067042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27966052938659529479034845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74576141169758745277426253 27966052938659529479034845)
  ·
    refine ⟨10487269851997323554638067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27966052938659529479034845 10487269851997323554638067)
    ·
      refine ⟨15730904777995985331957101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10487269851997323554638067 15730904777995985331957101)
      ·
        refine ⟨5899089291748494499483913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15730904777995985331957101 5899089291748494499483913)
        ·
          refine ⟨4424316968811370874612935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5899089291748494499483913 4424316968811370874612935)
          ·
            refine ⟨6636475453217056311919403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4424316968811370874612935 6636475453217056311919403)
            ·
              refine ⟨9954713179825584467879105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6636475453217056311919403 9954713179825584467879105)
              ·
                refine ⟨7466034884869188350909329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9954713179825584467879105 7466034884869188350909329)
                ·
                  refine ⟨5599526163651891263181997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7466034884869188350909329 5599526163651891263181997)
                  ·
                    refine ⟨2099822311369459223693249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5599526163651891263181997 2099822311369459223693249)
                    ·
                      refine ⟨1574866733527094417769937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099822311369459223693249 1574866733527094417769937)
                      ·
                        rfl

theorem cell23_3067042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_3067042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067042 prefixEnd_3067042 := by exact prefixLift 3067042
  have htrace : WordTrace (prefixWord ++ tailWord_3067042) baseStart_3067042 baseEnd_3067042 := by
    simpa [prefixWord, tailWord_3067042, baseEnd_3067042] using wordTrace_append hprefix tailTrace_3067042
  have hstable : (prefixWord ++ tailWord_3067042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067042).length < 2 ^ (prefixWord ++ tailWord_3067042).sum := by decide
  have hdescent : baseEnd_3067042 < baseStart_3067042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067055 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 3, 2, 2]
def baseStart_3067055 : Nat := 118140960795 + 3067055 * 2 ^ 59
def prefixEnd_3067055 : Nat := 4983230072969 + 3 ^ 40 * 3067055 * 2
def baseEnd_3067055 : Nat := 1574873408775602866907377

theorem tailTrace_3067055 : CollatzResearch.WordTrace tailWord_3067055 prefixEnd_3067055 1574873408775602866907377 := by
  unfold tailWord_3067055
  simp only [CollatzResearch.WordTrace]
  refine ⟨111864685903591021136362619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74576457269060680757575079 111864685903591021136362619)
  ·
    refine ⟨167797028855386531704543929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111864685903591021136362619 167797028855386531704543929)
    ·
      refine ⟨125847771641539898778407947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167797028855386531704543929 125847771641539898778407947)
      ·
        refine ⟨188771657462309848167611921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125847771641539898778407947 188771657462309848167611921)
        ·
          refine ⟨141578743096732386125708941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188771657462309848167611921 141578743096732386125708941)
          ·
            refine ⟨53092028661274644797140853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141578743096732386125708941 53092028661274644797140853)
            ·
              refine ⟨4977377686994497949731955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53092028661274644797140853 4977377686994497949731955)
              ·
                refine ⟨7466066530491746924597933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4977377686994497949731955 7466066530491746924597933)
                ·
                  refine ⟨2799774948934405096724225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7466066530491746924597933 2799774948934405096724225)
                  ·
                    refine ⟨2099831211700803822543169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2799774948934405096724225 2099831211700803822543169)
                    ·
                      refine ⟨1574873408775602866907377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099831211700803822543169 1574873408775602866907377)
                      ·
                        rfl

theorem cell23_3067055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 2, 2].length) (baseStart_3067055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067055 prefixEnd_3067055 := by exact prefixLift 3067055
  have htrace : WordTrace (prefixWord ++ tailWord_3067055) baseStart_3067055 baseEnd_3067055 := by
    simpa [prefixWord, tailWord_3067055, baseEnd_3067055] using wordTrace_append hprefix tailTrace_3067055
  have hstable : (prefixWord ++ tailWord_3067055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067055).length < 2 ^ (prefixWord ++ tailWord_3067055).sum := by decide
  have hdescent : baseEnd_3067055 < baseStart_3067055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067065 : List Nat := [1, 2, 1, 4, 1, 3, 4, 1, 2, 4]
def baseStart_3067065 : Nat := 118140960795 + 3067065 * 2 ^ 59
def prefixEnd_3067065 : Nat := 4983230072969 + 3 ^ 40 * 3067065 * 2
def baseEnd_3067065 : Nat := 524959514527382609260777

theorem tailTrace_3067065 : CollatzResearch.WordTrace tailWord_3067065 prefixEnd_3067065 524959514527382609260777 := by
  unfold tailWord_3067065
  simp only [CollatzResearch.WordTrace]
  refine ⟨111865050633554792844226649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74576700422369861896151099 111865050633554792844226649)
  ·
    refine ⟨83898787975166094633169987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111865050633554792844226649 83898787975166094633169987)
    ·
      refine ⟨125848181962749141949754981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83898787975166094633169987 125848181962749141949754981)
      ·
        refine ⟨23596534118015464115579059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125848181962749141949754981 23596534118015464115579059)
        ·
          refine ⟨35394801177023196173368589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23596534118015464115579059 35394801177023196173368589)
          ·
            refine ⟨13273050441383698565013221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35394801177023196173368589 13273050441383698565013221)
            ·
              refine ⟨2488696957759443480939979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13273050441383698565013221 2488696957759443480939979)
              ·
                refine ⟨3733045436639165221409969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2488696957759443480939979 3733045436639165221409969)
                ·
                  refine ⟨2799784077479373916057477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3733045436639165221409969 2799784077479373916057477)
                  ·
                    refine ⟨524959514527382609260777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2799784077479373916057477 524959514527382609260777)
                    ·
                      rfl

theorem cell23_3067065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 2, 4].length) (baseStart_3067065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067065 prefixEnd_3067065 := by exact prefixLift 3067065
  have htrace : WordTrace (prefixWord ++ tailWord_3067065) baseStart_3067065 baseEnd_3067065 := by
    simpa [prefixWord, tailWord_3067065, baseEnd_3067065] using wordTrace_append hprefix tailTrace_3067065
  have hstable : (prefixWord ++ tailWord_3067065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067065).length < 2 ^ (prefixWord ++ tailWord_3067065).sum := by decide
  have hdescent : baseEnd_3067065 < baseStart_3067065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067072 : List Nat := [2, 1, 1, 2, 7, 1, 1, 2, 1, 1, 4]
def baseStart_3067072 : Nat := 118140960795 + 3067072 * 2 ^ 59
def prefixEnd_3067072 : Nat := 4983230072969 + 3 ^ 40 * 3067072 * 2
def baseEnd_3067072 : Nat := 1574882137946729300394799

theorem tailTrace_3067072 : CollatzResearch.WordTrace tailWord_3067072 prefixEnd_3067072 1574882137946729300394799 := by
  unfold tailWord_3067072
  simp only [CollatzResearch.WordTrace]
  refine ⟨55932652972264716519865735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74576870629686288693154313 55932652972264716519865735)
  ·
    refine ⟨83898979458397074779798603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55932652972264716519865735 83898979458397074779798603)
    ·
      refine ⟨125848469187595612169697905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83898979458397074779798603 125848469187595612169697905)
      ·
        refine ⟨94386351890696709127273429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125848469187595612169697905 94386351890696709127273429)
        ·
          refine ⟨2212180122438204120170471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 94386351890696709127273429 2212180122438204120170471)
          ·
            refine ⟨3318270183657306180255707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212180122438204120170471 3318270183657306180255707)
            ·
              refine ⟨4977405275485959270383561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3318270183657306180255707 4977405275485959270383561)
              ·
                refine ⟨3733053956614469452787671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4977405275485959270383561 3733053956614469452787671)
                ·
                  refine ⟨5599580934921704179181507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3733053956614469452787671 5599580934921704179181507)
                  ·
                    refine ⟨8399371402382556268772261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5599580934921704179181507 8399371402382556268772261)
                    ·
                      refine ⟨1574882137946729300394799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8399371402382556268772261 1574882137946729300394799)
                      ·
                        rfl

theorem cell23_3067072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 1, 1, 4].length) (baseStart_3067072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067072 prefixEnd_3067072 := by exact prefixLift 3067072
  have htrace : WordTrace (prefixWord ++ tailWord_3067072) baseStart_3067072 baseEnd_3067072 := by
    simpa [prefixWord, tailWord_3067072, baseEnd_3067072] using wordTrace_append hprefix tailTrace_3067072
  have hstable : (prefixWord ++ tailWord_3067072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067072).length < 2 ^ (prefixWord ++ tailWord_3067072).sum := by decide
  have hdescent : baseEnd_3067072 < baseStart_3067072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067092 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3067092 : Nat := 118140960795 + 3067092 * 2 ^ 59
def prefixEnd_3067092 : Nat := 4983230072969 + 3 ^ 40 * 3067092 * 2
def baseEnd_3067092 : Nat := 1574892407559819222144707

theorem tailTrace_3067092 : CollatzResearch.WordTrace tailWord_3067092 prefixEnd_3067092 1574892407559819222144707 := by
  unfold tailWord_3067092
  simp only [CollatzResearch.WordTrace]
  refine ⟨55933017702228488227729765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74577356936304650970306353 55933017702228488227729765)
  ·
    refine ⟨10487440819167841542699331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55933017702228488227729765 10487440819167841542699331)
    ·
      refine ⟨15731161228751762314048997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10487440819167841542699331 15731161228751762314048997)
      ·
        refine ⟨2949592730390955433884187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15731161228751762314048997 2949592730390955433884187)
        ·
          refine ⟨4424389095586433150826281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2949592730390955433884187 4424389095586433150826281)
          ·
            refine ⟨3318291821689824863119711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4424389095586433150826281 3318291821689824863119711)
            ·
              refine ⟨4977437732534737294679567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3318291821689824863119711 4977437732534737294679567)
              ·
                refine ⟨7466156598802105942019351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4977437732534737294679567 7466156598802105942019351)
                ·
                  refine ⟨11199234898203158913029027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7466156598802105942019351 11199234898203158913029027)
                  ·
                    refine ⟨16798852347304738369543541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11199234898203158913029027 16798852347304738369543541)
                    ·
                      refine ⟨1574892407559819222144707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16798852347304738369543541 1574892407559819222144707)
                      ·
                        rfl

theorem cell23_3067092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3067092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067092 prefixEnd_3067092 := by exact prefixLift 3067092
  have htrace : WordTrace (prefixWord ++ tailWord_3067092) baseStart_3067092 baseEnd_3067092 := by
    simpa [prefixWord, tailWord_3067092, baseEnd_3067092] using wordTrace_append hprefix tailTrace_3067092
  have hstable : (prefixWord ++ tailWord_3067092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067092).length < 2 ^ (prefixWord ++ tailWord_3067092).sum := by decide
  have hdescent : baseEnd_3067092 < baseStart_3067092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067105 : List Nat := [1, 2, 3, 1, 3, 2, 1, 4, 2, 1, 3]
def baseStart_3067105 : Nat := 118140960795 + 3067105 * 2 ^ 59
def prefixEnd_3067105 : Nat := 4983230072969 + 3 ^ 40 * 3067105 * 2
def baseEnd_3067105 : Nat := 1574899082808327671282147

theorem tailTrace_3067105 : CollatzResearch.WordTrace tailWord_3067105 prefixEnd_3067105 1574899082808327671282147 := by
  unfold tailWord_3067105
  simp only [CollatzResearch.WordTrace]
  refine ⟨111866509553409879675682769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74577673035606586450455179 111866509553409879675682769)
  ·
    refine ⟨83899882165057409756762077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111866509553409879675682769 83899882165057409756762077)
    ·
      refine ⟨31462455811896528658785779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83899882165057409756762077 31462455811896528658785779)
      ·
        refine ⟨47193683717844792988178669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31462455811896528658785779 47193683717844792988178669)
        ·
          refine ⟨17697631394191797370567001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47193683717844792988178669 17697631394191797370567001)
          ·
            refine ⟨13273223545643848027925251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17697631394191797370567001 13273223545643848027925251)
            ·
              refine ⟨19909835318465772041887877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13273223545643848027925251 19909835318465772041887877)
              ·
                refine ⟨3733094122212332257853977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19909835318465772041887877 3733094122212332257853977)
                ·
                  refine ⟨2799820591659249193390483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3733094122212332257853977 2799820591659249193390483)
                  ·
                    refine ⟨4199730887488873790085725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2799820591659249193390483 4199730887488873790085725)
                    ·
                      refine ⟨1574899082808327671282147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4199730887488873790085725 1574899082808327671282147)
                      ·
                        rfl

theorem cell23_3067105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_3067105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067105 prefixEnd_3067105 := by exact prefixLift 3067105
  have htrace : WordTrace (prefixWord ++ tailWord_3067105) baseStart_3067105 baseEnd_3067105 := by
    simpa [prefixWord, tailWord_3067105, baseEnd_3067105] using wordTrace_append hprefix tailTrace_3067105
  have hstable : (prefixWord ++ tailWord_3067105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067105).length < 2 ^ (prefixWord ++ tailWord_3067105).sum := by decide
  have hdescent : baseEnd_3067105 < baseStart_3067105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067141 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_3067141 : Nat := 118140960795 + 3067141 * 2 ^ 59
def prefixEnd_3067141 : Nat := 4983230072969 + 3 ^ 40 * 3067141 * 2
def baseEnd_3067141 : Nat := 1574917568111889530431981

theorem tailTrace_3067141 : CollatzResearch.WordTrace tailWord_3067141 prefixEnd_3067141 1574917568111889530431981 := by
  unfold tailWord_3067141
  simp only [CollatzResearch.WordTrace]
  refine ⟨111867822581279457823993277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74578548387519638549328851 111867822581279457823993277)
  ·
    refine ⟨41950433467979796683997479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111867822581279457823993277 41950433467979796683997479)
    ·
      refine ⟨62925650201969695025996219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41950433467979796683997479 62925650201969695025996219)
      ·
        refine ⟨94388475302954542538994329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62925650201969695025996219 94388475302954542538994329)
        ·
          refine ⟨70791356477215906904245747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94388475302954542538994329 70791356477215906904245747)
          ·
            refine ⟨106187034715823860356368621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70791356477215906904245747 106187034715823860356368621)
            ·
              refine ⟨39820138018433947633638233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106187034715823860356368621 39820138018433947633638233)
              ·
                refine ⟨29865103513825460725228675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39820138018433947633638233 29865103513825460725228675)
                ·
                  refine ⟨44797655270738191087843013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29865103513825460725228675 44797655270738191087843013)
                  ·
                    refine ⟨8399560363263410828970565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44797655270738191087843013 8399560363263410828970565)
                    ·
                      refine ⟨1574917568111889530431981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8399560363263410828970565 1574917568111889530431981)
                      ·
                        rfl

theorem cell23_3067141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_3067141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067141 prefixEnd_3067141 := by exact prefixLift 3067141
  have htrace : WordTrace (prefixWord ++ tailWord_3067141) baseStart_3067141 baseEnd_3067141 := by
    simpa [prefixWord, tailWord_3067141, baseEnd_3067141] using wordTrace_append hprefix tailTrace_3067141
  have hstable : (prefixWord ++ tailWord_3067141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067141).length < 2 ^ (prefixWord ++ tailWord_3067141).sum := by decide
  have hdescent : baseEnd_3067141 < baseStart_3067141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067145 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 4, 2, 2]
def baseStart_3067145 : Nat := 118140960795 + 3067145 * 2 ^ 59
def prefixEnd_3067145 : Nat := 4983230072969 + 3 ^ 40 * 3067145 * 2
def baseEnd_3067145 : Nat := 1574919622034507514781963

theorem tailTrace_3067145 : CollatzResearch.WordTrace tailWord_3067145 prefixEnd_3067145 1574919622034507514781963 := by
  unfold tailWord_3067145
  simp only [CollatzResearch.WordTrace]
  refine ⟨111867968473264966507138889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74578645648843311004759259 111867968473264966507138889)
  ·
    refine ⟨83900976354948724880354167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111867968473264966507138889 83900976354948724880354167)
    ·
      refine ⟨125851464532423087320531251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83900976354948724880354167 125851464532423087320531251)
      ·
        refine ⟨188777196798634630980796877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125851464532423087320531251 188777196798634630980796877)
        ·
          refine ⟨70791448799487986617798829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188777196798634630980796877 70791448799487986617798829)
          ·
            refine ⟨26546793299807994981674561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70791448799487986617798829 26546793299807994981674561)
            ·
              refine ⟨19910094974855996236255921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26546793299807994981674561 19910094974855996236255921)
              ·
                refine ⟨14932571231141997177191941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19910094974855996236255921 14932571231141997177191941)
                ·
                  refine ⟨2799857105839124470723489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14932571231141997177191941 2799857105839124470723489)
                  ·
                    refine ⟨2099892829379343353042617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2799857105839124470723489 2099892829379343353042617)
                    ·
                      refine ⟨1574919622034507514781963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099892829379343353042617 1574919622034507514781963)
                      ·
                        rfl

theorem cell23_3067145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 2, 2].length) (baseStart_3067145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067145 prefixEnd_3067145 := by exact prefixLift 3067145
  have htrace : WordTrace (prefixWord ++ tailWord_3067145) baseStart_3067145 baseEnd_3067145 := by
    simpa [prefixWord, tailWord_3067145, baseEnd_3067145] using wordTrace_append hprefix tailTrace_3067145
  have hstable : (prefixWord ++ tailWord_3067145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067145).length < 2 ^ (prefixWord ++ tailWord_3067145).sum := by decide
  have hdescent : baseEnd_3067145 < baseStart_3067145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067162 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2]
def baseStart_3067162 : Nat := 118140960795 + 3067162 * 2 ^ 59
def prefixEnd_3067162 : Nat := 4983230072969 + 3 ^ 40 * 3067162 * 2
def baseEnd_3067162 : Nat := 1574928351205633948269385

theorem tailTrace_3067162 : CollatzResearch.WordTrace tailWord_3067162 prefixEnd_3067162 1574928351205633948269385 := by
  unfold tailWord_3067162
  simp only [CollatzResearch.WordTrace]
  refine ⟨27967147128550844602626935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74579059009468918940338493 27967147128550844602626935)
  ·
    refine ⟨41950720692826266903940403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27967147128550844602626935 41950720692826266903940403)
    ·
      refine ⟨62926081039239400355910605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41950720692826266903940403 62926081039239400355910605)
      ·
        refine ⟨23597280389714775133466477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62926081039239400355910605 23597280389714775133466477)
        ·
          refine ⟨8848980146143040675049929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23597280389714775133466477 8848980146143040675049929)
          ·
            refine ⟨6636735109607280506287447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8848980146143040675049929 6636735109607280506287447)
            ·
              refine ⟨9955102664410920759431171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6636735109607280506287447 9955102664410920759431171)
              ·
                refine ⟨14932653996616381139146757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9955102664410920759431171 14932653996616381139146757)
                ·
                  refine ⟨2799872624365571463590017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14932653996616381139146757 2799872624365571463590017)
                  ·
                    refine ⟨2099904468274178597692513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2799872624365571463590017 2099904468274178597692513)
                    ·
                      refine ⟨1574928351205633948269385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2099904468274178597692513 1574928351205633948269385)
                      ·
                        rfl

theorem cell23_3067162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_3067162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067162 prefixEnd_3067162 := by exact prefixLift 3067162
  have htrace : WordTrace (prefixWord ++ tailWord_3067162) baseStart_3067162 baseEnd_3067162 := by
    simpa [prefixWord, tailWord_3067162, baseEnd_3067162] using wordTrace_append hprefix tailTrace_3067162
  have hstable : (prefixWord ++ tailWord_3067162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067162).length < 2 ^ (prefixWord ++ tailWord_3067162).sum := by decide
  have hdescent : baseEnd_3067162 < baseStart_3067162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067191 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_3067191 : Nat := 118140960795 + 3067191 * 2 ^ 59
def prefixEnd_3067191 : Nat := 4983230072969 + 3 ^ 40 * 3067191 * 2
def baseEnd_3067191 : Nat := 1574943242144614334806751

theorem tailTrace_3067191 : CollatzResearch.WordTrace tailWord_3067191 prefixEnd_3067191 1574943242144614334806751 := by
  unfold tailWord_3067191
  simp only [CollatzResearch.WordTrace]
  refine ⟨111869646231098316363313427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74579764154065544242208951 111869646231098316363313427)
  ·
    refine ⟨167804469346647474544970141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111869646231098316363313427 167804469346647474544970141)
    ·
      refine ⟨62926676004992802954363803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167804469346647474544970141 62926676004992802954363803)
      ·
        refine ⟨94390014007489204431545705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62926676004992802954363803 94390014007489204431545705)
        ·
          refine ⟨70792510505616903323659279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94390014007489204431545705 70792510505616903323659279)
          ·
            refine ⟨106188765758425354985488919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70792510505616903323659279 106188765758425354985488919)
            ·
              refine ⟨159283148637638032478233379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106188765758425354985488919 159283148637638032478233379)
              ·
                refine ⟨238924722956457048717350069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159283148637638032478233379 238924722956457048717350069)
                ·
                  refine ⟨22399192777167848317251569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 238924722956457048717350069 22399192777167848317251569)
                  ·
                    refine ⟨16799394582875886237938677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22399192777167848317251569 16799394582875886237938677)
                    ·
                      refine ⟨1574943242144614334806751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16799394582875886237938677 1574943242144614334806751)
                      ·
                        rfl

theorem cell23_3067191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_3067191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067191 prefixEnd_3067191 := by exact prefixLift 3067191
  have htrace : WordTrace (prefixWord ++ tailWord_3067191) baseStart_3067191 baseEnd_3067191 := by
    simpa [prefixWord, tailWord_3067191, baseEnd_3067191] using wordTrace_append hprefix tailTrace_3067191
  have hstable : (prefixWord ++ tailWord_3067191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067191).length < 2 ^ (prefixWord ++ tailWord_3067191).sum := by decide
  have hdescent : baseEnd_3067191 < baseStart_3067191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067198 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_3067198 : Nat := 118140960795 + 3067198 * 2 ^ 59
def prefixEnd_3067198 : Nat := 4983230072969 + 3 ^ 40 * 3067198 * 2
def baseEnd_3067198 : Nat := 524982278836398602473073

theorem tailTrace_3067198 : CollatzResearch.WordTrace tailWord_3067198 prefixEnd_3067198 524982278836398602473073 := by
  unfold tailWord_3067198
  simp only [CollatzResearch.WordTrace]
  refine ⟨13983737692759119569852281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74579934361381971039212165 13983737692759119569852281)
  ·
    refine ⟨10487803269569339677389211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13983737692759119569852281 10487803269569339677389211)
    ·
      refine ⟨15731704904354009516083817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10487803269569339677389211 15731704904354009516083817)
      ·
        refine ⟨11798778678265507137062863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15731704904354009516083817 11798778678265507137062863)
        ·
          refine ⟨17698168017398260705594295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11798778678265507137062863 17698168017398260705594295)
          ·
            refine ⟨26547252026097391058391443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17698168017398260705594295 26547252026097391058391443)
            ·
              refine ⟨39820878039146086587587165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26547252026097391058391443 39820878039146086587587165)
              ·
                refine ⟨14932829264679782470345187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39820878039146086587587165 14932829264679782470345187)
                ·
                  refine ⟨22399243897019673705517781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14932829264679782470345187 22399243897019673705517781)
                  ·
                    refine ⟨524982278836398602473073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22399243897019673705517781 524982278836398602473073)
                    ·
                      rfl

theorem cell23_3067198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_3067198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067198 prefixEnd_3067198 := by exact prefixLift 3067198
  have htrace : WordTrace (prefixWord ++ tailWord_3067198) baseStart_3067198 baseEnd_3067198 := by
    simpa [prefixWord, tailWord_3067198, baseEnd_3067198] using wordTrace_append hprefix tailTrace_3067198
  have hstable : (prefixWord ++ tailWord_3067198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067198).length < 2 ^ (prefixWord ++ tailWord_3067198).sum := by decide
  have hdescent : baseEnd_3067198 < baseStart_3067198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067241 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 10]
def baseStart_3067241 : Nat := 118140960795 + 3067241 * 2 ^ 59
def prefixEnd_3067241 : Nat := 4983230072969 + 3 ^ 40 * 3067241 * 2
def baseEnd_3067241 : Nat := 174996546241926571020169

theorem tailTrace_3067241 : CollatzResearch.WordTrace tailWord_3067241 prefixEnd_3067241 174996546241926571020169 := by
  unfold tailWord_3067241
  simp only [CollatzResearch.WordTrace]
  refine ⟨111871469880917174902633577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74580979920611449935089051 111871469880917174902633577)
  ·
    refine ⟨83903602410687881176975183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111871469880917174902633577 83903602410687881176975183)
    ·
      refine ⟨125855403616031821765462775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83903602410687881176975183 125855403616031821765462775)
      ·
        refine ⟨188783105424047732648194163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125855403616031821765462775 188783105424047732648194163)
        ·
          refine ⟨283174658136071598972291245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188783105424047732648194163 283174658136071598972291245)
          ·
            refine ⟨106190496801026849614609217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283174658136071598972291245 106190496801026849614609217)
            ·
              refine ⟨79642872600770137210956913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106190496801026849614609217 79642872600770137210956913)
              ·
                refine ⟨59732154450577602908217685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79642872600770137210956913 59732154450577602908217685)
                ·
                  refine ⟨174996546241926571020169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 59732154450577602908217685 174996546241926571020169)
                  ·
                    rfl

theorem cell23_3067241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 10].length) (baseStart_3067241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067241 prefixEnd_3067241 := by exact prefixLift 3067241
  have htrace : WordTrace (prefixWord ++ tailWord_3067241) baseStart_3067241 baseEnd_3067241 := by
    simpa [prefixWord, tailWord_3067241, baseEnd_3067241] using wordTrace_append hprefix tailTrace_3067241
  have hstable : (prefixWord ++ tailWord_3067241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067241).length < 2 ^ (prefixWord ++ tailWord_3067241).sum := by decide
  have hdescent : baseEnd_3067241 < baseStart_3067241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067251 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 9]
def baseStart_3067251 : Nat := 118140960795 + 3067251 * 2 ^ 59
def prefixEnd_3067251 : Nat := 4983230072969 + 3 ^ 40 * 3067251 * 2
def baseEnd_3067251 : Nat := 1574974050983884100056475

theorem tailTrace_3067251 : CollatzResearch.WordTrace tailWord_3067251 prefixEnd_3067251 1574974050983884100056475 := by
  unfold tailWord_3067251
  simp only [CollatzResearch.WordTrace]
  refine ⟨111871834610880946610497607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74581223073920631073665071 111871834610880946610497607)
  ·
    refine ⟨167807751916321419915746411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111871834610880946610497607 167807751916321419915746411)
    ·
      refine ⟨251711627874482129873619617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167807751916321419915746411 251711627874482129873619617)
      ·
        refine ⟨188783720905861597405214713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251711627874482129873619617 188783720905861597405214713)
        ·
          refine ⟨141587790679396198053911035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188783720905861597405214713 141587790679396198053911035)
          ·
            refine ⟨212381686019094297080866553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141587790679396198053911035 212381686019094297080866553)
            ·
              refine ⟨159286264514320722810649915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212381686019094297080866553 159286264514320722810649915)
              ·
                refine ⟨238929396771481084215974873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159286264514320722810649915 238929396771481084215974873)
                ·
                  refine ⟨179197047578610813161981155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238929396771481084215974873 179197047578610813161981155)
                  ·
                    refine ⟨268795571367916219742971733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 179197047578610813161981155 268795571367916219742971733)
                    ·
                      refine ⟨1574974050983884100056475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 268795571367916219742971733 1574974050983884100056475)
                      ·
                        rfl

theorem cell23_3067251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_3067251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067251 prefixEnd_3067251 := by exact prefixLift 3067251
  have htrace : WordTrace (prefixWord ++ tailWord_3067251) baseStart_3067251 baseEnd_3067251 := by
    simpa [prefixWord, tailWord_3067251, baseEnd_3067251] using wordTrace_append hprefix tailTrace_3067251
  have hstable : (prefixWord ++ tailWord_3067251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067251).length < 2 ^ (prefixWord ++ tailWord_3067251).sum := by decide
  have hdescent : baseEnd_3067251 < baseStart_3067251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067255 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 3]
def baseStart_3067255 : Nat := 118140960795 + 3067255 * 2 ^ 59
def prefixEnd_3067255 : Nat := 4983230072969 + 3 ^ 40 * 3067255 * 2
def baseEnd_3067255 : Nat := 1574976104906502084406457

theorem tailTrace_3067255 : CollatzResearch.WordTrace tailWord_3067255 prefixEnd_3067255 1574976104906502084406457 := by
  unfold tailWord_3067255
  simp only [CollatzResearch.WordTrace]
  refine ⟨111871980502866455293643219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74581320335244303529095479 111871980502866455293643219)
  ·
    refine ⟨167807970754299682940464829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111871980502866455293643219 167807970754299682940464829)
    ·
      refine ⟨62927989032862381102674311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167807970754299682940464829 62927989032862381102674311)
      ·
        refine ⟨94391983549293571654011467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62927989032862381102674311 94391983549293571654011467)
        ·
          refine ⟨141587975323940357481017201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94391983549293571654011467 141587975323940357481017201)
          ·
            refine ⟨106190981492955268110762901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141587975323940357481017201 106190981492955268110762901)
            ·
              refine ⟨4977702257482278192692011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106190981492955268110762901 4977702257482278192692011)
              ·
                refine ⟨7466553386223417289038017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4977702257482278192692011 7466553386223417289038017)
                ·
                  refine ⟨5599915039667562966778513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7466553386223417289038017 5599915039667562966778513)
                  ·
                    refine ⟨4199936279750672225083885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5599915039667562966778513 4199936279750672225083885)
                    ·
                      refine ⟨1574976104906502084406457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4199936279750672225083885 1574976104906502084406457)
                      ·
                        rfl

theorem cell23_3067255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_3067255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067255 prefixEnd_3067255 := by exact prefixLift 3067255
  have htrace : WordTrace (prefixWord ++ tailWord_3067255) baseStart_3067255 baseEnd_3067255 := by
    simpa [prefixWord, tailWord_3067255, baseEnd_3067255] using wordTrace_append hprefix tailTrace_3067255
  have hstable : (prefixWord ++ tailWord_3067255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067255).length < 2 ^ (prefixWord ++ tailWord_3067255).sum := by decide
  have hdescent : baseEnd_3067255 < baseStart_3067255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067319 : List Nat := [1, 1, 3, 1, 3, 2, 4, 3, 1, 1, 3]
def baseStart_3067319 : Nat := 118140960795 + 3067319 * 2 ^ 59
def prefixEnd_3067319 : Nat := 4983230072969 + 3 ^ 40 * 3067319 * 2
def baseEnd_3067319 : Nat := 1575008967668389834006163

theorem tailTrace_3067319 : CollatzResearch.WordTrace tailWord_3067319 prefixEnd_3067319 1575008967668389834006163 := by
  unfold tailWord_3067319
  simp only [CollatzResearch.WordTrace]
  refine ⟨111874314774634594223973011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74582876516423062815982007 111874314774634594223973011)
  ·
    refine ⟨167811472161951891335959517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111874314774634594223973011 167811472161951891335959517)
    ·
      refine ⟨62929302060731959250984819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167811472161951891335959517 62929302060731959250984819)
      ·
        refine ⟨94393953091097938876477229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62929302060731959250984819 94393953091097938876477229)
        ·
          refine ⟨35397732409161727078678961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94393953091097938876477229 35397732409161727078678961)
          ·
            refine ⟨26548299306871295309009221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35397732409161727078678961 26548299306871295309009221)
            ·
              refine ⟨4977806120038367870439229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26548299306871295309009221 4977806120038367870439229)
              ·
                refine ⟨1866677295014387951414711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4977806120038367870439229 1866677295014387951414711)
                ·
                  refine ⟨2800015942521581927122067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866677295014387951414711 2800015942521581927122067)
                  ·
                    refine ⟨4200023913782372890683101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2800015942521581927122067 4200023913782372890683101)
                    ·
                      refine ⟨1575008967668389834006163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4200023913782372890683101 1575008967668389834006163)
                      ·
                        rfl

theorem cell23_3067319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 1, 1, 3].length) (baseStart_3067319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067319 prefixEnd_3067319 := by exact prefixLift 3067319
  have htrace : WordTrace (prefixWord ++ tailWord_3067319) baseStart_3067319 baseEnd_3067319 := by
    simpa [prefixWord, tailWord_3067319, baseEnd_3067319] using wordTrace_append hprefix tailTrace_3067319
  have hstable : (prefixWord ++ tailWord_3067319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067319).length < 2 ^ (prefixWord ++ tailWord_3067319).sum := by decide
  have hdescent : baseEnd_3067319 < baseStart_3067319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067335 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 4, 4]
def baseStart_3067335 : Nat := 118140960795 + 3067335 * 2 ^ 59
def prefixEnd_3067335 : Nat := 4983230072969 + 3 ^ 40 * 3067335 * 2
def baseEnd_3067335 : Nat := 525005727786287257135363

theorem tailTrace_3067335 : CollatzResearch.WordTrace tailWord_3067335 prefixEnd_3067335 525005727786287257135363 := by
  unfold tailWord_3067335
  simp only [CollatzResearch.WordTrace]
  refine ⟨111874898342576628956555459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74583265561717752637703639 111874898342576628956555459)
  ·
    refine ⟨167812347513864943434833189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111874898342576628956555459 167812347513864943434833189)
    ·
      refine ⟨31464815158849676894031223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167812347513864943434833189 31464815158849676894031223)
      ·
        refine ⟨47197222738274515341046835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31464815158849676894031223 47197222738274515341046835)
        ·
          refine ⟨70795834107411773011570253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47197222738274515341046835 70795834107411773011570253)
          ·
            refine ⟨26548437790279414879338845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70795834107411773011570253 26548437790279414879338845)
            ·
              refine ⟨9955664171354780579752067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26548437790279414879338845 9955664171354780579752067)
              ·
                refine ⟨14933496257032170869628101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9955664171354780579752067 14933496257032170869628101)
                ·
                  refine ⟨2800030548193532038055269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14933496257032170869628101 2800030548193532038055269)
                  ·
                    refine ⟨525005727786287257135363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2800030548193532038055269 525005727786287257135363)
                    ·
                      rfl

theorem cell23_3067335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_3067335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067335 prefixEnd_3067335 := by exact prefixLift 3067335
  have htrace : WordTrace (prefixWord ++ tailWord_3067335) baseStart_3067335 baseEnd_3067335 := by
    simpa [prefixWord, tailWord_3067335, baseEnd_3067335] using wordTrace_append hprefix tailTrace_3067335
  have hstable : (prefixWord ++ tailWord_3067335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067335).length < 2 ^ (prefixWord ++ tailWord_3067335).sum := by decide
  have hdescent : baseEnd_3067335 < baseStart_3067335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067365 : List Nat := [1, 3, 1, 5, 1, 2, 1, 9]
def baseStart_3067365 : Nat := 118140960795 + 3067365 * 2 ^ 59
def prefixEnd_3067365 : Nat := 4983230072969 + 3 ^ 40 * 3067365 * 2
def baseEnd_3067365 : Nat := 58334540288092468667813

theorem tailTrace_3067365 : CollatzResearch.WordTrace tailWord_3067365 prefixEnd_3067365 58334540288092468667813 := by
  unfold tailWord_3067365
  simp only [CollatzResearch.WordTrace]
  refine ⟨111875992532467944080147549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74583995021645296053431699 111875992532467944080147549)
  ·
    refine ⟨41953497199675479030055331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111875992532467944080147549 41953497199675479030055331)
    ·
      refine ⟨62930245799513218545082997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41953497199675479030055331 62930245799513218545082997)
      ·
        refine ⟨5899710543704364238601531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62930245799513218545082997 5899710543704364238601531)
        ·
          refine ⟨8849565815556546357902297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5899710543704364238601531 8849565815556546357902297)
          ·
            refine ⟨6637174361667409768426723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8849565815556546357902297 6637174361667409768426723)
            ·
              refine ⟨9955761542501114652640085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6637174361667409768426723 9955761542501114652640085)
              ·
                refine ⟨58334540288092468667813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9955761542501114652640085 58334540288092468667813)
                ·
                  rfl

theorem cell23_3067365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 9].length) (baseStart_3067365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067365 prefixEnd_3067365 := by exact prefixLift 3067365
  have htrace : WordTrace (prefixWord ++ tailWord_3067365) baseStart_3067365 baseEnd_3067365 := by
    simpa [prefixWord, tailWord_3067365, baseEnd_3067365] using wordTrace_append hprefix tailTrace_3067365
  have hstable : (prefixWord ++ tailWord_3067365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067365).length < 2 ^ (prefixWord ++ tailWord_3067365).sum := by decide
  have hdescent : baseEnd_3067365 < baseStart_3067365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067375 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 3]
def baseStart_3067375 : Nat := 118140960795 + 3067375 * 2 ^ 59
def prefixEnd_3067375 : Nat := 4983230072969 + 3 ^ 40 * 3067375 * 2
def baseEnd_3067375 : Nat := 1575037722585041614905905

theorem tailTrace_3067375 : CollatzResearch.WordTrace tailWord_3067375 prefixEnd_3067375 1575037722585041614905905 := by
  unfold tailWord_3067375
  simp only [CollatzResearch.WordTrace]
  refine ⟨111876357262431715788011579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74584238174954477192007719 111876357262431715788011579)
  ·
    refine ⟨167814535893647573682017369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111876357262431715788011579 167814535893647573682017369)
    ·
      refine ⟨125860901920235680261513027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167814535893647573682017369 125860901920235680261513027)
      ·
        refine ⟨188791352880353520392269541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125860901920235680261513027 188791352880353520392269541)
        ·
          refine ⟨35398378665066285073550539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188791352880353520392269541 35398378665066285073550539)
          ·
            refine ⟨53097567997599427610325809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35398378665066285073550539 53097567997599427610325809)
            ·
              refine ⟨39823175998199570707744357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53097567997599427610325809 39823175998199570707744357)
              ·
                refine ⟨7466845499662419507702067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39823175998199570707744357 7466845499662419507702067)
                ·
                  refine ⟨11200268249493629261553101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7466845499662419507702067 11200268249493629261553101)
                  ·
                    refine ⟨4200100593560110973082413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11200268249493629261553101 4200100593560110973082413)
                    ·
                      refine ⟨1575037722585041614905905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4200100593560110973082413 1575037722585041614905905)
                      ·
                        rfl

theorem cell23_3067375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 3].length) (baseStart_3067375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067375 prefixEnd_3067375 := by exact prefixLift 3067375
  have htrace : WordTrace (prefixWord ++ tailWord_3067375) baseStart_3067375 baseEnd_3067375 := by
    simpa [prefixWord, tailWord_3067375, baseEnd_3067375] using wordTrace_append hprefix tailTrace_3067375
  have hstable : (prefixWord ++ tailWord_3067375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067375).length < 2 ^ (prefixWord ++ tailWord_3067375).sum := by decide
  have hdescent : baseEnd_3067375 < baseStart_3067375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067376 : List Nat := [2, 1, 1, 1, 3, 4, 3, 3, 1, 2, 2]
def baseStart_3067376 : Nat := 118140960795 + 3067376 * 2 ^ 59
def prefixEnd_3067376 : Nat := 4983230072969 + 3 ^ 40 * 3067376 * 2
def baseEnd_3067376 : Nat := 1575038236065696110993401

theorem tailTrace_3067376 : CollatzResearch.WordTrace tailWord_3067376 prefixEnd_3067376 1575038236065696110993401 := by
  unfold tailWord_3067376
  simp only [CollatzResearch.WordTrace]
  refine ⟨55938196867714046479398991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74584262490285395305865321 55938196867714046479398991)
  ·
    refine ⟨83907295301571069719098487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55938196867714046479398991 83907295301571069719098487)
    ·
      refine ⟨125860942952356604578647731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83907295301571069719098487 125860942952356604578647731)
      ·
        refine ⟨188791414428534906867971597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125860942952356604578647731 188791414428534906867971597)
        ·
          refine ⟨70796780410700590075489349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188791414428534906867971597 70796780410700590075489349)
          ·
            refine ⟨13274396327006360639154253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70796780410700590075489349 13274396327006360639154253)
            ·
              refine ⟨4977898622627385239682845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13274396327006360639154253 4977898622627385239682845)
              ·
                refine ⟨1866711983485269464881067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4977898622627385239682845 1866711983485269464881067)
                ·
                  refine ⟨2800067975227904197321601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866711983485269464881067 2800067975227904197321601)
                  ·
                    refine ⟨2100050981420928147991201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2800067975227904197321601 2100050981420928147991201)
                    ·
                      refine ⟨1575038236065696110993401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2100050981420928147991201 1575038236065696110993401)
                      ·
                        rfl

theorem cell23_3067376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 1, 2, 2].length) (baseStart_3067376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067376 prefixEnd_3067376 := by exact prefixLift 3067376
  have htrace : WordTrace (prefixWord ++ tailWord_3067376) baseStart_3067376 baseEnd_3067376 := by
    simpa [prefixWord, tailWord_3067376, baseEnd_3067376] using wordTrace_append hprefix tailTrace_3067376
  have hstable : (prefixWord ++ tailWord_3067376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067376).length < 2 ^ (prefixWord ++ tailWord_3067376).sum := by decide
  have hdescent : baseEnd_3067376 < baseStart_3067376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067393 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_3067393 : Nat := 118140960795 + 3067393 * 2 ^ 59
def prefixEnd_3067393 : Nat := 4983230072969 + 3 ^ 40 * 3067393 * 2
def baseEnd_3067393 : Nat := 1575046965236822544480823

theorem tailTrace_3067393 : CollatzResearch.WordTrace tailWord_3067393 prefixEnd_3067393 1575046965236822544480823 := by
  unfold tailWord_3067393
  simp only [CollatzResearch.WordTrace]
  refine ⟨111877013776366504862166833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74584675850911003241444555 111877013776366504862166833)
  ·
    refine ⟨83907760332274878646625125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111877013776366504862166833 83907760332274878646625125)
    ·
      refine ⟨15732705062301539746242211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83907760332274878646625125 15732705062301539746242211)
      ·
        refine ⟨23599057593452309619363317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15732705062301539746242211 23599057593452309619363317)
        ·
          refine ⟨2212411649386154026815311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23599057593452309619363317 2212411649386154026815311)
          ·
            refine ⟨3318617474079231040222967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212411649386154026815311 3318617474079231040222967)
            ·
              refine ⟨4977926211118846560334451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3318617474079231040222967 4977926211118846560334451)
              ·
                refine ⟨7466889316678269840501677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4977926211118846560334451 7466889316678269840501677)
                ·
                  refine ⟨2800083493754351190188129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7466889316678269840501677 2800083493754351190188129)
                  ·
                    refine ⟨2100062620315763392641097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2800083493754351190188129 2100062620315763392641097)
                    ·
                      refine ⟨1575046965236822544480823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2100062620315763392641097 1575046965236822544480823)
                      ·
                        rfl

theorem cell23_3067393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_3067393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067393 prefixEnd_3067393 := by exact prefixLift 3067393
  have htrace : WordTrace (prefixWord ++ tailWord_3067393) baseStart_3067393 baseEnd_3067393 := by
    simpa [prefixWord, tailWord_3067393, baseEnd_3067393] using wordTrace_append hprefix tailTrace_3067393
  have hstable : (prefixWord ++ tailWord_3067393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067393).length < 2 ^ (prefixWord ++ tailWord_3067393).sum := by decide
  have hdescent : baseEnd_3067393 < baseStart_3067393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067495 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_3067495 : Nat := 118140960795 + 3067495 * 2 ^ 59
def prefixEnd_3067495 : Nat := 4983230072969 + 3 ^ 40 * 3067495 * 2
def baseEnd_3067495 : Nat := 1575099340263581145405353

theorem tailTrace_3067495 : CollatzResearch.WordTrace tailWord_3067495 prefixEnd_3067495 1575099340263581145405353 := by
  unfold tailWord_3067495
  simp only [CollatzResearch.WordTrace]
  refine ⟨111880734021996976282379939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74587156014664650854919959 111880734021996976282379939)
  ·
    refine ⟨167821101032995464423569909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111880734021996976282379939 167821101032995464423569909)
    ·
      refine ⟨15733228221843324789709679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167821101032995464423569909 15733228221843324789709679)
      ·
        refine ⟨23599842332764987184564519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15733228221843324789709679 23599842332764987184564519)
        ·
          refine ⟨35399763499147480776846779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23599842332764987184564519 35399763499147480776846779)
          ·
            refine ⟨53099645248721221165270169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35399763499147480776846779 53099645248721221165270169)
            ·
              refine ⟨39824733936540915873952627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53099645248721221165270169 39824733936540915873952627)
              ·
                refine ⟨59737100904811373810928941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39824733936540915873952627 59737100904811373810928941)
                ·
                  refine ⟨22401412839304265179098353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59737100904811373810928941 22401412839304265179098353)
                  ·
                    refine ⟨16801059629478198884323765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22401412839304265179098353 16801059629478198884323765)
                    ·
                      refine ⟨1575099340263581145405353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16801059629478198884323765 1575099340263581145405353)
                      ·
                        rfl

theorem cell23_3067495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_3067495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067495 prefixEnd_3067495 := by exact prefixLift 3067495
  have htrace : WordTrace (prefixWord ++ tailWord_3067495) baseStart_3067495 baseEnd_3067495 := by
    simpa [prefixWord, tailWord_3067495, baseEnd_3067495] using wordTrace_append hprefix tailTrace_3067495
  have hstable : (prefixWord ++ tailWord_3067495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067495).length < 2 ^ (prefixWord ++ tailWord_3067495).sum := by decide
  have hdescent : baseEnd_3067495 < baseStart_3067495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067532 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 3, 4]
def baseStart_3067532 : Nat := 118140960795 + 3067532 * 2 ^ 59
def prefixEnd_3067532 : Nat := 4983230072969 + 3 ^ 40 * 3067532 * 2
def baseEnd_3067532 : Nat := 525039446349265833547561

theorem tailTrace_3067532 : CollatzResearch.WordTrace tailWord_3067532 prefixEnd_3067532 525039446349265833547561 := by
  unfold tailWord_3067532
  simp only [CollatzResearch.WordTrace]
  refine ⟨55941041761431465800738425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74588055681908621067651233 55941041761431465800738425)
  ·
    refine ⟨41955781321073599350553819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55941041761431465800738425 41955781321073599350553819)
    ·
      refine ⟨62933671981610399025830729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41955781321073599350553819 62933671981610399025830729)
      ·
        refine ⟨47200253986207799269373047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62933671981610399025830729 47200253986207799269373047)
        ·
          refine ⟨70800380979311698904059571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47200253986207799269373047 70800380979311698904059571)
          ·
            refine ⟨106200571468967548356089357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70800380979311698904059571 106200571468967548356089357)
            ·
              refine ⟨39825214300862830633533509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106200571468967548356089357 39825214300862830633533509)
              ·
                refine ⟨7467227681411780743787533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39825214300862830633533509 7467227681411780743787533)
                ·
                  refine ⟨2800210380529417778920325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7467227681411780743787533 2800210380529417778920325)
                  ·
                    refine ⟨525039446349265833547561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2800210380529417778920325 525039446349265833547561)
                    ·
                      rfl

theorem cell23_3067532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_3067532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067532 prefixEnd_3067532 := by exact prefixLift 3067532
  have htrace : WordTrace (prefixWord ++ tailWord_3067532) baseStart_3067532 baseEnd_3067532 := by
    simpa [prefixWord, tailWord_3067532, baseEnd_3067532] using wordTrace_append hprefix tailTrace_3067532
  have hstable : (prefixWord ++ tailWord_3067532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067532).length < 2 ^ (prefixWord ++ tailWord_3067532).sum := by decide
  have hdescent : baseEnd_3067532 < baseStart_3067532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067592 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 3, 5]
def baseStart_3067592 : Nat := 118140960795 + 3067592 * 2 ^ 59
def prefixEnd_3067592 : Nat := 4983230072969 + 3 ^ 40 * 3067592 * 2
def baseEnd_3067592 : Nat := 525049715962355755297469

theorem tailTrace_3067592 : CollatzResearch.WordTrace tailWord_3067592 prefixEnd_3067592 525049715962355755297469 := by
  unfold tailWord_3067592
  simp only [CollatzResearch.WordTrace]
  refine ⟨55942135951322780924330515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74589514601763707899107353 55942135951322780924330515)
  ·
    refine ⟨83913203926984171386495773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55942135951322780924330515 83913203926984171386495773)
    ·
      refine ⟨31467451472619064269935915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83913203926984171386495773 31467451472619064269935915)
      ·
        refine ⟨47201177208928596404903873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31467451472619064269935915 47201177208928596404903873)
        ·
          refine ⟨35400882906696447303677905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47201177208928596404903873 35400882906696447303677905)
          ·
            refine ⟨26550662180022335477758429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35400882906696447303677905 26550662180022335477758429)
            ·
              refine ⟨9956498317508375804159411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26550662180022335477758429 9956498317508375804159411)
              ·
                refine ⟨14934747476262563706239117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9956498317508375804159411 14934747476262563706239117)
                ·
                  refine ⟨5600530303598461389839669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14934747476262563706239117 5600530303598461389839669)
                  ·
                    refine ⟨525049715962355755297469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5600530303598461389839669 525049715962355755297469)
                    ·
                      rfl

theorem cell23_3067592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_3067592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067592 prefixEnd_3067592 := by exact prefixLift 3067592
  have htrace : WordTrace (prefixWord ++ tailWord_3067592) baseStart_3067592 baseEnd_3067592 := by
    simpa [prefixWord, tailWord_3067592, baseEnd_3067592] using wordTrace_append hprefix tailTrace_3067592
  have hstable : (prefixWord ++ tailWord_3067592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067592).length < 2 ^ (prefixWord ++ tailWord_3067592).sum := by decide
  have hdescent : baseEnd_3067592 < baseStart_3067592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067629 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3067629 : Nat := 118140960795 + 3067629 * 2 ^ 59
def prefixEnd_3067629 : Nat := 4983230072969 + 3 ^ 40 * 3067629 * 2
def baseEnd_3067629 : Nat := 1575168146671283621129737

theorem tailTrace_3067629 : CollatzResearch.WordTrace tailWord_3067629 prefixEnd_3067629 1575168146671283621129737 := by
  unfold tailWord_3067629
  simp only [CollatzResearch.WordTrace]
  refine ⟨111885621403511517167757941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74590414269007678111838627 111885621403511517167757941)
  ·
    refine ⟨10489277006579204734477307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111885621403511517167757941 10489277006579204734477307)
    ·
      refine ⟨15733915509868807101715961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10489277006579204734477307 15733915509868807101715961)
      ·
        refine ⟨11800436632401605326286971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15733915509868807101715961 11800436632401605326286971)
        ·
          refine ⟨17700654948602407989430457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11800436632401605326286971 17700654948602407989430457)
          ·
            refine ⟨13275491211451805992072843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17700654948602407989430457 13275491211451805992072843)
            ·
              refine ⟨19913236817177708988109265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13275491211451805992072843 19913236817177708988109265)
              ·
                refine ⟨14934927612883281741081949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19913236817177708988109265 14934927612883281741081949)
                ·
                  refine ⟨5600597854831230652905731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14934927612883281741081949 5600597854831230652905731)
                  ·
                    refine ⟨8400896782246845979358597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5600597854831230652905731 8400896782246845979358597)
                    ·
                      refine ⟨1575168146671283621129737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8400896782246845979358597 1575168146671283621129737)
                      ·
                        rfl

theorem cell23_3067629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3067629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067629 prefixEnd_3067629 := by exact prefixLift 3067629
  have htrace : WordTrace (prefixWord ++ tailWord_3067629) baseStart_3067629 baseEnd_3067629 := by
    simpa [prefixWord, tailWord_3067629, baseEnd_3067629] using wordTrace_append hprefix tailTrace_3067629
  have hstable : (prefixWord ++ tailWord_3067629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067629).length < 2 ^ (prefixWord ++ tailWord_3067629).sum := by decide
  have hdescent : baseEnd_3067629 < baseStart_3067629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067639 : List Nat := [1, 1, 3, 1, 1, 1, 6, 3, 2, 4]
def baseStart_3067639 : Nat := 118140960795 + 3067639 * 2 ^ 59
def prefixEnd_3067639 : Nat := 4983230072969 + 3 ^ 40 * 3067639 * 2
def baseEnd_3067639 : Nat := 525057760492609527334897

theorem tailTrace_3067639 : CollatzResearch.WordTrace tailWord_3067639 prefixEnd_3067639 525057760492609527334897 := by
  unfold tailWord_3067639
  simp only [CollatzResearch.WordTrace]
  refine ⟨111885986133475288875621971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74590657422316859250414647 111885986133475288875621971)
  ·
    refine ⟨167828979200212933313432957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111885986133475288875621971 167828979200212933313432957)
    ·
      refine ⟨62935867200079849992537359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167828979200212933313432957 62935867200079849992537359)
      ·
        refine ⟨94403800800119774988806039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62935867200079849992537359 94403800800119774988806039)
        ·
          refine ⟨141605701200179662483209059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94403800800119774988806039 141605701200179662483209059)
          ·
            refine ⟨212408551800269493724813589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141605701200179662483209059 212408551800269493724813589)
            ·
              refine ⟨9956650865637632518350637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 212408551800269493724813589 9956650865637632518350637)
              ·
                refine ⟨3733744074614112194381489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9956650865637632518350637 3733744074614112194381489)
                ·
                  refine ⟨2800308055960584145786117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3733744074614112194381489 2800308055960584145786117)
                  ·
                    refine ⟨525057760492609527334897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2800308055960584145786117 525057760492609527334897)
                    ·
                      rfl

theorem cell23_3067639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_3067639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067639 prefixEnd_3067639 := by exact prefixLift 3067639
  have htrace : WordTrace (prefixWord ++ tailWord_3067639) baseStart_3067639 baseEnd_3067639 := by
    simpa [prefixWord, tailWord_3067639, baseEnd_3067639] using wordTrace_append hprefix tailTrace_3067639
  have hstable : (prefixWord ++ tailWord_3067639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067639).length < 2 ^ (prefixWord ++ tailWord_3067639).sum := by decide
  have hdescent : baseEnd_3067639 < baseStart_3067639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067649 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_3067649 : Nat := 118140960795 + 3067649 * 2 ^ 59
def prefixEnd_3067649 : Nat := 4983230072969 + 3 ^ 40 * 3067649 * 2
def baseEnd_3067649 : Nat := 1575178416284373542879645

theorem tailTrace_3067649 : CollatzResearch.WordTrace tailWord_3067649 prefixEnd_3067649 1575178416284373542879645 := by
  unfold tailWord_3067649
  simp only [CollatzResearch.WordTrace]
  refine ⟨111886350863439060583486001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74590900575626040388990667 111886350863439060583486001)
  ·
    refine ⟨83914763147579295437614501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111886350863439060583486001 83914763147579295437614501)
    ·
      refine ⟨15734018090171117894552719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83914763147579295437614501 15734018090171117894552719)
      ·
        refine ⟨23601027135256676841829079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15734018090171117894552719 23601027135256676841829079)
        ·
          refine ⟨35401540702885015262743619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23601027135256676841829079 35401540702885015262743619)
          ·
            refine ⟨53102311054327522894115429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35401540702885015262743619 53102311054327522894115429)
            ·
              refine ⟨9956683322686410542646643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53102311054327522894115429 9956683322686410542646643)
              ·
                refine ⟨14935024984029615813969965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9956683322686410542646643 14935024984029615813969965)
                ·
                  refine ⟨5600634369011105930238737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14935024984029615813969965 5600634369011105930238737)
                  ·
                    refine ⟨4200475776758329447679053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5600634369011105930238737 4200475776758329447679053)
                    ·
                      refine ⟨1575178416284373542879645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4200475776758329447679053 1575178416284373542879645)
                      ·
                        rfl

theorem cell23_3067649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_3067649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067649 prefixEnd_3067649 := by exact prefixLift 3067649
  have htrace : WordTrace (prefixWord ++ tailWord_3067649) baseStart_3067649 baseEnd_3067649 := by
    simpa [prefixWord, tailWord_3067649, baseEnd_3067649] using wordTrace_append hprefix tailTrace_3067649
  have hstable : (prefixWord ++ tailWord_3067649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067649).length < 2 ^ (prefixWord ++ tailWord_3067649).sum := by decide
  have hdescent : baseEnd_3067649 < baseStart_3067649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067709 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3067709 : Nat := 118140960795 + 3067709 * 2 ^ 59
def prefixEnd_3067709 : Nat := 4983230072969 + 3 ^ 40 * 3067709 * 2
def baseEnd_3067709 : Nat := 1575209225123643308129369

theorem tailTrace_3067709 : CollatzResearch.WordTrace tailWord_3067709 prefixEnd_3067709 1575209225123643308129369 := by
  unfold tailWord_3067709
  simp only [CollatzResearch.WordTrace]
  refine ⟨111888539243221690830670181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74592359495481127220446787 111888539243221690830670181)
  ·
    refine ⟨20979101108104067030750659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111888539243221690830670181 20979101108104067030750659)
    ·
      refine ⟨31468651662156100546125989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20979101108104067030750659 31468651662156100546125989)
      ·
        refine ⟨5900372186654268852398623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31468651662156100546125989 5900372186654268852398623)
        ·
          refine ⟨8850558279981403278597935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5900372186654268852398623 8850558279981403278597935)
          ·
            refine ⟨13275837419972104917896903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8850558279981403278597935 13275837419972104917896903)
            ·
              refine ⟨19913756129958157376845355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13275837419972104917896903 19913756129958157376845355)
              ·
                refine ⟨29870634194937236065268033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19913756129958157376845355 29870634194937236065268033)
                ·
                  refine ⟨22402975646202927048951025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29870634194937236065268033 22402975646202927048951025)
                  ·
                    refine ⟨16802231734652195286713269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22402975646202927048951025 16802231734652195286713269)
                    ·
                      refine ⟨1575209225123643308129369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16802231734652195286713269 1575209225123643308129369)
                      ·
                        rfl

theorem cell23_3067709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3067709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067709 prefixEnd_3067709 := by exact prefixLift 3067709
  have htrace : WordTrace (prefixWord ++ tailWord_3067709) baseStart_3067709 baseEnd_3067709 := by
    simpa [prefixWord, tailWord_3067709, baseEnd_3067709] using wordTrace_append hprefix tailTrace_3067709
  have hstable : (prefixWord ++ tailWord_3067709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067709).length < 2 ^ (prefixWord ++ tailWord_3067709).sum := by decide
  have hdescent : baseEnd_3067709 < baseStart_3067709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067747 : List Nat := [1, 1, 1, 5, 5, 1, 2, 1, 2, 1, 3]
def baseStart_3067747 : Nat := 118140960795 + 3067747 * 2 ^ 59
def prefixEnd_3067747 : Nat := 4983230072969 + 3 ^ 40 * 3067747 * 2
def baseEnd_3067747 : Nat := 1575228737388514159454195

theorem tailTrace_3067747 : CollatzResearch.WordTrace tailWord_3067747 prefixEnd_3067747 1575228737388514159454195 := by
  unfold tailWord_3067747
  simp only [CollatzResearch.WordTrace]
  refine ⟨111889925217084023320553495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74593283478056015547035663 111889925217084023320553495)
  ·
    refine ⟨167834887825626034980830243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111889925217084023320553495 167834887825626034980830243)
    ·
      refine ⟨251752331738439052471245365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167834887825626034980830243 251752331738439052471245365)
      ·
        refine ⟨23601781100478661169179253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251752331738439052471245365 23601781100478661169179253)
        ·
          refine ⟨2212666978169874484610555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23601781100478661169179253 2212666978169874484610555)
          ·
            refine ⟨3319000467254811726915833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212666978169874484610555 3319000467254811726915833)
            ·
              refine ⟨2489250350441108795186875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3319000467254811726915833 2489250350441108795186875)
              ·
                refine ⟨3733875525661663192780313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489250350441108795186875 3733875525661663192780313)
                ·
                  refine ⟨2800406644246247394585235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3733875525661663192780313 2800406644246247394585235)
                  ·
                    refine ⟨4200609966369371091877853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2800406644246247394585235 4200609966369371091877853)
                    ·
                      refine ⟨1575228737388514159454195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4200609966369371091877853 1575228737388514159454195)
                      ·
                        rfl

theorem cell23_3067747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_3067747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067747 prefixEnd_3067747 := by exact prefixLift 3067747
  have htrace : WordTrace (prefixWord ++ tailWord_3067747) baseStart_3067747 baseEnd_3067747 := by
    simpa [prefixWord, tailWord_3067747, baseEnd_3067747] using wordTrace_append hprefix tailTrace_3067747
  have hstable : (prefixWord ++ tailWord_3067747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067747).length < 2 ^ (prefixWord ++ tailWord_3067747).sum := by decide
  have hdescent : baseEnd_3067747 < baseStart_3067747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067799 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_3067799 : Nat := 118140960795 + 3067799 * 2 ^ 59
def prefixEnd_3067799 : Nat := 4983230072969 + 3 ^ 40 * 3067799 * 2
def baseEnd_3067799 : Nat := 1575255438382547956003955

theorem tailTrace_3067799 : CollatzResearch.WordTrace tailWord_3067799 prefixEnd_3067799 1575255438382547956003955 := by
  unfold tailWord_3067799
  simp only [CollatzResearch.WordTrace]
  refine ⟨111891821812895636201446451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74594547875263757467630967 111891821812895636201446451)
  ·
    refine ⟨167837732719343454302169677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111891821812895636201446451 167837732719343454302169677)
    ·
      refine ⟨62939149769753795363313629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167837732719343454302169677 62939149769753795363313629)
      ·
        refine ⟨23602181163657673261242611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62939149769753795363313629 23602181163657673261242611)
        ·
          refine ⟨35403271745486509891863917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23602181163657673261242611 35403271745486509891863917)
          ·
            refine ⟨13276226904557441209448969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35403271745486509891863917 13276226904557441209448969)
            ·
              refine ⟨9957170178418080907086727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13276226904557441209448969 9957170178418080907086727)
              ·
                refine ⟨14935755267627121360630091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9957170178418080907086727 14935755267627121360630091)
                ·
                  refine ⟨22403632901440682040945137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14935755267627121360630091 22403632901440682040945137)
                  ·
                    refine ⟨16802724676080511530708853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22403632901440682040945137 16802724676080511530708853)
                    ·
                      refine ⟨1575255438382547956003955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16802724676080511530708853 1575255438382547956003955)
                      ·
                        rfl

theorem cell23_3067799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_3067799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067799 prefixEnd_3067799 := by exact prefixLift 3067799
  have htrace : WordTrace (prefixWord ++ tailWord_3067799) baseStart_3067799 baseEnd_3067799 := by
    simpa [prefixWord, tailWord_3067799, baseEnd_3067799] using wordTrace_append hprefix tailTrace_3067799
  have hstable : (prefixWord ++ tailWord_3067799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067799).length < 2 ^ (prefixWord ++ tailWord_3067799).sum := by decide
  have hdescent : baseEnd_3067799 < baseStart_3067799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067896 : List Nat := [2, 1, 2, 1, 1, 3, 4, 3, 1, 5]
def baseStart_3067896 : Nat := 118140960795 + 3067896 * 2 ^ 59
def prefixEnd_3067896 : Nat := 4983230072969 + 3 ^ 40 * 3067896 * 2
def baseEnd_3067896 : Nat := 525101748668678025497003

theorem tailTrace_3067896 : CollatzResearch.WordTrace tailWord_3067896 prefixEnd_3067896 525101748668678025497003 := by
  unfold tailWord_3067896
  simp only [CollatzResearch.WordTrace]
  refine ⟨55947679846772110883863771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74596906462362814511818361 55947679846772110883863771)
  ·
    refine ⟨83921519770158166325795657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55947679846772110883863771 83921519770158166325795657)
    ·
      refine ⟨62941139827618624744346743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83921519770158166325795657 62941139827618624744346743)
      ·
        refine ⟨94411709741427937116520115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62941139827618624744346743 94411709741427937116520115)
        ·
          refine ⟨141617564612141905674780173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94411709741427937116520115 141617564612141905674780173)
          ·
            refine ⟨53106586729553214628042565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141617564612141905674780173 53106586729553214628042565)
            ·
              refine ⟨9957485011791227742757981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53106586729553214628042565 9957485011791227742757981)
              ·
                refine ⟨3734056879421710403534243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9957485011791227742757981 3734056879421710403534243)
                ·
                  refine ⟨5601085319132565605301365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3734056879421710403534243 5601085319132565605301365)
                  ·
                    refine ⟨525101748668678025497003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5601085319132565605301365 525101748668678025497003)
                    ·
                      rfl

theorem cell23_3067896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_3067896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067896 prefixEnd_3067896 := by exact prefixLift 3067896
  have htrace : WordTrace (prefixWord ++ tailWord_3067896) baseStart_3067896 baseEnd_3067896 := by
    simpa [prefixWord, tailWord_3067896, baseEnd_3067896] using wordTrace_append hprefix tailTrace_3067896
  have hstable : (prefixWord ++ tailWord_3067896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067896).length < 2 ^ (prefixWord ++ tailWord_3067896).sum := by decide
  have hdescent : baseEnd_3067896 < baseStart_3067896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067916 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 3, 1, 4]
def baseStart_3067916 : Nat := 118140960795 + 3067916 * 2 ^ 59
def prefixEnd_3067916 : Nat := 4983230072969 + 3 ^ 40 * 3067916 * 2
def baseEnd_3067916 : Nat := 1575315515619123998240917

theorem tailTrace_3067916 : CollatzResearch.WordTrace tailWord_3067916 prefixEnd_3067916 1575315515619123998240917 := by
  unfold tailWord_3067916
  simp only [CollatzResearch.WordTrace]
  refine ⟨55948044576735882591727801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74597392768981176788970401 55948044576735882591727801)
  ·
    refine ⟨41961033432551911943795851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55948044576735882591727801 41961033432551911943795851)
    ·
      refine ⟨62941550148827867915693777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41961033432551911943795851 62941550148827867915693777)
      ·
        refine ⟨47206162611620900936770333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62941550148827867915693777 47206162611620900936770333)
        ·
          refine ⟨17702310979357837851288875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47206162611620900936770333 17702310979357837851288875)
          ·
            refine ⟨26553466469036756776933313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17702310979357837851288875 26553466469036756776933313)
            ·
              refine ⟨19915099851777567582699985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26553466469036756776933313 19915099851777567582699985)
              ·
                refine ⟨14936324888833175687024989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19915099851777567582699985 14936324888833175687024989)
                ·
                  refine ⟨5601121833312440882634371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14936324888833175687024989 5601121833312440882634371)
                  ·
                    refine ⟨8401682749968661323951557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5601121833312440882634371 8401682749968661323951557)
                    ·
                      refine ⟨1575315515619123998240917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8401682749968661323951557 1575315515619123998240917)
                      ·
                        rfl

theorem cell23_3067916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_3067916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067916 prefixEnd_3067916 := by exact prefixLift 3067916
  have htrace : WordTrace (prefixWord ++ tailWord_3067916) baseStart_3067916 baseEnd_3067916 := by
    simpa [prefixWord, tailWord_3067916, baseEnd_3067916] using wordTrace_append hprefix tailTrace_3067916
  have hstable : (prefixWord ++ tailWord_3067916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067916).length < 2 ^ (prefixWord ++ tailWord_3067916).sum := by decide
  have hdescent : baseEnd_3067916 < baseStart_3067916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067917 : List Nat := [1, 7, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3067917 : Nat := 118140960795 + 3067917 * 2 ^ 59
def prefixEnd_3067917 : Nat := 4983230072969 + 3 ^ 40 * 3067917 * 2
def baseEnd_3067917 : Nat := 175035114344419832703157

theorem tailTrace_3067917 : CollatzResearch.WordTrace tailWord_3067917 prefixEnd_3067917 175035114344419832703157 := by
  unfold tailWord_3067917
  simp only [CollatzResearch.WordTrace]
  refine ⟨111896125626468142354242005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74597417084312094902828003 111896125626468142354242005)
  ·
    refine ⟨2622565444370347086427547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 111896125626468142354242005 2622565444370347086427547)
    ·
      refine ⟨3933848166555520629641321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2622565444370347086427547 3933848166555520629641321)
      ·
        refine ⟨2950386124916640472230991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3933848166555520629641321 2950386124916640472230991)
        ·
          refine ⟨4425579187374960708346487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2950386124916640472230991 4425579187374960708346487)
          ·
            refine ⟨6638368781062441062519731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4425579187374960708346487 6638368781062441062519731)
            ·
              refine ⟨9957553171593661593779597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6638368781062441062519731 9957553171593661593779597)
              ·
                refine ⟨3734082439347623097667349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9957553171593661593779597 3734082439347623097667349)
                ·
                  refine ⟨175035114344419832703157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3734082439347623097667349 175035114344419832703157)
                  ·
                    rfl

theorem cell23_3067917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3067917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067917 prefixEnd_3067917 := by exact prefixLift 3067917
  have htrace : WordTrace (prefixWord ++ tailWord_3067917) baseStart_3067917 baseEnd_3067917 := by
    simpa [prefixWord, tailWord_3067917, baseEnd_3067917] using wordTrace_append hprefix tailTrace_3067917
  have hstable : (prefixWord ++ tailWord_3067917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067917).length < 2 ^ (prefixWord ++ tailWord_3067917).sum := by decide
  have hdescent : baseEnd_3067917 < baseStart_3067917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067933 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_3067933 : Nat := 118140960795 + 3067933 * 2 ^ 59
def prefixEnd_3067933 : Nat := 4983230072969 + 3 ^ 40 * 3067933 * 2
def baseEnd_3067933 : Nat := 1575324244790250431728339

theorem tailTrace_3067933 : CollatzResearch.WordTrace tailWord_3067933 prefixEnd_3067933 1575324244790250431728339 := by
  unfold tailWord_3067933
  simp only [CollatzResearch.WordTrace]
  refine ⟨111896709194410177086824453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74597806129606784724549635 111896709194410177086824453)
  ·
    refine ⟨20980632973951908203779585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111896709194410177086824453 20980632973951908203779585)
    ·
      refine ⟨15735474730463931152834689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20980632973951908203779585 15735474730463931152834689)
      ·
        refine ⟨11801606047847948364626017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15735474730463931152834689 11801606047847948364626017)
        ·
          refine ⟨8851204535885961273469513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11801606047847948364626017 8851204535885961273469513)
          ·
            refine ⟨6638403401914470955102135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8851204535885961273469513 6638403401914470955102135)
            ·
              refine ⟨9957605102871706432653203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6638403401914470955102135 9957605102871706432653203)
              ·
                refine ⟨14936407654307559648979805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9957605102871706432653203 14936407654307559648979805)
                ·
                  refine ⟨5601152870365334868367427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14936407654307559648979805 5601152870365334868367427)
                  ·
                    refine ⟨8401729305548002302551141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5601152870365334868367427 8401729305548002302551141)
                    ·
                      refine ⟨1575324244790250431728339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8401729305548002302551141 1575324244790250431728339)
                      ·
                        rfl

theorem cell23_3067933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_3067933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067933 prefixEnd_3067933 := by exact prefixLift 3067933
  have htrace : WordTrace (prefixWord ++ tailWord_3067933) baseStart_3067933 baseEnd_3067933 := by
    simpa [prefixWord, tailWord_3067933, baseEnd_3067933] using wordTrace_append hprefix tailTrace_3067933
  have hstable : (prefixWord ++ tailWord_3067933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067933).length < 2 ^ (prefixWord ++ tailWord_3067933).sum := by decide
  have hdescent : baseEnd_3067933 < baseStart_3067933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067939 : List Nat := [1, 1, 1, 4, 3, 1, 1, 11]
def baseStart_3067939 : Nat := 118140960795 + 3067939 * 2 ^ 59
def prefixEnd_3067939 : Nat := 4983230072969 + 3 ^ 40 * 3067939 * 2
def baseEnd_3067939 : Nat := 58345456506451015120493

theorem tailTrace_3067939 : CollatzResearch.WordTrace tailWord_3067939 prefixEnd_3067939 58345456506451015120493 := by
  unfold tailWord_3067939
  simp only [CollatzResearch.WordTrace]
  refine ⟨111896928032388440111542871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74597952021592293407695247 111896928032388440111542871)
  ·
    refine ⟨167845392048582660167314307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111896928032388440111542871 167845392048582660167314307)
    ·
      refine ⟨251768088072873990250971461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167845392048582660167314307 251768088072873990250971461)
      ·
        refine ⟨47206516513663873172057149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251768088072873990250971461 47206516513663873172057149)
        ·
          refine ⟨17702443692623952439521431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47206516513663873172057149 17702443692623952439521431)
          ·
            refine ⟨26553665538935928659282147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17702443692623952439521431 26553665538935928659282147)
            ·
              refine ⟨39830498308403892988923221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26553665538935928659282147 39830498308403892988923221)
              ·
                refine ⟨58345456506451015120493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 39830498308403892988923221 58345456506451015120493)
                ·
                  rfl

theorem cell23_3067939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 11].length) (baseStart_3067939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067939 prefixEnd_3067939 := by exact prefixLift 3067939
  have htrace : WordTrace (prefixWord ++ tailWord_3067939) baseStart_3067939 baseEnd_3067939 := by
    simpa [prefixWord, tailWord_3067939, baseEnd_3067939] using wordTrace_append hprefix tailTrace_3067939
  have hstable : (prefixWord ++ tailWord_3067939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067939).length < 2 ^ (prefixWord ++ tailWord_3067939).sum := by decide
  have hdescent : baseEnd_3067939 < baseStart_3067939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067953 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 1, 1, 5]
def baseStart_3067953 : Nat := 118140960795 + 3067953 * 2 ^ 59
def prefixEnd_3067953 : Nat := 4983230072969 + 3 ^ 40 * 3067953 * 2
def baseEnd_3067953 : Nat := 1575334514403340353478247

theorem tailTrace_3067953 : CollatzResearch.WordTrace tailWord_3067953 prefixEnd_3067953 1575334514403340353478247 := by
  unfold tailWord_3067953
  simp only [CollatzResearch.WordTrace]
  refine ⟨111897438654337720502552513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74598292436225147001701675 111897438654337720502552513)
  ·
    refine ⟨83923078990753290376914385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111897438654337720502552513 83923078990753290376914385)
    ·
      refine ⟨62942309243064967782685789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83923078990753290376914385 62942309243064967782685789)
      ·
        refine ⟨23603365966149362918507171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62942309243064967782685789 23603365966149362918507171)
        ·
          refine ⟨35405048949224044377760757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23603365966149362918507171 35405048949224044377760757)
          ·
            refine ⟨3319223338989754160415071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35405048949224044377760757 3319223338989754160415071)
            ·
              refine ⟨4978835008484631240622607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3319223338989754160415071 4978835008484631240622607)
              ·
                refine ⟨7468252512726946860933911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4978835008484631240622607 7468252512726946860933911)
                ·
                  refine ⟨11202378769090420291400867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7468252512726946860933911 11202378769090420291400867)
                  ·
                    refine ⟨16803568153635630437101301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11202378769090420291400867 16803568153635630437101301)
                    ·
                      refine ⟨1575334514403340353478247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16803568153635630437101301 1575334514403340353478247)
                      ·
                        rfl

theorem cell23_3067953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_3067953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067953 prefixEnd_3067953 := by exact prefixLift 3067953
  have htrace : WordTrace (prefixWord ++ tailWord_3067953) baseStart_3067953 baseEnd_3067953 := by
    simpa [prefixWord, tailWord_3067953, baseEnd_3067953] using wordTrace_append hprefix tailTrace_3067953
  have hstable : (prefixWord ++ tailWord_3067953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067953).length < 2 ^ (prefixWord ++ tailWord_3067953).sum := by decide
  have hdescent : baseEnd_3067953 < baseStart_3067953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067956 : List Nat := [2, 5, 1, 2, 13]
def baseStart_3067956 : Nat := 118140960795 + 3067956 * 2 ^ 59
def prefixEnd_3067956 : Nat := 4983230072969 + 3 ^ 40 * 3067956 * 2
def baseEnd_3067956 : Nat := 2160954807743901017477

theorem tailTrace_3067956 : CollatzResearch.WordTrace tailWord_3067956 prefixEnd_3067956 2160954807743901017477 := by
  unfold tailWord_3067956
  simp only [CollatzResearch.WordTrace]
  refine ⟨55948774036663426007455861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74598365382217901343274481 55948774036663426007455861)
  ·
    refine ⟨5245197565937196188198987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55948774036663426007455861 5245197565937196188198987)
    ·
      refine ⟨7867796348905794282298481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5245197565937196188198987 7867796348905794282298481)
      ·
        refine ⟨5900847261679345711723861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7867796348905794282298481 5900847261679345711723861)
        ·
          refine ⟨2160954807743901017477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 5900847261679345711723861 2160954807743901017477)
          ·
            rfl

theorem cell23_3067956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 13].length) (baseStart_3067956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067956 prefixEnd_3067956 := by exact prefixLift 3067956
  have htrace : WordTrace (prefixWord ++ tailWord_3067956) baseStart_3067956 baseEnd_3067956 := by
    simpa [prefixWord, tailWord_3067956, baseEnd_3067956] using wordTrace_append hprefix tailTrace_3067956
  have hstable : (prefixWord ++ tailWord_3067956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067956).length < 2 ^ (prefixWord ++ tailWord_3067956).sum := by decide
  have hdescent : baseEnd_3067956 < baseStart_3067956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067960 : List Nat := [2, 1, 2, 1, 6, 1, 2, 2, 2, 4]
def baseStart_3067960 : Nat := 118140960795 + 3067960 * 2 ^ 59
def prefixEnd_3067960 : Nat := 4983230072969 + 3 ^ 40 * 3067960 * 2
def baseEnd_3067960 : Nat := 525112702922640608696905

theorem tailTrace_3067960 : CollatzResearch.WordTrace tailWord_3067960 prefixEnd_3067960 525112702922640608696905 := by
  unfold tailWord_3067960
  simp only [CollatzResearch.WordTrace]
  refine ⟨55948846982656180349028667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74598462643541573798704889 55948846982656180349028667)
  ·
    refine ⟨83923270473984270523543001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55948846982656180349028667 83923270473984270523543001)
    ·
      refine ⟨62942452855488202892657251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83923270473984270523543001 62942452855488202892657251)
      ·
        refine ⟨94413679283232304338985877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62942452855488202892657251 94413679283232304338985877)
        ·
          refine ⟨4425641216401514265889963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94413679283232304338985877 4425641216401514265889963)
          ·
            refine ⟨6638461824602271398834945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4425641216401514265889963 6638461824602271398834945)
            ·
              refine ⟨4978846368451703549126209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6638461824602271398834945 4978846368451703549126209)
              ·
                refine ⟨3734134776338777661844657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4978846368451703549126209 3734134776338777661844657)
                ·
                  refine ⟨2800601082254083246383493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3734134776338777661844657 2800601082254083246383493)
                  ·
                    refine ⟨525112702922640608696905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2800601082254083246383493 525112702922640608696905)
                    ·
                      rfl

theorem cell23_3067960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_3067960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067960 prefixEnd_3067960 := by exact prefixLift 3067960
  have htrace : WordTrace (prefixWord ++ tailWord_3067960) baseStart_3067960 baseEnd_3067960 := by
    simpa [prefixWord, tailWord_3067960, baseEnd_3067960] using wordTrace_append hprefix tailTrace_3067960
  have hstable : (prefixWord ++ tailWord_3067960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067960).length < 2 ^ (prefixWord ++ tailWord_3067960).sum := by decide
  have hdescent : baseEnd_3067960 < baseStart_3067960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067961 : List Nat := [1, 2, 1, 5, 4, 1, 2, 2, 1, 1, 3]
def baseStart_3067961 : Nat := 118140960795 + 3067961 * 2 ^ 59
def prefixEnd_3067961 : Nat := 4983230072969 + 3 ^ 40 * 3067961 * 2
def baseEnd_3067961 : Nat := 1575338622248576322178211

theorem tailTrace_3067961 : CollatzResearch.WordTrace tailWord_3067961 prefixEnd_3067961 1575338622248576322178211 := by
  unfold tailWord_3067961
  simp only [CollatzResearch.WordTrace]
  refine ⟨111897730438308737868843737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74598486958872491912562491 111897730438308737868843737)
  ·
    refine ⟨83923297828731553401632803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111897730438308737868843737 83923297828731553401632803)
    ·
      refine ⟨125884946743097330102449205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83923297828731553401632803 125884946743097330102449205)
      ·
        refine ⟨11801713757165374697104613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125884946743097330102449205 11801713757165374697104613)
        ·
          refine ⟨2212821329468507755707115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11801713757165374697104613 2212821329468507755707115)
          ·
            refine ⟨3319231994202761633560673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212821329468507755707115 3319231994202761633560673)
            ·
              refine ⟨2489423995652071225170505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3319231994202761633560673 2489423995652071225170505)
              ·
                refine ⟨1867067996739053418877879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2489423995652071225170505 1867067996739053418877879)
                ·
                  refine ⟨2800601995108580128316819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1867067996739053418877879 2800601995108580128316819)
                  ·
                    refine ⟨4200902992662870192475229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2800601995108580128316819 4200902992662870192475229)
                    ·
                      refine ⟨1575338622248576322178211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4200902992662870192475229 1575338622248576322178211)
                      ·
                        rfl

theorem cell23_3067961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_3067961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067961 prefixEnd_3067961 := by exact prefixLift 3067961
  have htrace : WordTrace (prefixWord ++ tailWord_3067961) baseStart_3067961 baseEnd_3067961 := by
    simpa [prefixWord, tailWord_3067961, baseEnd_3067961] using wordTrace_append hprefix tailTrace_3067961
  have hstable : (prefixWord ++ tailWord_3067961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067961).length < 2 ^ (prefixWord ++ tailWord_3067961).sum := by decide
  have hdescent : baseEnd_3067961 < baseStart_3067961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3067993 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 3, 3, 2]
def baseStart_3067993 : Nat := 118140960795 + 3067993 * 2 ^ 59
def prefixEnd_3067993 : Nat := 4983230072969 + 3 ^ 40 * 3067993 * 2
def baseEnd_3067993 : Nat := 1575355053629520196978063

theorem tailTrace_3067993 : CollatzResearch.WordTrace tailWord_3067993 prefixEnd_3067993 1575355053629520196978063 := by
  unfold tailWord_3067993
  simp only [CollatzResearch.WordTrace]
  refine ⟨111898897574192807334008633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74599265049461871556005755 111898897574192807334008633)
  ·
    refine ⟨83924173180644605500506475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111898897574192807334008633 83924173180644605500506475)
    ·
      refine ⟨125886259770966908250759713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83924173180644605500506475 125886259770966908250759713)
      ·
        refine ⟨94414694828225181188069785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125886259770966908250759713 94414694828225181188069785)
        ·
          refine ⟨70811021121168885891052339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94414694828225181188069785 70811021121168885891052339)
          ·
            refine ⟨106216531681753328836578509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70811021121168885891052339 106216531681753328836578509)
            ·
              refine ⟨39831199380657498313716941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106216531681753328836578509 39831199380657498313716941)
              ·
                refine ⟨14936699767746561867643853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39831199380657498313716941 14936699767746561867643853)
                ·
                  refine ⟨5601262412904960700366445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14936699767746561867643853 5601262412904960700366445)
                  ·
                    refine ⟨2100473404839360262637417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5601262412904960700366445 2100473404839360262637417)
                    ·
                      refine ⟨1575355053629520196978063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2100473404839360262637417 1575355053629520196978063)
                      ·
                        rfl

theorem cell23_3067993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 3, 2].length) (baseStart_3067993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3067993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3067993 prefixEnd_3067993 := by exact prefixLift 3067993
  have htrace : WordTrace (prefixWord ++ tailWord_3067993) baseStart_3067993 baseEnd_3067993 := by
    simpa [prefixWord, tailWord_3067993, baseEnd_3067993] using wordTrace_append hprefix tailTrace_3067993
  have hstable : (prefixWord ++ tailWord_3067993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3067993).length < 2 ^ (prefixWord ++ tailWord_3067993).sum := by decide
  have hdescent : baseEnd_3067993 < baseStart_3067993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3067993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068016 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 2, 6]
def baseStart_3068016 : Nat := 118140960795 + 3068016 * 2 ^ 59
def prefixEnd_3068016 : Nat := 4983230072969 + 3 ^ 40 * 3068016 * 2
def baseEnd_3068016 : Nat := 525122287894857868996819

theorem tailTrace_3068016 : CollatzResearch.WordTrace tailWord_3068016 prefixEnd_3068016 525122287894857868996819 := by
  unfold tailWord_3068016
  simp only [CollatzResearch.WordTrace]
  refine ⟨55949868226554741131047951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74599824302072988174730601 55949868226554741131047951)
  ·
    refine ⟨83924802339832111696571927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55949868226554741131047951 83924802339832111696571927)
    ·
      refine ⟨125887203509748167544857891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83924802339832111696571927 125887203509748167544857891)
      ·
        refine ⟨188830805264622251317286837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125887203509748167544857891 188830805264622251317286837)
        ·
          refine ⟨17702887993558336060995641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188830805264622251317286837 17702887993558336060995641)
          ·
            refine ⟨13277165995168752045746731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17702887993558336060995641 13277165995168752045746731)
            ·
              refine ⟨19915748992753128068620097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13277165995168752045746731 19915748992753128068620097)
              ·
                refine ⟨14936811744564846051465073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19915748992753128068620097 14936811744564846051465073)
                ·
                  refine ⟨11202608808423634538598805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14936811744564846051465073 11202608808423634538598805)
                  ·
                    refine ⟨525122287894857868996819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11202608808423634538598805 525122287894857868996819)
                    ·
                      rfl

theorem cell23_3068016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2, 6].length) (baseStart_3068016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068016 prefixEnd_3068016 := by exact prefixLift 3068016
  have htrace : WordTrace (prefixWord ++ tailWord_3068016) baseStart_3068016 baseEnd_3068016 := by
    simpa [prefixWord, tailWord_3068016, baseEnd_3068016] using wordTrace_append hprefix tailTrace_3068016
  have hstable : (prefixWord ++ tailWord_3068016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068016).length < 2 ^ (prefixWord ++ tailWord_3068016).sum := by decide
  have hdescent : baseEnd_3068016 < baseStart_3068016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068083 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 2, 5, 2]
def baseStart_3068083 : Nat := 118140960795 + 3068083 * 2 ^ 59
def prefixEnd_3068083 : Nat := 4983230072969 + 3 ^ 40 * 3068083 * 2
def baseEnd_3068083 : Nat := 1575401266888424844852649

theorem tailTrace_3068083 : CollatzResearch.WordTrace tailWord_3068083 prefixEnd_3068083 1575401266888424844852649 := by
  unfold tailWord_3068083
  simp only [CollatzResearch.WordTrace]
  refine ⟨111902180143866752704784903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74601453429244501803189935 111902180143866752704784903)
  ·
    refine ⟨167853270215800129057177355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111902180143866752704784903 167853270215800129057177355)
    ·
      refine ⟨251779905323700193585766033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167853270215800129057177355 251779905323700193585766033)
      ·
        refine ⟨188834928992775145189324525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251779905323700193585766033 188834928992775145189324525)
        ·
          refine ⟨70813098372290679445996697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188834928992775145189324525 70813098372290679445996697)
          ·
            refine ⟨53109823779218009584497523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70813098372290679445996697 53109823779218009584497523)
            ·
              refine ⟨79664735668827014376746285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53109823779218009584497523 79664735668827014376746285)
              ·
                refine ⟨29874275875810130391279857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79664735668827014376746285 29874275875810130391279857)
                ·
                  refine ⟨22405706906857597793459893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29874275875810130391279857 22405706906857597793459893)
                  ·
                    refine ⟨2100535022517899793136865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22405706906857597793459893 2100535022517899793136865)
                    ·
                      refine ⟨1575401266888424844852649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2100535022517899793136865 1575401266888424844852649)
                      ·
                        rfl

theorem cell23_3068083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 5, 2].length) (baseStart_3068083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068083 prefixEnd_3068083 := by exact prefixLift 3068083
  have htrace : WordTrace (prefixWord ++ tailWord_3068083) baseStart_3068083 baseEnd_3068083 := by
    simpa [prefixWord, tailWord_3068083, baseEnd_3068083] using wordTrace_append hprefix tailTrace_3068083
  have hstable : (prefixWord ++ tailWord_3068083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068083).length < 2 ^ (prefixWord ++ tailWord_3068083).sum := by decide
  have hdescent : baseEnd_3068083 < baseStart_3068083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068110 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_3068110 : Nat := 118140960795 + 3068110 * 2 ^ 59
def prefixEnd_3068110 : Nat := 4983230072969 + 3 ^ 40 * 3068110 * 2
def baseEnd_3068110 : Nat := 525138376955365413071675

theorem tailTrace_3068110 : CollatzResearch.WordTrace tailWord_3068110 prefixEnd_3068110 525138376955365413071675 := by
  unfold tailWord_3068110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13987895614346117039502223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74602109943179290877345189 13987895614346117039502223)
  ·
    refine ⟨20981843421519175559253335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13987895614346117039502223 20981843421519175559253335)
    ·
      refine ⟨31472765132278763338880003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20981843421519175559253335 31472765132278763338880003)
      ·
        refine ⟨47209147698418145008320005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31472765132278763338880003 47209147698418145008320005)
        ·
          refine ⟨8851715193453402189060001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47209147698418145008320005 8851715193453402189060001)
          ·
            refine ⟨6638786395090051641795001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8851715193453402189060001 6638786395090051641795001)
            ·
              refine ⟨4979089796317538731346251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6638786395090051641795001 4979089796317538731346251)
              ·
                refine ⟨7468634694476308097019377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4979089796317538731346251 7468634694476308097019377)
                ·
                  refine ⟨5601476020857231072764533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7468634694476308097019377 5601476020857231072764533)
                  ·
                    refine ⟨525138376955365413071675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5601476020857231072764533 525138376955365413071675)
                    ·
                      rfl

theorem cell23_3068110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_3068110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068110 prefixEnd_3068110 := by exact prefixLift 3068110
  have htrace : WordTrace (prefixWord ++ tailWord_3068110) baseStart_3068110 baseEnd_3068110 := by
    simpa [prefixWord, tailWord_3068110, baseEnd_3068110] using wordTrace_append hprefix tailTrace_3068110
  have hstable : (prefixWord ++ tailWord_3068110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068110).length < 2 ^ (prefixWord ++ tailWord_3068110).sum := by decide
  have hdescent : baseEnd_3068110 < baseStart_3068110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068113 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 2, 1, 4]
def baseStart_3068113 : Nat := 118140960795 + 3068113 * 2 ^ 59
def prefixEnd_3068113 : Nat := 4983230072969 + 3 ^ 40 * 3068113 * 2
def baseEnd_3068113 : Nat := 1575416671308059727477511

theorem tailTrace_3068113 : CollatzResearch.WordTrace tailWord_3068113 prefixEnd_3068113 1575416671308059727477511 := by
  unfold tailWord_3068113
  simp only [CollatzResearch.WordTrace]
  refine ⟨111903274333758067828376993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74602182889172045218917995 111903274333758067828376993)
  ·
    refine ⟨83927455750318550871282745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111903274333758067828376993 83927455750318550871282745)
    ·
      refine ⟨62945591812738913153462059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83927455750318550871282745 62945591812738913153462059)
      ·
        refine ⟨94418387719108369730193089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62945591812738913153462059 94418387719108369730193089)
        ·
          refine ⟨70813790789331277297644817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94418387719108369730193089 70813790789331277297644817)
          ·
            refine ⟨53110343091998457973233613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70813790789331277297644817 53110343091998457973233613)
            ·
              refine ⟨19916378659499421739962605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53110343091998457973233613 19916378659499421739962605)
              ·
                refine ⟨7468641997312283152485977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19916378659499421739962605 7468641997312283152485977)
                ·
                  refine ⟨5601481497984212364364483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7468641997312283152485977 5601481497984212364364483)
                  ·
                    refine ⟨8402222246976318546546725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5601481497984212364364483 8402222246976318546546725)
                    ·
                      refine ⟨1575416671308059727477511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8402222246976318546546725 1575416671308059727477511)
                      ·
                        rfl

theorem cell23_3068113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_3068113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068113 prefixEnd_3068113 := by exact prefixLift 3068113
  have htrace : WordTrace (prefixWord ++ tailWord_3068113) baseStart_3068113 baseEnd_3068113 := by
    simpa [prefixWord, tailWord_3068113, baseEnd_3068113] using wordTrace_append hprefix tailTrace_3068113
  have hstable : (prefixWord ++ tailWord_3068113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068113).length < 2 ^ (prefixWord ++ tailWord_3068113).sum := by decide
  have hdescent : baseEnd_3068113 < baseStart_3068113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068131 : List Nat := [1, 1, 1, 8, 2, 1, 2, 2, 5]
def baseStart_3068131 : Nat := 118140960795 + 3068131 * 2 ^ 59
def prefixEnd_3068131 : Nat := 4983230072969 + 3 ^ 40 * 3068131 * 2
def baseEnd_3068131 : Nat := 175047323773315628561381

theorem tailTrace_3068131 : CollatzResearch.WordTrace tailWord_3068131 prefixEnd_3068131 175047323773315628561381 := by
  unfold tailWord_3068131
  simp only [CollatzResearch.WordTrace]
  refine ⟨111903930847692856902532247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74602620565128571268354831 111903930847692856902532247)
  ·
    refine ⟨167855896271539285353798371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111903930847692856902532247 167855896271539285353798371)
    ·
      refine ⟨251783844407308928030697557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167855896271539285353798371 251783844407308928030697557)
      ·
        refine ⟨2950591926648151500359737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 251783844407308928030697557 2950591926648151500359737)
        ·
          refine ⟨2212943944986113625269803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2950591926648151500359737 2212943944986113625269803)
          ·
            refine ⟨3319415917479170437904705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212943944986113625269803 3319415917479170437904705)
            ·
              refine ⟨2489561938109377828428529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3319415917479170437904705 2489561938109377828428529)
              ·
                refine ⟨1867171453582033371321397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2489561938109377828428529 1867171453582033371321397)
                ·
                  refine ⟨175047323773315628561381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1867171453582033371321397 175047323773315628561381)
                  ·
                    rfl

theorem cell23_3068131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 5].length) (baseStart_3068131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068131 prefixEnd_3068131 := by exact prefixLift 3068131
  have htrace : WordTrace (prefixWord ++ tailWord_3068131) baseStart_3068131 baseEnd_3068131 := by
    simpa [prefixWord, tailWord_3068131, baseEnd_3068131] using wordTrace_append hprefix tailTrace_3068131
  have hstable : (prefixWord ++ tailWord_3068131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068131).length < 2 ^ (prefixWord ++ tailWord_3068131).sum := by decide
  have hdescent : baseEnd_3068131 < baseStart_3068131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068150 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_3068150 : Nat := 118140960795 + 3068150 * 2 ^ 59
def prefixEnd_3068150 : Nat := 4983230072969 + 3 ^ 40 * 3068150 * 2
def baseEnd_3068150 : Nat := 1575435670092276082714841

theorem tailTrace_3068150 : CollatzResearch.WordTrace tailWord_3068150 prefixEnd_3068150 1575435670092276082714841 := by
  unfold tailWord_3068150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6994038989664001446717119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74603082556416015431649269 6994038989664001446717119)
  ·
    refine ⟨10491058484496002170075679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6994038989664001446717119 10491058484496002170075679)
    ·
      refine ⟨15736587726744003255113519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10491058484496002170075679 15736587726744003255113519)
      ·
        refine ⟨23604881590116004882670279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15736587726744003255113519 23604881590116004882670279)
        ·
          refine ⟨35407322385174007324005419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23604881590116004882670279 35407322385174007324005419)
          ·
            refine ⟨53110983577761010986008129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35407322385174007324005419 53110983577761010986008129)
            ·
              refine ⟨39833237683320758239506097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53110983577761010986008129 39833237683320758239506097)
              ·
                refine ⟨29874928262490568679629573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39833237683320758239506097 29874928262490568679629573)
                ·
                  refine ⟨5601549049216981627430545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29874928262490568679629573 5601549049216981627430545)
                  ·
                    refine ⟨4201161786912736220572909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5601549049216981627430545 4201161786912736220572909)
                    ·
                      refine ⟨1575435670092276082714841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4201161786912736220572909 1575435670092276082714841)
                      ·
                        rfl

theorem cell23_3068150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_3068150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068150 prefixEnd_3068150 := by exact prefixLift 3068150
  have htrace : WordTrace (prefixWord ++ tailWord_3068150) baseStart_3068150 baseEnd_3068150 := by
    simpa [prefixWord, tailWord_3068150, baseEnd_3068150] using wordTrace_append hprefix tailTrace_3068150
  have hstable : (prefixWord ++ tailWord_3068150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068150).length < 2 ^ (prefixWord ++ tailWord_3068150).sum := by decide
  have hdescent : baseEnd_3068150 < baseStart_3068150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068164 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_3068164 : Nat := 118140960795 + 3068164 * 2 ^ 59
def prefixEnd_3068164 : Nat := 4983230072969 + 3 ^ 40 * 3068164 * 2
def baseEnd_3068164 : Nat := 1575442858821439027939777

theorem tailTrace_3068164 : CollatzResearch.WordTrace tailWord_3068164 prefixEnd_3068164 1575442858821439027939777 := by
  unfold tailWord_3068164
  simp only [CollatzResearch.WordTrace]
  refine ⟨55952567228286651769241773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74603422971048869025655697 55952567228286651769241773)
  ·
    refine ⟨20982212710607494413465665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55952567228286651769241773 20982212710607494413465665)
    ·
      refine ⟨15736659532955620810099249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20982212710607494413465665 15736659532955620810099249)
      ·
        refine ⟨11802494649716715607574437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15736659532955620810099249 11802494649716715607574437)
        ·
          refine ⟨2212967746821884176420207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11802494649716715607574437 2212967746821884176420207)
          ·
            refine ⟨3319451620232826264630311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212967746821884176420207 3319451620232826264630311)
            ·
              refine ⟨4979177430349239396945467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3319451620232826264630311 4979177430349239396945467)
              ·
                refine ⟨7468766145523859095418201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4979177430349239396945467 7468766145523859095418201)
                ·
                  refine ⟨5601574609142894321563651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7468766145523859095418201 5601574609142894321563651)
                  ·
                    refine ⟨8402361913714341482345477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5601574609142894321563651 8402361913714341482345477)
                    ·
                      refine ⟨1575442858821439027939777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8402361913714341482345477 1575442858821439027939777)
                      ·
                        rfl

theorem cell23_3068164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_3068164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068164 prefixEnd_3068164 := by exact prefixLift 3068164
  have htrace : WordTrace (prefixWord ++ tailWord_3068164) baseStart_3068164 baseEnd_3068164 := by
    simpa [prefixWord, tailWord_3068164, baseEnd_3068164] using wordTrace_append hprefix tailTrace_3068164
  have hstable : (prefixWord ++ tailWord_3068164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068164).length < 2 ^ (prefixWord ++ tailWord_3068164).sum := by decide
  have hdescent : baseEnd_3068164 < baseStart_3068164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068167 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3068167 : Nat := 118140960795 + 3068167 * 2 ^ 59
def prefixEnd_3068167 : Nat := 4983230072969 + 3 ^ 40 * 3068167 * 2
def baseEnd_3068167 : Nat := 1575444399263402516202263

theorem tailTrace_3068167 : CollatzResearch.WordTrace tailWord_3068167 prefixEnd_3068167 1575444399263402516202263 := by
  unfold tailWord_3068167
  simp only [CollatzResearch.WordTrace]
  refine ⟨111905243875562435050842755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74603495917041623367228503 111905243875562435050842755)
  ·
    refine ⟨167857865813343652576264133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111905243875562435050842755 167857865813343652576264133)
    ·
      refine ⟨31473349840001934858049525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167857865813343652576264133 31473349840001934858049525)
      ·
        refine ⟨2950626547500181392942143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31473349840001934858049525 2950626547500181392942143)
        ·
          refine ⟨4425939821250272089413215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2950626547500181392942143 4425939821250272089413215)
          ·
            refine ⟨6638909731875408134119823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4425939821250272089413215 6638909731875408134119823)
            ·
              refine ⟨9958364597813112201179735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6638909731875408134119823 9958364597813112201179735)
              ·
                refine ⟨14937546896719668301769603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9958364597813112201179735 14937546896719668301769603)
                ·
                  refine ⟨22406320345079502452654405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14937546896719668301769603 22406320345079502452654405)
                  ·
                    refine ⟨4201185064702406709872701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22406320345079502452654405 4201185064702406709872701)
                    ·
                      refine ⟨1575444399263402516202263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4201185064702406709872701 1575444399263402516202263)
                      ·
                        rfl

theorem cell23_3068167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3068167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068167 prefixEnd_3068167 := by exact prefixLift 3068167
  have htrace : WordTrace (prefixWord ++ tailWord_3068167) baseStart_3068167 baseEnd_3068167 := by
    simpa [prefixWord, tailWord_3068167, baseEnd_3068167] using wordTrace_append hprefix tailTrace_3068167
  have hstable : (prefixWord ++ tailWord_3068167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068167).length < 2 ^ (prefixWord ++ tailWord_3068167).sum := by decide
  have hdescent : baseEnd_3068167 < baseStart_3068167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068217 : List Nat := [1, 2, 1, 6, 1, 2, 2, 2, 1, 5]
def baseStart_3068217 : Nat := 118140960795 + 3068217 * 2 ^ 59
def prefixEnd_3068217 : Nat := 4983230072969 + 3 ^ 40 * 3068217 * 2
def baseEnd_3068217 : Nat := 525156691098709106859011

theorem tailTrace_3068217 : CollatzResearch.WordTrace tailWord_3068217 prefixEnd_3068217 525156691098709106859011 := by
  unfold tailWord_3068217
  simp only [CollatzResearch.WordTrace]
  refine ⟨111907067525381293590162905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74604711683587529060108603 111907067525381293590162905)
  ·
    refine ⟨83930300644035970192622179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111907067525381293590162905 83930300644035970192622179)
    ·
      refine ⟨125895450966053955288933269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83930300644035970192622179 125895450966053955288933269)
      ·
        refine ⟨5901349264033779154168747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125895450966053955288933269 5901349264033779154168747)
        ·
          refine ⟨8852023896050668731253121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5901349264033779154168747 8852023896050668731253121)
          ·
            refine ⟨6639017922038001548439841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8852023896050668731253121 6639017922038001548439841)
            ·
              refine ⟨4979263441528501161329881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6639017922038001548439841 4979263441528501161329881)
              ·
                refine ⟨3734447581146375870997411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4979263441528501161329881 3734447581146375870997411)
                ·
                  refine ⟨5601671371719563806496117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3734447581146375870997411 5601671371719563806496117)
                  ·
                    refine ⟨525156691098709106859011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5601671371719563806496117 525156691098709106859011)
                    ·
                      rfl

theorem cell23_3068217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 5].length) (baseStart_3068217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068217 prefixEnd_3068217 := by exact prefixLift 3068217
  have htrace : WordTrace (prefixWord ++ tailWord_3068217) baseStart_3068217 baseEnd_3068217 := by
    simpa [prefixWord, tailWord_3068217, baseEnd_3068217] using wordTrace_append hprefix tailTrace_3068217
  have hstable : (prefixWord ++ tailWord_3068217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068217).length < 2 ^ (prefixWord ++ tailWord_3068217).sum := by decide
  have hdescent : baseEnd_3068217 < baseStart_3068217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068220 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 2, 6, 2]
def baseStart_3068220 : Nat := 118140960795 + 3068220 * 2 ^ 59
def prefixEnd_3068220 : Nat := 4983230072969 + 3 ^ 40 * 3068220 * 2
def baseEnd_3068220 : Nat := 1575471613738090808839519

theorem tailTrace_3068220 : CollatzResearch.WordTrace tailWord_3068220 prefixEnd_3068220 1575471613738090808839519 := by
  unfold tailWord_3068220
  simp only [CollatzResearch.WordTrace]
  refine ⟨55953588472185212551261057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74604784629580283401681409 55953588472185212551261057)
  ·
    refine ⟨41965191354138909413445793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55953588472185212551261057 41965191354138909413445793)
    ·
      refine ⟨31473893515604182060084345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41965191354138909413445793 31473893515604182060084345)
      ·
        refine ⟨23605420136703136545063259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31473893515604182060084345 23605420136703136545063259)
        ·
          refine ⟨35408130205054704817594889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23605420136703136545063259 35408130205054704817594889)
          ·
            refine ⟨26556097653791028613196167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35408130205054704817594889 26556097653791028613196167)
            ·
              refine ⟨39834146480686542919794251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26556097653791028613196167 39834146480686542919794251)
              ·
                refine ⟨59751219721029814379691377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39834146480686542919794251 59751219721029814379691377)
                ·
                  refine ⟨44813414790772360784768533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59751219721029814379691377 44813414790772360784768533)
                  ·
                    refine ⟨2100628818317454411786025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44813414790772360784768533 2100628818317454411786025)
                    ·
                      refine ⟨1575471613738090808839519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2100628818317454411786025 1575471613738090808839519)
                      ·
                        rfl

theorem cell23_3068220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_3068220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068220 prefixEnd_3068220 := by exact prefixLift 3068220
  have htrace : WordTrace (prefixWord ++ tailWord_3068220) baseStart_3068220 baseEnd_3068220 := by
    simpa [prefixWord, tailWord_3068220, baseEnd_3068220] using wordTrace_append hprefix tailTrace_3068220
  have hstable : (prefixWord ++ tailWord_3068220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068220).length < 2 ^ (prefixWord ++ tailWord_3068220).sum := by decide
  have hdescent : baseEnd_3068220 < baseStart_3068220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068223 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 5]
def baseStart_3068223 : Nat := 118140960795 + 3068223 * 2 ^ 59
def prefixEnd_3068223 : Nat := 4983230072969 + 3 ^ 40 * 3068223 * 2
def baseEnd_3068223 : Nat := 1575473154180054297102005

theorem tailTrace_3068223 : CollatzResearch.WordTrace tailWord_3068223 prefixEnd_3068223 1575473154180054297102005 := by
  unfold tailWord_3068223
  simp only [CollatzResearch.WordTrace]
  refine ⟨111907286363359556614881323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74604857575573037743254215 111907286363359556614881323)
  ·
    refine ⟨167860929545039334922321985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111907286363359556614881323 167860929545039334922321985)
    ·
      refine ⟨125895697158779501191741489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167860929545039334922321985 125895697158779501191741489)
      ·
        refine ⟨94421772869084625893806117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125895697158779501191741489 94421772869084625893806117)
        ·
          refine ⟨17704082412953367355088647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94421772869084625893806117 17704082412953367355088647)
          ·
            refine ⟨26556123619430051032632971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17704082412953367355088647 26556123619430051032632971)
            ·
              refine ⟨39834185429145076548949457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26556123619430051032632971 39834185429145076548949457)
              ·
                refine ⟨29875639071858807411712093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39834185429145076548949457 29875639071858807411712093)
                ·
                  refine ⟨11203364651947052779392035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29875639071858807411712093 11203364651947052779392035)
                  ·
                    refine ⟨16805046977920579169088053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11203364651947052779392035 16805046977920579169088053)
                    ·
                      refine ⟨1575473154180054297102005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16805046977920579169088053 1575473154180054297102005)
                      ·
                        rfl

theorem cell23_3068223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_3068223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068223 prefixEnd_3068223 := by exact prefixLift 3068223
  have htrace : WordTrace (prefixWord ++ tailWord_3068223) baseStart_3068223 baseEnd_3068223 := by
    simpa [prefixWord, tailWord_3068223, baseEnd_3068223] using wordTrace_append hprefix tailTrace_3068223
  have hstable : (prefixWord ++ tailWord_3068223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068223).length < 2 ^ (prefixWord ++ tailWord_3068223).sum := by decide
  have hdescent : baseEnd_3068223 < baseStart_3068223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068233 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 3, 2, 4]
def baseStart_3068233 : Nat := 118140960795 + 3068233 * 2 ^ 59
def prefixEnd_3068233 : Nat := 4983230072969 + 3 ^ 40 * 3068233 * 2
def baseEnd_3068233 : Nat := 1575478288986599257976959

theorem tailTrace_3068233 : CollatzResearch.WordTrace tailWord_3068233 prefixEnd_3068233 1575478288986599257976959 := by
  unfold tailWord_3068233
  simp only [CollatzResearch.WordTrace]
  refine ⟨111907651093323328322745353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74605100728882218881830235 111907651093323328322745353)
  ·
    refine ⟨83930738319992496242059015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111907651093323328322745353 83930738319992496242059015)
    ·
      refine ⟨125896107479988744363088523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83930738319992496242059015 125896107479988744363088523)
      ·
        refine ⟨188844161219983116544632785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125896107479988744363088523 188844161219983116544632785)
        ·
          refine ⟨141633120914987337408474589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188844161219983116544632785 141633120914987337408474589)
          ·
            refine ⟨53112420343120251528177971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141633120914987337408474589 53112420343120251528177971)
            ·
              refine ⟨79668630514680377292266957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53112420343120251528177971 79668630514680377292266957)
              ·
                refine ⟨29875736443005141484600109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79668630514680377292266957 29875736443005141484600109)
                ·
                  refine ⟨11203401166126928056725041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29875736443005141484600109 11203401166126928056725041)
                  ·
                    refine ⟨8402550874595196042543781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11203401166126928056725041 8402550874595196042543781)
                    ·
                      refine ⟨1575478288986599257976959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8402550874595196042543781 1575478288986599257976959)
                      ·
                        rfl

theorem cell23_3068233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_3068233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068233 prefixEnd_3068233 := by exact prefixLift 3068233
  have htrace : WordTrace (prefixWord ++ tailWord_3068233) baseStart_3068233 baseEnd_3068233 := by
    simpa [prefixWord, tailWord_3068233, baseEnd_3068233] using wordTrace_append hprefix tailTrace_3068233
  have hstable : (prefixWord ++ tailWord_3068233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068233).length < 2 ^ (prefixWord ++ tailWord_3068233).sum := by decide
  have hdescent : baseEnd_3068233 < baseStart_3068233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068240 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 5]
def baseStart_3068240 : Nat := 118140960795 + 3068240 * 2 ^ 59
def prefixEnd_3068240 : Nat := 4983230072969 + 3 ^ 40 * 3068240 * 2
def baseEnd_3068240 : Nat := 1575481883351180730589427

theorem tailTrace_3068240 : CollatzResearch.WordTrace tailWord_3068240 prefixEnd_3068240 1575481883351180730589427 := by
  unfold tailWord_3068240
  simp only [CollatzResearch.WordTrace]
  refine ⟨55953953202148984259125087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74605270936198645678833449 55953953202148984259125087)
  ·
    refine ⟨83930929803223476388687631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55953953202148984259125087 83930929803223476388687631)
    ·
      refine ⟨125896394704835214583031447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83930929803223476388687631 125896394704835214583031447)
      ·
        refine ⟨188844592057252821874547171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125896394704835214583031447 188844592057252821874547171)
        ·
          refine ⟨283266888085879232811820757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188844592057252821874547171 283266888085879232811820757)
          ·
            refine ⟨6639067689512794519027049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 283266888085879232811820757 6639067689512794519027049)
            ·
              refine ⟨4979300767134595889270287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6639067689512794519027049 4979300767134595889270287)
              ·
                refine ⟨7468951150701893833905431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4979300767134595889270287 7468951150701893833905431)
                ·
                  refine ⟨11203426726052840750858147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7468951150701893833905431 11203426726052840750858147)
                  ·
                    refine ⟨16805140089079261126287221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11203426726052840750858147 16805140089079261126287221)
                    ·
                      refine ⟨1575481883351180730589427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16805140089079261126287221 1575481883351180730589427)
                      ·
                        rfl

theorem cell23_3068240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 5].length) (baseStart_3068240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068240 prefixEnd_3068240 := by exact prefixLift 3068240
  have htrace : WordTrace (prefixWord ++ tailWord_3068240) baseStart_3068240 baseEnd_3068240 := by
    simpa [prefixWord, tailWord_3068240, baseEnd_3068240] using wordTrace_append hprefix tailTrace_3068240
  have hstable : (prefixWord ++ tailWord_3068240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068240).length < 2 ^ (prefixWord ++ tailWord_3068240).sum := by decide
  have hdescent : baseEnd_3068240 < baseStart_3068240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068264 : List Nat := [2, 1, 4, 2, 2, 1, 4, 1, 2, 4]
def baseStart_3068264 : Nat := 118140960795 + 3068264 * 2 ^ 59
def prefixEnd_3068264 : Nat := 4983230072969 + 3 ^ 40 * 3068264 * 2
def baseEnd_3068264 : Nat := 525164735628962878896439

theorem tailTrace_3068264 : CollatzResearch.WordTrace tailWord_3068264 prefixEnd_3068264 525164735628962878896439 := by
  unfold tailWord_3068264
  simp only [CollatzResearch.WordTrace]
  refine ⟨55954390878105510308561923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74605854504140680411415897 55954390878105510308561923)
  ·
    refine ⟨83931586317158265462842885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55954390878105510308561923 83931586317158265462842885)
    ·
      refine ⟨15737172434467174774283041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83931586317158265462842885 15737172434467174774283041)
      ·
        refine ⟨11802879325850381080712281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15737172434467174774283041 11802879325850381080712281)
        ·
          refine ⟨8852159494387785810534211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11802879325850381080712281 8852159494387785810534211)
          ·
            refine ⟨13278239241581678715801317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8852159494387785810534211 13278239241581678715801317)
            ·
              refine ⟨2489669857796564759212747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13278239241581678715801317 2489669857796564759212747)
              ·
                refine ⟨3734504786694847138819121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489669857796564759212747 3734504786694847138819121)
                ·
                  refine ⟨2800878590021135354114341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3734504786694847138819121 2800878590021135354114341)
                  ·
                    refine ⟨525164735628962878896439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2800878590021135354114341 525164735628962878896439)
                    ·
                      rfl

theorem cell23_3068264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_3068264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068264 prefixEnd_3068264 := by exact prefixLift 3068264
  have htrace : WordTrace (prefixWord ++ tailWord_3068264) baseStart_3068264 baseEnd_3068264 := by
    simpa [prefixWord, tailWord_3068264, baseEnd_3068264] using wordTrace_append hprefix tailTrace_3068264
  have hstable : (prefixWord ++ tailWord_3068264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068264).length < 2 ^ (prefixWord ++ tailWord_3068264).sum := by decide
  have hdescent : baseEnd_3068264 < baseStart_3068264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068274 : List Nat := [3, 2, 1, 2, 1, 5, 1, 2, 1, 2, 3]
def baseStart_3068274 : Nat := 118140960795 + 3068274 * 2 ^ 59
def prefixEnd_3068274 : Nat := 4983230072969 + 3 ^ 40 * 3068274 * 2
def baseEnd_3068274 : Nat := 1575499341693433597564271

theorem tailTrace_3068274 : CollatzResearch.WordTrace tailWord_3068274 prefixEnd_3068274 1575499341693433597564271 := by
  unfold tailWord_3068274
  simp only [CollatzResearch.WordTrace]
  refine ⟨27977286621543698081246969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74606097657449861549991917 27977286621543698081246969)
  ·
    refine ⟨20982964966157773560935227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27977286621543698081246969 20982964966157773560935227)
    ·
      refine ⟨31474447449236660341402841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20982964966157773560935227 31474447449236660341402841)
      ·
        refine ⟨23605835586927495256052131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31474447449236660341402841 23605835586927495256052131)
        ·
          refine ⟨35408753380391242884078197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23605835586927495256052131 35408753380391242884078197)
          ·
            refine ⟨3319570629411679020382331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35408753380391242884078197 3319570629411679020382331)
            ·
              refine ⟨4979355944117518530573497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3319570629411679020382331 4979355944117518530573497)
              ·
                refine ⟨3734516958088138897930123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4979355944117518530573497 3734516958088138897930123)
                ·
                  refine ⟨5601775437132208346895185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3734516958088138897930123 5601775437132208346895185)
                  ·
                    refine ⟨4201331577849156260171389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5601775437132208346895185 4201331577849156260171389)
                    ·
                      refine ⟨1575499341693433597564271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4201331577849156260171389 1575499341693433597564271)
                      ·
                        rfl

theorem cell23_3068274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_3068274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068274 prefixEnd_3068274 := by exact prefixLift 3068274
  have htrace : WordTrace (prefixWord ++ tailWord_3068274) baseStart_3068274 baseEnd_3068274 := by
    simpa [prefixWord, tailWord_3068274, baseEnd_3068274] using wordTrace_append hprefix tailTrace_3068274
  have hstable : (prefixWord ++ tailWord_3068274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068274).length < 2 ^ (prefixWord ++ tailWord_3068274).sum := by decide
  have hdescent : baseEnd_3068274 < baseStart_3068274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068320 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 2, 6]
def baseStart_3068320 : Nat := 118140960795 + 3068320 * 2 ^ 59
def prefixEnd_3068320 : Nat := 4983230072969 + 3 ^ 40 * 3068320 * 2
def baseEnd_3068320 : Nat := 525174320601180139196353

theorem tailTrace_3068320 : CollatzResearch.WordTrace tailWord_3068320 prefixEnd_3068320 525174320601180139196353 := by
  unfold tailWord_3068320
  simp only [CollatzResearch.WordTrace]
  refine ⟨55955412122004071090581207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74607216162672094787441609 55955412122004071090581207)
  ·
    refine ⟨83933118183006106635871811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55955412122004071090581207 83933118183006106635871811)
    ·
      refine ⟨125899677274509159953807717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83933118183006106635871811 125899677274509159953807717)
      ·
        refine ⟨23606189488970467491338947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125899677274509159953807717 23606189488970467491338947)
        ·
          refine ⟨35409284233455701237008421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23606189488970467491338947 35409284233455701237008421)
          ·
            refine ⟨6639240793772943981939079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35409284233455701237008421 6639240793772943981939079)
            ·
              refine ⟨9958861190659415972908619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6639240793772943981939079 9958861190659415972908619)
              ·
                refine ⟨14938291785989123959362929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9958861190659415972908619 14938291785989123959362929)
                ·
                  refine ⟨11203718839491842969522197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14938291785989123959362929 11203718839491842969522197)
                  ·
                    refine ⟨525174320601180139196353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11203718839491842969522197 525174320601180139196353)
                    ·
                      rfl

theorem cell23_3068320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 2, 6].length) (baseStart_3068320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068320 prefixEnd_3068320 := by exact prefixLift 3068320
  have htrace : WordTrace (prefixWord ++ tailWord_3068320) baseStart_3068320 baseEnd_3068320 := by
    simpa [prefixWord, tailWord_3068320, baseEnd_3068320] using wordTrace_append hprefix tailTrace_3068320
  have hstable : (prefixWord ++ tailWord_3068320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068320).length < 2 ^ (prefixWord ++ tailWord_3068320).sum := by decide
  have hdescent : baseEnd_3068320 < baseStart_3068320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068348 : List Nat := [2, 2, 2, 4, 1, 3, 2, 1, 1, 3, 2]
def baseStart_3068348 : Nat := 118140960795 + 3068348 * 2 ^ 59
def prefixEnd_3068348 : Nat := 4983230072969 + 3 ^ 40 * 3068348 * 2
def baseEnd_3068348 : Nat := 1575537339261866308038931

theorem tailTrace_3068348 : CollatzResearch.WordTrace tailWord_3068348 prefixEnd_3068348 1575537339261866308038931 := by
  unfold tailWord_3068348
  simp only [CollatzResearch.WordTrace]
  refine ⟨55955922743953351481590849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74607896991937801975454465 55955922743953351481590849)
  ·
    refine ⟨41966942057965013611193137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55955922743953351481590849 41966942057965013611193137)
    ·
      refine ⟨31475206543473760208394853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41966942057965013611193137 31475206543473760208394853)
      ·
        refine ⟨5901601226901330039074035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31475206543473760208394853 5901601226901330039074035)
        ·
          refine ⟨8852401840351995058611053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5901601226901330039074035 8852401840351995058611053)
          ·
            refine ⟨3319650690131998146979145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8852401840351995058611053 3319650690131998146979145)
            ·
              refine ⟨2489738017598998610234359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3319650690131998146979145 2489738017598998610234359)
              ·
                refine ⟨3734607026398497915351539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489738017598998610234359 3734607026398497915351539)
                ·
                  refine ⟨5601910539597746873027309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3734607026398497915351539 5601910539597746873027309)
                  ·
                    refine ⟨2100716452349155077385241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5601910539597746873027309 2100716452349155077385241)
                    ·
                      refine ⟨1575537339261866308038931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2100716452349155077385241 1575537339261866308038931)
                      ·
                        rfl

theorem cell23_3068348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_3068348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068348 prefixEnd_3068348 := by exact prefixLift 3068348
  have htrace : WordTrace (prefixWord ++ tailWord_3068348) baseStart_3068348 baseEnd_3068348 := by
    simpa [prefixWord, tailWord_3068348, baseEnd_3068348] using wordTrace_append hprefix tailTrace_3068348
  have hstable : (prefixWord ++ tailWord_3068348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068348).length < 2 ^ (prefixWord ++ tailWord_3068348).sum := by decide
  have hdescent : baseEnd_3068348 < baseStart_3068348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068397 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_3068397 : Nat := 118140960795 + 3068397 * 2 ^ 59
def prefixEnd_3068397 : Nat := 4983230072969 + 3 ^ 40 * 3068397 * 2
def baseEnd_3068397 : Nat := 525187499937978872108735

theorem tailTrace_3068397 : CollatzResearch.WordTrace tailWord_3068397 prefixEnd_3068397 525187499937978872108735 := by
  unfold tailWord_3068397
  simp only [CollatzResearch.WordTrace]
  refine ⟨111913632664729184331715445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74609088443152789554476963 111913632664729184331715445)
  ·
    refine ⟨10491903062318361031098323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111913632664729184331715445 10491903062318361031098323)
    ·
      refine ⟨15737854593477541546647485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10491903062318361031098323 15737854593477541546647485)
      ·
        refine ⟨5901695472554078079992807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15737854593477541546647485 5901695472554078079992807)
        ·
          refine ⟨8852543208831117119989211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5901695472554078079992807 8852543208831117119989211)
          ·
            refine ⟨13278814813246675679983817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8852543208831117119989211 13278814813246675679983817)
            ·
              refine ⟨9959111109935006759987863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13278814813246675679983817 9959111109935006759987863)
              ·
                refine ⟨14938666664902510139981795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9959111109935006759987863 14938666664902510139981795)
                ·
                  refine ⟨22407999997353765209972693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14938666664902510139981795 22407999997353765209972693)
                  ·
                    refine ⟨525187499937978872108735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22407999997353765209972693 525187499937978872108735)
                    ·
                      rfl

theorem cell23_3068397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_3068397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068397 prefixEnd_3068397 := by exact prefixLift 3068397
  have htrace : WordTrace (prefixWord ++ tailWord_3068397) baseStart_3068397 baseEnd_3068397 := by
    simpa [prefixWord, tailWord_3068397, baseEnd_3068397] using wordTrace_append hprefix tailTrace_3068397
  have hstable : (prefixWord ++ tailWord_3068397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068397).length < 2 ^ (prefixWord ++ tailWord_3068397).sum := by decide
  have hdescent : baseEnd_3068397 < baseStart_3068397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068400 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 4]
def baseStart_3068400 : Nat := 118140960795 + 3068400 * 2 ^ 59
def prefixEnd_3068400 : Nat := 4983230072969 + 3 ^ 40 * 3068400 * 2
def baseEnd_3068400 : Nat := 1575564040255900104588691

theorem tailTrace_3068400 : CollatzResearch.WordTrace tailWord_3068400 prefixEnd_3068400 1575564040255900104588691 := by
  unfold tailWord_3068400
  simp only [CollatzResearch.WordTrace]
  refine ⟨55956871041859157922037327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74609161389145543896049769 55956871041859157922037327)
  ·
    refine ⟨83935306562788736883055991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55956871041859157922037327 83935306562788736883055991)
    ·
      refine ⟨125902959844183105324583987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83935306562788736883055991 125902959844183105324583987)
      ·
        refine ⟨188854439766274657986875981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125902959844183105324583987 188854439766274657986875981)
        ·
          refine ⟨70820414912352996745078493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188854439766274657986875981 70820414912352996745078493)
          ·
            refine ⟨26557655592132373779404435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70820414912352996745078493 26557655592132373779404435)
            ·
              refine ⟨39836483388198560669106653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26557655592132373779404435 39836483388198560669106653)
              ·
                refine ⟨14938681270574460250914995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39836483388198560669106653 14938681270574460250914995)
                ·
                  refine ⟨22408021905861690376372493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14938681270574460250914995 22408021905861690376372493)
                  ·
                    refine ⟨8403008214698133891139685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22408021905861690376372493 8403008214698133891139685)
                    ·
                      refine ⟨1575564040255900104588691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8403008214698133891139685 1575564040255900104588691)
                      ·
                        rfl

theorem cell23_3068400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_3068400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068400 prefixEnd_3068400 := by exact prefixLift 3068400
  have htrace : WordTrace (prefixWord ++ tailWord_3068400) baseStart_3068400 baseEnd_3068400 := by
    simpa [prefixWord, tailWord_3068400, baseEnd_3068400] using wordTrace_append hprefix tailTrace_3068400
  have hstable : (prefixWord ++ tailWord_3068400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068400).length < 2 ^ (prefixWord ++ tailWord_3068400).sum := by decide
  have hdescent : baseEnd_3068400 < baseStart_3068400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068417 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_3068417 : Nat := 118140960795 + 3068417 * 2 ^ 59
def prefixEnd_3068417 : Nat := 4983230072969 + 3 ^ 40 * 3068417 * 2
def baseEnd_3068417 : Nat := 1575572769427026538076113

theorem tailTrace_3068417 : CollatzResearch.WordTrace tailWord_3068417 prefixEnd_3068417 1575572769427026538076113 := by
  unfold tailWord_3068417
  simp only [CollatzResearch.WordTrace]
  refine ⟨111914362124656727747443505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74609574749771151831629003 111914362124656727747443505)
  ·
    refine ⟨83935771593492545810582629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111914362124656727747443505 83935771593492545810582629)
    ·
      refine ⟨15737957173779852339484243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83935771593492545810582629 15737957173779852339484243)
      ·
        refine ⟨23606935760669778509226365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15737957173779852339484243 23606935760669778509226365)
        ·
          refine ⟨8852600910251166940959887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23606935760669778509226365 8852600910251166940959887)
          ·
            refine ⟨13278901365376750411439831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8852600910251166940959887 13278901365376750411439831)
            ·
              refine ⟨19918352048065125617159747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13278901365376750411439831 19918352048065125617159747)
              ·
                refine ⟨29877528072097688425739621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19918352048065125617159747 29877528072097688425739621)
                ·
                  refine ⟨5602036513518316579826179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29877528072097688425739621 5602036513518316579826179)
                  ·
                    refine ⟨8403054770277474869739269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5602036513518316579826179 8403054770277474869739269)
                    ·
                      refine ⟨1575572769427026538076113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8403054770277474869739269 1575572769427026538076113)
                      ·
                        rfl

theorem cell23_3068417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_3068417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068417 prefixEnd_3068417 := by exact prefixLift 3068417
  have htrace : WordTrace (prefixWord ++ tailWord_3068417) baseStart_3068417 baseEnd_3068417 := by
    simpa [prefixWord, tailWord_3068417, baseEnd_3068417] using wordTrace_append hprefix tailTrace_3068417
  have hstable : (prefixWord ++ tailWord_3068417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068417).length < 2 ^ (prefixWord ++ tailWord_3068417).sum := by decide
  have hdescent : baseEnd_3068417 < baseStart_3068417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068418 : List Nat := [3, 4, 1, 2, 2, 1, 3, 2, 5]
def baseStart_3068418 : Nat := 118140960795 + 3068418 * 2 ^ 59
def prefixEnd_3068418 : Nat := 4983230072969 + 3 ^ 40 * 3068418 * 2
def baseEnd_3068418 : Nat := 175063698100853448240401

theorem tailTrace_3068418 : CollatzResearch.WordTrace tailWord_3068418 prefixEnd_3068418 175063698100853448240401 := by
  unfold tailWord_3068418
  simp only [CollatzResearch.WordTrace]
  refine ⟨27978599649413276229557477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74609599065102069945486605 27978599649413276229557477)
  ·
    refine ⟨5245987434264989293042027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27978599649413276229557477 5245987434264989293042027)
    ·
      refine ⟨7868981151397483939563041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5245987434264989293042027 7868981151397483939563041)
      ·
        refine ⟨5901735863548112954672281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7868981151397483939563041 5901735863548112954672281)
        ·
          refine ⟨4426301897661084716004211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5901735863548112954672281 4426301897661084716004211)
          ·
            refine ⟨6639452846491627074006317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4426301897661084716004211 6639452846491627074006317)
            ·
              refine ⟨2489794817434360152752369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6639452846491627074006317 2489794817434360152752369)
              ·
                refine ⟨1867346113075770114564277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2489794817434360152752369 1867346113075770114564277)
                ·
                  refine ⟨175063698100853448240401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1867346113075770114564277 175063698100853448240401)
                  ·
                    rfl

theorem cell23_3068418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_3068418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068418 prefixEnd_3068418 := by exact prefixLift 3068418
  have htrace : WordTrace (prefixWord ++ tailWord_3068418) baseStart_3068418 baseEnd_3068418 := by
    simpa [prefixWord, tailWord_3068418, baseEnd_3068418] using wordTrace_append hprefix tailTrace_3068418
  have hstable : (prefixWord ++ tailWord_3068418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068418).length < 2 ^ (prefixWord ++ tailWord_3068418).sum := by decide
  have hdescent : baseEnd_3068418 < baseStart_3068418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068437 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_3068437 : Nat := 118140960795 + 3068437 * 2 ^ 59
def prefixEnd_3068437 : Nat := 4983230072969 + 3 ^ 40 * 3068437 * 2
def baseEnd_3068437 : Nat := 1575583039040116459826021

theorem tailTrace_3068437 : CollatzResearch.WordTrace tailWord_3068437 prefixEnd_3068437 1575583039040116459826021 := by
  unfold tailWord_3068437
  simp only [CollatzResearch.WordTrace]
  refine ⟨111915091584584271163171565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74610061056389514108781043 111915091584584271163171565)
  ·
    refine ⟨41968159344219101686189337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111915091584584271163171565 41968159344219101686189337)
    ·
      refine ⟨31476119508164326264642003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41968159344219101686189337 31476119508164326264642003)
      ·
        refine ⟨47214179262246489396963005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31476119508164326264642003 47214179262246489396963005)
        ·
          refine ⟨17705317223342433523861127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47214179262246489396963005 17705317223342433523861127)
          ·
            refine ⟨26557975835013650285791691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17705317223342433523861127 26557975835013650285791691)
            ·
              refine ⟨39836963752520475428687537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26557975835013650285791691 39836963752520475428687537)
              ·
                refine ⟨29877722814390356571515653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39836963752520475428687537 29877722814390356571515653)
                ·
                  refine ⟨5602073027698191857159185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29877722814390356571515653 5602073027698191857159185)
                  ·
                    refine ⟨4201554770773643892869389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5602073027698191857159185 4201554770773643892869389)
                    ·
                      refine ⟨1575583039040116459826021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4201554770773643892869389 1575583039040116459826021)
                      ·
                        rfl

theorem cell23_3068437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_3068437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068437 prefixEnd_3068437 := by exact prefixLift 3068437
  have htrace : WordTrace (prefixWord ++ tailWord_3068437) baseStart_3068437 baseEnd_3068437 := by
    simpa [prefixWord, tailWord_3068437, baseEnd_3068437] using wordTrace_append hprefix tailTrace_3068437
  have hstable : (prefixWord ++ tailWord_3068437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068437).length < 2 ^ (prefixWord ++ tailWord_3068437).sum := by decide
  have hdescent : baseEnd_3068437 < baseStart_3068437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068487 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 3, 5]
def baseStart_3068487 : Nat := 118140960795 + 3068487 * 2 ^ 59
def prefixEnd_3068487 : Nat := 4983230072969 + 3 ^ 40 * 3068487 * 2
def baseEnd_3068487 : Nat := 525202904357613754733597

theorem tailTrace_3068487 : CollatzResearch.WordTrace tailWord_3068487 prefixEnd_3068487 525202904357613754733597 := by
  unfold tailWord_3068487
  simp only [CollatzResearch.WordTrace]
  refine ⟨111916915234403129702491715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74611276822935419801661143 111916915234403129702491715)
  ·
    refine ⟨167875372851604694553737573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111916915234403129702491715 167875372851604694553737573)
    ·
      refine ⟨31476632409675880228825795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167875372851604694553737573 31476632409675880228825795)
      ·
        refine ⟨47214948614513820343238693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31476632409675880228825795 47214948614513820343238693)
        ·
          refine ⟨8852802865221341314357255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47214948614513820343238693 8852802865221341314357255)
          ·
            refine ⟨13279204297832011971535883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8852802865221341314357255 13279204297832011971535883)
            ·
              refine ⟨19918806446748017957303825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13279204297832011971535883 19918806446748017957303825)
              ·
                refine ⟨14939104835061013467977869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19918806446748017957303825 14939104835061013467977869)
                ·
                  refine ⟨5602164313147880050491701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14939104835061013467977869 5602164313147880050491701)
                  ·
                    refine ⟨525202904357613754733597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5602164313147880050491701 525202904357613754733597)
                    ·
                      rfl

theorem cell23_3068487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_3068487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068487 prefixEnd_3068487 := by exact prefixLift 3068487
  have htrace : WordTrace (prefixWord ++ tailWord_3068487) baseStart_3068487 baseEnd_3068487 := by
    simpa [prefixWord, tailWord_3068487, baseEnd_3068487] using wordTrace_append hprefix tailTrace_3068487
  have hstable : (prefixWord ++ tailWord_3068487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068487).length < 2 ^ (prefixWord ++ tailWord_3068487).sum := by decide
  have hdescent : baseEnd_3068487 < baseStart_3068487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068494 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2]
def baseStart_3068494 : Nat := 118140960795 + 3068494 * 2 ^ 59
def prefixEnd_3068494 : Nat := 4983230072969 + 3 ^ 40 * 3068494 * 2
def baseEnd_3068494 : Nat := 1575612307437422736813259

theorem tailTrace_3068494 : CollatzResearch.WordTrace tailWord_3068494 prefixEnd_3068494 1575612307437422736813259 := by
  unfold tailWord_3068494
  simp only [CollatzResearch.WordTrace]
  refine ⟨13989646318172221237249567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74611447030251846598664357 13989646318172221237249567)
  ·
    refine ⟨20984469477258331855874351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13989646318172221237249567 20984469477258331855874351)
    ·
      refine ⟨31476704215887497783811527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20984469477258331855874351 31476704215887497783811527)
      ·
        refine ⟨47215056323831246675717291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31476704215887497783811527 47215056323831246675717291)
        ·
          refine ⟨70822584485746870013575937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47215056323831246675717291 70822584485746870013575937)
          ·
            refine ⟨53116938364310152510181953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70822584485746870013575937 53116938364310152510181953)
            ·
              refine ⟨39837703773232614382636465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53116938364310152510181953 39837703773232614382636465)
              ·
                refine ⟨29878277829924460786977349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39837703773232614382636465 29878277829924460786977349)
                ·
                  refine ⟨5602177093110836397558253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29878277829924460786977349 5602177093110836397558253)
                  ·
                    refine ⟨2100816409916563649084345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5602177093110836397558253 2100816409916563649084345)
                    ·
                      refine ⟨1575612307437422736813259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2100816409916563649084345 1575612307437422736813259)
                      ·
                        rfl

theorem cell23_3068494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_3068494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068494 prefixEnd_3068494 := by exact prefixLift 3068494
  have htrace : WordTrace (prefixWord ++ tailWord_3068494) baseStart_3068494 baseEnd_3068494 := by
    simpa [prefixWord, tailWord_3068494, baseEnd_3068494] using wordTrace_append hprefix tailTrace_3068494
  have hstable : (prefixWord ++ tailWord_3068494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068494).length < 2 ^ (prefixWord ++ tailWord_3068494).sum := by decide
  have hdescent : baseEnd_3068494 < baseStart_3068494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068551 : List Nat := [1, 1, 4, 2, 1, 2, 5, 1, 2, 4]
def baseStart_3068551 : Nat := 118140960795 + 3068551 * 2 ^ 59
def prefixEnd_3068551 : Nat := 4983230072969 + 3 ^ 40 * 3068551 * 2
def baseEnd_3068551 : Nat := 525213858611576337933499

theorem tailTrace_3068551 : CollatzResearch.WordTrace tailWord_3068551 prefixEnd_3068551 525213858611576337933499 := by
  unfold tailWord_3068551
  simp only [CollatzResearch.WordTrace]
  refine ⟨111919249506171268632821507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74612833004114179088547671 111919249506171268632821507)
  ·
    refine ⟨167878874259256902949232261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111919249506171268632821507 167878874259256902949232261)
    ·
      refine ⟨31477288923610669302981049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167878874259256902949232261 31477288923610669302981049)
      ·
        refine ⟨23607966692708001977235787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31477288923610669302981049 23607966692708001977235787)
        ·
          refine ⟨35411950039062002965853681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23607966692708001977235787 35411950039062002965853681)
          ·
            refine ⟨26558962529296502224390261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35411950039062002965853681 26558962529296502224390261)
            ·
              refine ⟨2489902737121547083536587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26558962529296502224390261 2489902737121547083536587)
              ·
                refine ⟨3734854105682320625304881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489902737121547083536587 3734854105682320625304881)
                ·
                  refine ⟨2801140579261740468978661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3734854105682320625304881 2801140579261740468978661)
                  ·
                    refine ⟨525213858611576337933499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2801140579261740468978661 525213858611576337933499)
                    ·
                      rfl

theorem cell23_3068551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_3068551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068551 prefixEnd_3068551 := by exact prefixLift 3068551
  have htrace : WordTrace (prefixWord ++ tailWord_3068551) baseStart_3068551 baseEnd_3068551 := by
    simpa [prefixWord, tailWord_3068551, baseEnd_3068551] using wordTrace_append hprefix tailTrace_3068551
  have hstable : (prefixWord ++ tailWord_3068551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068551).length < 2 ^ (prefixWord ++ tailWord_3068551).sum := by decide
  have hdescent : baseEnd_3068551 < baseStart_3068551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068554 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_3068554 : Nat := 118140960795 + 3068554 * 2 ^ 59
def prefixEnd_3068554 : Nat := 4983230072969 + 3 ^ 40 * 3068554 * 2
def baseEnd_3068554 : Nat := 1575643116276692502062983

theorem tailTrace_3068554 : CollatzResearch.WordTrace tailWord_3068554 prefixEnd_3068554 1575643116276692502062983 := by
  unfold tailWord_3068554
  simp only [CollatzResearch.WordTrace]
  refine ⟨27979839731290100036295179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74612905950106933430120477 27979839731290100036295179)
  ·
    refine ⟨41969759596935150054442769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27979839731290100036295179 41969759596935150054442769)
    ·
      refine ⟨31477319697701362540832077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41969759596935150054442769 31477319697701362540832077)
      ·
        refine ⟨11803994886638010952812029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31477319697701362540832077 11803994886638010952812029)
        ·
          refine ⟨4426498082489254107304511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11803994886638010952812029 4426498082489254107304511)
          ·
            refine ⟨6639747123733881160956767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4426498082489254107304511 6639747123733881160956767)
            ·
              refine ⟨9959620685600821741435151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6639747123733881160956767 9959620685600821741435151)
              ·
                refine ⟨14939431028401232612152727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9959620685600821741435151 14939431028401232612152727)
                ·
                  refine ⟨22409146542601848918229091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14939431028401232612152727 22409146542601848918229091)
                  ·
                    refine ⟨33613719813902773377343637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22409146542601848918229091 33613719813902773377343637)
                    ·
                      refine ⟨1575643116276692502062983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33613719813902773377343637 1575643116276692502062983)
                      ·
                        rfl

theorem cell23_3068554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_3068554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068554 prefixEnd_3068554 := by exact prefixLift 3068554
  have htrace : WordTrace (prefixWord ++ tailWord_3068554) baseStart_3068554 baseEnd_3068554 := by
    simpa [prefixWord, tailWord_3068554, baseEnd_3068554] using wordTrace_append hprefix tailTrace_3068554
  have hstable : (prefixWord ++ tailWord_3068554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068554).length < 2 ^ (prefixWord ++ tailWord_3068554).sum := by decide
  have hdescent : baseEnd_3068554 < baseStart_3068554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068564 : List Nat := [2, 4, 2, 2, 1, 2, 1, 9]
def baseStart_3068564 : Nat := 118140960795 + 3068564 * 2 ^ 59
def prefixEnd_3068564 : Nat := 4983230072969 + 3 ^ 40 * 3068564 * 2
def baseEnd_3068564 : Nat := 58357342632712498627331

theorem tailTrace_3068564 : CollatzResearch.WordTrace tailWord_3068564 prefixEnd_3068564 58357342632712498627331 := by
  unfold tailWord_3068564
  simp only [CollatzResearch.WordTrace]
  refine ⟨55959861827562085926522373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74613149103416114568696497 55959861827562085926522373)
  ·
    refine ⟨10492474092667891111222945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55959861827562085926522373 10492474092667891111222945)
    ·
      refine ⟨7869355569500918333417209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10492474092667891111222945 7869355569500918333417209)
      ·
        refine ⟨5902016677125688750062907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7869355569500918333417209 5902016677125688750062907)
        ·
          refine ⟨8853025015688533125094361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5902016677125688750062907 8853025015688533125094361)
          ·
            refine ⟨6639768761766399843820771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8853025015688533125094361 6639768761766399843820771)
            ·
              refine ⟨9959653142649599765731157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6639768761766399843820771 9959653142649599765731157)
              ·
                refine ⟨58357342632712498627331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9959653142649599765731157 58357342632712498627331)
                ·
                  rfl

theorem cell23_3068564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 9].length) (baseStart_3068564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068564 prefixEnd_3068564 := by exact prefixLift 3068564
  have htrace : WordTrace (prefixWord ++ tailWord_3068564) baseStart_3068564 baseEnd_3068564 := by
    simpa [prefixWord, tailWord_3068564, baseEnd_3068564] using wordTrace_append hprefix tailTrace_3068564
  have hstable : (prefixWord ++ tailWord_3068564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068564).length < 2 ^ (prefixWord ++ tailWord_3068564).sum := by decide
  have hdescent : baseEnd_3068564 < baseStart_3068564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068608 : List Nat := [2, 1, 1, 2, 4, 2, 4, 1, 2, 1, 3]
def baseStart_3068608 : Nat := 118140960795 + 3068608 * 2 ^ 59
def prefixEnd_3068608 : Nat := 4983230072969 + 3 ^ 40 * 3068608 * 2
def baseEnd_3068608 : Nat := 1575670844232035290787735

theorem tailTrace_3068608 : CollatzResearch.WordTrace tailWord_3068608 prefixEnd_3068608 1575670844232035290787735 := by
  unfold tailWord_3068608
  simp only [CollatzResearch.WordTrace]
  refine ⟨55960664233482383683823239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74614218977976511578430985 55960664233482383683823239)
  ·
    refine ⟨83940996350223575525734859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55960664233482383683823239 83940996350223575525734859)
    ·
      refine ⟨125911494525335363288602289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83940996350223575525734859 125911494525335363288602289)
      ·
        refine ⟨94433620894001522466451717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125911494525335363288602289 94433620894001522466451717)
        ·
          refine ⟨17706303917625285462459697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94433620894001522466451717 17706303917625285462459697)
          ·
            refine ⟨13279727938218964096844773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17706303917625285462459697 13279727938218964096844773)
            ·
              refine ⟨2489948988416055768158395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13279727938218964096844773 2489948988416055768158395)
              ·
                refine ⟨3734923482624083652237593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489948988416055768158395 3734923482624083652237593)
                ·
                  refine ⟨2801192611968062739178195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3734923482624083652237593 2801192611968062739178195)
                  ·
                    refine ⟨4201788917952094108767293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2801192611968062739178195 4201788917952094108767293)
                    ·
                      refine ⟨1575670844232035290787735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4201788917952094108767293 1575670844232035290787735)
                      ·
                        rfl

theorem cell23_3068608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 2, 1, 3].length) (baseStart_3068608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068608 prefixEnd_3068608 := by exact prefixLift 3068608
  have htrace : WordTrace (prefixWord ++ tailWord_3068608) baseStart_3068608 baseEnd_3068608 := by
    simpa [prefixWord, tailWord_3068608, baseEnd_3068608] using wordTrace_append hprefix tailTrace_3068608
  have hstable : (prefixWord ++ tailWord_3068608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068608).length < 2 ^ (prefixWord ++ tailWord_3068608).sum := by decide
  have hdescent : baseEnd_3068608 < baseStart_3068608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068618 : List Nat := [3, 1, 2, 1, 4, 1, 3, 2, 1, 3, 2]
def baseStart_3068618 : Nat := 118140960795 + 3068618 * 2 ^ 59
def prefixEnd_3068618 : Nat := 4983230072969 + 3 ^ 40 * 3068618 * 2
def baseEnd_3068618 : Nat := 1575675979038580251662689

theorem tailTrace_3068618 : CollatzResearch.WordTrace tailWord_3068618 prefixEnd_3068618 1575675979038580251662689 := by
  unfold tailWord_3068618
  simp only [CollatzResearch.WordTrace]
  refine ⟨27980423299232134768877627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74614462131285692717007005 27980423299232134768877627)
  ·
    refine ⟨41970634948848202153316441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27980423299232134768877627 41970634948848202153316441)
    ·
      refine ⟨31477976211636151614987331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41970634948848202153316441 31477976211636151614987331)
      ·
        refine ⟨47216964317454227422480997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31477976211636151614987331 47216964317454227422480997)
        ·
          refine ⟨8853180809522667641715187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47216964317454227422480997 8853180809522667641715187)
          ·
            refine ⟨13279771214284001462572781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8853180809522667641715187 13279771214284001462572781)
            ·
              refine ⟨4979914205356500548464793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13279771214284001462572781 4979914205356500548464793)
              ·
                refine ⟨3734935654017375411348595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4979914205356500548464793 3734935654017375411348595)
                ·
                  refine ⟨5602403481026063117022893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3734935654017375411348595 5602403481026063117022893)
                  ·
                    refine ⟨2100901305384773668883585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5602403481026063117022893 2100901305384773668883585)
                    ·
                      refine ⟨1575675979038580251662689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2100901305384773668883585 1575675979038580251662689)
                      ·
                        rfl

theorem cell23_3068618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_3068618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068618 prefixEnd_3068618 := by exact prefixLift 3068618
  have htrace : WordTrace (prefixWord ++ tailWord_3068618) baseStart_3068618 baseEnd_3068618 := by
    simpa [prefixWord, tailWord_3068618, baseEnd_3068618] using wordTrace_append hprefix tailTrace_3068618
  have hstable : (prefixWord ++ tailWord_3068618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068618).length < 2 ^ (prefixWord ++ tailWord_3068618).sum := by decide
  have hdescent : baseEnd_3068618 < baseStart_3068618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068631 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 1, 4, 2]
def baseStart_3068631 : Nat := 118140960795 + 3068631 * 2 ^ 59
def prefixEnd_3068631 : Nat := 4983230072969 + 3 ^ 40 * 3068631 * 2
def baseEnd_3068631 : Nat := 1575682654287088700800129

theorem tailTrace_3068631 : CollatzResearch.WordTrace tailWord_3068631 prefixEnd_3068631 1575682654287088700800129 := by
  unfold tailWord_3068631
  simp only [CollatzResearch.WordTrace]
  refine ⟨111922167345881442295733747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74614778230587628197155831 111922167345881442295733747)
  ·
    refine ⟨167883251018822163443600621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111922167345881442295733747 167883251018822163443600621)
    ·
      refine ⟨62956219132058311291350233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167883251018822163443600621 62956219132058311291350233)
      ·
        refine ⟨47217164349043733468512675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62956219132058311291350233 47217164349043733468512675)
        ·
          refine ⟨70825746523565600202769013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47217164349043733468512675 70825746523565600202769013)
          ·
            refine ⟨6639913736584275019009595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70825746523565600202769013 6639913736584275019009595)
            ·
              refine ⟨9959870604876412528514393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6639913736584275019009595 9959870604876412528514393)
              ·
                refine ⟨7469902953657309396385795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9959870604876412528514393 7469902953657309396385795)
                ·
                  refine ⟨11204854430485964094578693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7469902953657309396385795 11204854430485964094578693)
                  ·
                    refine ⟨2100910205716118267733505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11204854430485964094578693 2100910205716118267733505)
                    ·
                      refine ⟨1575682654287088700800129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2100910205716118267733505 1575682654287088700800129)
                      ·
                        rfl

theorem cell23_3068631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_3068631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068631 prefixEnd_3068631 := by exact prefixLift 3068631
  have htrace : WordTrace (prefixWord ++ tailWord_3068631) baseStart_3068631 baseEnd_3068631 := by
    simpa [prefixWord, tailWord_3068631, baseEnd_3068631] using wordTrace_append hprefix tailTrace_3068631
  have hstable : (prefixWord ++ tailWord_3068631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068631).length < 2 ^ (prefixWord ++ tailWord_3068631).sum := by decide
  have hdescent : baseEnd_3068631 < baseStart_3068631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068664 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 2, 3, 3]
def baseStart_3068664 : Nat := 118140960795 + 3068664 * 2 ^ 59
def prefixEnd_3068664 : Nat := 4983230072969 + 3 ^ 40 * 3068664 * 2
def baseEnd_3068664 : Nat := 1575699599148687071687477

theorem tailTrace_3068664 : CollatzResearch.WordTrace tailWord_3068664 prefixEnd_3068664 1575699599148687071687477 := by
  unfold tailWord_3068664
  simp only [CollatzResearch.WordTrace]
  refine ⟨55961685477380944465842523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74615580636507925954456697 55961685477380944465842523)
  ·
    refine ⟨83942528216071416698763785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55961685477380944465842523 83942528216071416698763785)
    ·
      refine ⟨62956896162053562524072839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83942528216071416698763785 62956896162053562524072839)
      ·
        refine ⟨94435344243080343786109259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62956896162053562524072839 94435344243080343786109259)
        ·
          refine ⟨141653016364620515679163889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94435344243080343786109259 141653016364620515679163889)
          ·
            refine ⟨106239762273465386759372917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141653016364620515679163889 106239762273465386759372917)
            ·
              refine ⟨9959977713137380008691211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106239762273465386759372917 9959977713137380008691211)
              ·
                refine ⟨14939966569706070013036817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9959977713137380008691211 14939966569706070013036817)
                ·
                  refine ⟨11204974927279552509777613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14939966569706070013036817 11204974927279552509777613)
                  ·
                    refine ⟨4201865597729832191166605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11204974927279552509777613 4201865597729832191166605)
                    ·
                      refine ⟨1575699599148687071687477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4201865597729832191166605 1575699599148687071687477)
                      ·
                        rfl

theorem cell23_3068664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_3068664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068664 prefixEnd_3068664 := by exact prefixLift 3068664
  have htrace : WordTrace (prefixWord ++ tailWord_3068664) baseStart_3068664 baseEnd_3068664 := by
    simpa [prefixWord, tailWord_3068664, baseEnd_3068664] using wordTrace_append hprefix tailTrace_3068664
  have hstable : (prefixWord ++ tailWord_3068664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068664).length < 2 ^ (prefixWord ++ tailWord_3068664).sum := by decide
  have hdescent : baseEnd_3068664 < baseStart_3068664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068677 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_3068677 : Nat := 118140960795 + 3068677 * 2 ^ 59
def prefixEnd_3068677 : Nat := 4983230072969 + 3 ^ 40 * 3068677 * 2
def baseEnd_3068677 : Nat := 1575706274397195520824917

theorem tailTrace_3068677 : CollatzResearch.WordTrace tailWord_3068677 prefixEnd_3068677 1575706274397195520824917 := by
  unfold tailWord_3068677
  simp only [CollatzResearch.WordTrace]
  refine ⟨111923845103714792151908285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74615896735809861434605523 111923845103714792151908285)
  ·
    refine ⟨41971441913893047056965607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111923845103714792151908285 41971441913893047056965607)
    ·
      refine ⟨62957162870839570585448411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41971441913893047056965607 62957162870839570585448411)
      ·
        refine ⟨94435744306259355878172617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62957162870839570585448411 94435744306259355878172617)
        ·
          refine ⟨70826808229694516908629463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94435744306259355878172617 70826808229694516908629463)
          ·
            refine ⟨106240212344541775362944195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70826808229694516908629463 106240212344541775362944195)
            ·
              refine ⟨159360318516812663044416293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106240212344541775362944195 159360318516812663044416293)
              ·
                refine ⟨29880059721902374320828055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159360318516812663044416293 29880059721902374320828055)
                ·
                  refine ⟨44820089582853561481242083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29880059721902374320828055 44820089582853561481242083)
                  ·
                    refine ⟨67230134374280342221863125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44820089582853561481242083 67230134374280342221863125)
                    ·
                      refine ⟨1575706274397195520824917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67230134374280342221863125 1575706274397195520824917)
                      ·
                        rfl

theorem cell23_3068677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_3068677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068677 prefixEnd_3068677 := by exact prefixLift 3068677
  have htrace : WordTrace (prefixWord ++ tailWord_3068677) baseStart_3068677 baseEnd_3068677 := by
    simpa [prefixWord, tailWord_3068677, baseEnd_3068677] using wordTrace_append hprefix tailTrace_3068677
  have hstable : (prefixWord ++ tailWord_3068677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068677).length < 2 ^ (prefixWord ++ tailWord_3068677).sum := by decide
  have hdescent : baseEnd_3068677 < baseStart_3068677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068721 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 2, 4, 2]
def baseStart_3068721 : Nat := 118140960795 + 3068721 * 2 ^ 59
def prefixEnd_3068721 : Nat := 4983230072969 + 3 ^ 40 * 3068721 * 2
def baseEnd_3068721 : Nat := 1575728867545993348674715

theorem tailTrace_3068721 : CollatzResearch.WordTrace tailWord_3068721 prefixEnd_3068721 1575728867545993348674715 := by
  unfold tailWord_3068721
  simp only [CollatzResearch.WordTrace]
  refine ⟨111925449915555387666510017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74616966610370258444340011 111925449915555387666510017)
  ·
    refine ⟨83944087436666540749882513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111925449915555387666510017 83944087436666540749882513)
    ·
      refine ⟨62958065577499905562411885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83944087436666540749882513 62958065577499905562411885)
      ·
        refine ⟨23609274591562464585904457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62958065577499905562411885 23609274591562464585904457)
        ·
          refine ⟨17706955943671848439428343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23609274591562464585904457 17706955943671848439428343)
          ·
            refine ⟨26560433915507772659142515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17706955943671848439428343 26560433915507772659142515)
            ·
              refine ⟨39840650873261658988713773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26560433915507772659142515 39840650873261658988713773)
              ·
                refine ⟨14940244077473122120767665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39840650873261658988713773 14940244077473122120767665)
                ·
                  refine ⟨11205183058104841590575749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14940244077473122120767665 11205183058104841590575749)
                  ·
                    refine ⟨2100971823394657798232953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11205183058104841590575749 2100971823394657798232953)
                    ·
                      refine ⟨1575728867545993348674715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2100971823394657798232953 1575728867545993348674715)
                      ·
                        rfl

theorem cell23_3068721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_3068721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068721 prefixEnd_3068721 := by exact prefixLift 3068721
  have htrace : WordTrace (prefixWord ++ tailWord_3068721) baseStart_3068721 baseEnd_3068721 := by
    simpa [prefixWord, tailWord_3068721, baseEnd_3068721] using wordTrace_append hprefix tailTrace_3068721
  have hstable : (prefixWord ++ tailWord_3068721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068721).length < 2 ^ (prefixWord ++ tailWord_3068721).sum := by decide
  have hdescent : baseEnd_3068721 < baseStart_3068721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068811 : List Nat := [1, 1, 1, 1, 4, 2, 2, 5, 1, 1, 4]
def baseStart_3068811 : Nat := 118140960795 + 3068811 * 2 ^ 59
def prefixEnd_3068811 : Nat := 4983230072969 + 3 ^ 40 * 3068811 * 2
def baseEnd_3068811 : Nat := 1575775080804897996549301

theorem tailTrace_3068811 : CollatzResearch.WordTrace tailWord_3068811 prefixEnd_3068811 1575775080804897996549301 := by
  unfold tailWord_3068811
  simp only [CollatzResearch.WordTrace]
  refine ⟨111928732485229333037286287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74619154990152888691524191 111928732485229333037286287)
  ·
    refine ⟨167893098727843999555929431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111928732485229333037286287 167893098727843999555929431)
    ·
      refine ⟨251839648091765999333894147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167893098727843999555929431 251839648091765999333894147)
      ·
        refine ⟨377759472137648999000841221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251839648091765999333894147 377759472137648999000841221)
        ·
          refine ⟨70829901025809187312657729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 377759472137648999000841221 70829901025809187312657729)
          ·
            refine ⟨53122425769356890484493297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70829901025809187312657729 53122425769356890484493297)
            ·
              refine ⟨39841819327017667863369973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53122425769356890484493297 39841819327017667863369973)
              ·
                refine ⟨3735170561907906362190935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39841819327017667863369973 3735170561907906362190935)
                ·
                  refine ⟨5602755842861859543286403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3735170561907906362190935 5602755842861859543286403)
                  ·
                    refine ⟨8404133764292789314929605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5602755842861859543286403 8404133764292789314929605)
                    ·
                      refine ⟨1575775080804897996549301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8404133764292789314929605 1575775080804897996549301)
                      ·
                        rfl

theorem cell23_3068811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 1, 4].length) (baseStart_3068811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068811 prefixEnd_3068811 := by exact prefixLift 3068811
  have htrace : WordTrace (prefixWord ++ tailWord_3068811) baseStart_3068811 baseEnd_3068811 := by
    simpa [prefixWord, tailWord_3068811, baseEnd_3068811] using wordTrace_append hprefix tailTrace_3068811
  have hstable : (prefixWord ++ tailWord_3068811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068811).length < 2 ^ (prefixWord ++ tailWord_3068811).sum := by decide
  have hdescent : baseEnd_3068811 < baseStart_3068811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068841 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 1, 2, 4]
def baseStart_3068841 : Nat := 118140960795 + 3068841 * 2 ^ 59
def prefixEnd_3068841 : Nat := 4983230072969 + 3 ^ 40 * 3068841 * 2
def baseEnd_3068841 : Nat := 1575790485224532879174163

theorem tailTrace_3068841 : CollatzResearch.WordTrace tailWord_3068841 prefixEnd_3068841 1575790485224532879174163 := by
  unfold tailWord_3068841
  simp only [CollatzResearch.WordTrace]
  refine ⟨111929826675120648160878377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74619884450080432107252251 111929826675120648160878377)
  ·
    refine ⟨83947370006340486120658783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111929826675120648160878377 83947370006340486120658783)
    ·
      refine ⟨125921055009510729180988175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83947370006340486120658783 125921055009510729180988175)
      ·
        refine ⟨188881582514266093771482263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125921055009510729180988175 188881582514266093771482263)
        ·
          refine ⟨283322373771399140657223395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188881582514266093771482263 283322373771399140657223395)
          ·
            refine ⟨424983560657098710985835093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283322373771399140657223395 424983560657098710985835093)
            ·
              refine ⟨4980276101450375519365255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 424983560657098710985835093 4980276101450375519365255)
              ·
                refine ⟨7470414152175563279047883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4980276101450375519365255 7470414152175563279047883)
                ·
                  refine ⟨11205621228263344918571825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7470414152175563279047883 11205621228263344918571825)
                  ·
                    refine ⟨8404215921197508688928869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11205621228263344918571825 8404215921197508688928869)
                    ·
                      refine ⟨1575790485224532879174163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8404215921197508688928869 1575790485224532879174163)
                      ·
                        rfl

theorem cell23_3068841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 2, 4].length) (baseStart_3068841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068841 prefixEnd_3068841 := by exact prefixLift 3068841
  have htrace : WordTrace (prefixWord ++ tailWord_3068841) baseStart_3068841 baseEnd_3068841 := by
    simpa [prefixWord, tailWord_3068841, baseEnd_3068841] using wordTrace_append hprefix tailTrace_3068841
  have hstable : (prefixWord ++ tailWord_3068841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068841).length < 2 ^ (prefixWord ++ tailWord_3068841).sum := by decide
  have hdescent : baseEnd_3068841 < baseStart_3068841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068868 : List Nat := [2, 3, 3, 3, 1, 1, 10]
def baseStart_3068868 : Nat := 118140960795 + 3068868 * 2 ^ 59
def prefixEnd_3068868 : Nat := 4983230072969 + 3 ^ 40 * 3068868 * 2
def baseEnd_3068868 : Nat := 19454374681508694735019

theorem tailTrace_3068868 : CollatzResearch.WordTrace tailWord_3068868 prefixEnd_3068868 19454374681508694735019 := by
  unfold tailWord_3068868
  simp only [CollatzResearch.WordTrace]
  refine ⟨55965405723011415886055629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74620540964015221181407505 55965405723011415886055629)
  ·
    refine ⟨20987027146129280957270861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55965405723011415886055629 20987027146129280957270861)
    ·
      refine ⟨7870135179798480358976573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20987027146129280957270861 7870135179798480358976573)
      ·
        refine ⟨2951300692424430134616215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7870135179798480358976573 2951300692424430134616215)
        ·
          refine ⟨4426951038636645201924323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2951300692424430134616215 4426951038636645201924323)
          ·
            refine ⟨6640426557954967802886485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4426951038636645201924323 6640426557954967802886485)
            ·
              refine ⟨19454374681508694735019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6640426557954967802886485 19454374681508694735019)
              ·
                rfl

theorem cell23_3068868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 10].length) (baseStart_3068868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068868 prefixEnd_3068868 := by exact prefixLift 3068868
  have htrace : WordTrace (prefixWord ++ tailWord_3068868) baseStart_3068868 baseEnd_3068868 := by
    simpa [prefixWord, tailWord_3068868, baseEnd_3068868] using wordTrace_append hprefix tailTrace_3068868
  have hstable : (prefixWord ++ tailWord_3068868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068868).length < 2 ^ (prefixWord ++ tailWord_3068868).sum := by decide
  have hdescent : baseEnd_3068868 < baseStart_3068868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068872 : List Nat := [2, 1, 3, 1, 6, 1, 1, 2, 2, 4]
def baseStart_3068872 : Nat := 118140960795 + 3068872 * 2 ^ 59
def prefixEnd_3068872 : Nat := 4983230072969 + 3 ^ 40 * 3068872 * 2
def baseEnd_3068872 : Nat := 525268801041607419295507

theorem tailTrace_3068872 : CollatzResearch.WordTrace tailWord_3068872 prefixEnd_3068872 525268801041607419295507 := by
  unfold tailWord_3068872
  simp only [CollatzResearch.WordTrace]
  refine ⟨55965478669004170227628435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74620638225338893636837913 55965478669004170227628435)
  ·
    refine ⟨83948218003506255341442653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55965478669004170227628435 83948218003506255341442653)
    ·
      refine ⟨31480581751314845753040995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83948218003506255341442653 31480581751314845753040995)
      ·
        refine ⟨47220872626972268629561493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31480581751314845753040995 47220872626972268629561493)
        ·
          refine ⟨2213478404389325092010695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47220872626972268629561493 2213478404389325092010695)
          ·
            refine ⟨3320217606583987638016043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2213478404389325092010695 3320217606583987638016043)
            ·
              refine ⟨4980326409875981457024065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3320217606583987638016043 4980326409875981457024065)
              ·
                refine ⟨3735244807406986092768049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4980326409875981457024065 3735244807406986092768049)
                ·
                  refine ⟨2801433605555239569576037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3735244807406986092768049 2801433605555239569576037)
                  ·
                    refine ⟨525268801041607419295507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2801433605555239569576037 525268801041607419295507)
                    ·
                      rfl

theorem cell23_3068872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_3068872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068872 prefixEnd_3068872 := by exact prefixLift 3068872
  have htrace : WordTrace (prefixWord ++ tailWord_3068872) baseStart_3068872 baseEnd_3068872 := by
    simpa [prefixWord, tailWord_3068872, baseEnd_3068872] using wordTrace_append hprefix tailTrace_3068872
  have hstable : (prefixWord ++ tailWord_3068872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068872).length < 2 ^ (prefixWord ++ tailWord_3068872).sum := by decide
  have hdescent : baseEnd_3068872 < baseStart_3068872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068895 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 1, 3, 3]
def baseStart_3068895 : Nat := 118140960795 + 3068895 * 2 ^ 59
def prefixEnd_3068895 : Nat := 4983230072969 + 3 ^ 40 * 3068895 * 2
def baseEnd_3068895 : Nat := 1575818213179875667898915

theorem tailTrace_3068895 : CollatzResearch.WordTrace tailWord_3068895 prefixEnd_3068895 1575818213179875667898915 := by
  unfold tailWord_3068895
  simp only [CollatzResearch.WordTrace]
  refine ⟨111931796216925015383344139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74621197477950010255562759 111931796216925015383344139)
  ·
    refine ⟨167897694325387523075016209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111931796216925015383344139 167897694325387523075016209)
    ·
      refine ⟨125923270744040642306262157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167897694325387523075016209 125923270744040642306262157)
      ·
        refine ⟨47221226529015240864848309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125923270744040642306262157 47221226529015240864848309)
        ·
          refine ⟨4426989987095178831079529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47221226529015240864848309 4426989987095178831079529)
          ·
            refine ⟨3320242490321384123309647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4426989987095178831079529 3320242490321384123309647)
            ·
              refine ⟨4980363735482076184964471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3320242490321384123309647 4980363735482076184964471)
              ·
                refine ⟨7470545603223114277446707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4980363735482076184964471 7470545603223114277446707)
                ·
                  refine ⟨11205818404834671416170061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7470545603223114277446707 11205818404834671416170061)
                  ·
                    refine ⟨4202181901813001781063773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11205818404834671416170061 4202181901813001781063773)
                    ·
                      refine ⟨1575818213179875667898915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4202181901813001781063773 1575818213179875667898915)
                      ·
                        rfl

theorem cell23_3068895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_3068895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068895 prefixEnd_3068895 := by exact prefixLift 3068895
  have htrace : WordTrace (prefixWord ++ tailWord_3068895) baseStart_3068895 baseEnd_3068895 := by
    simpa [prefixWord, tailWord_3068895, baseEnd_3068895] using wordTrace_append hprefix tailTrace_3068895
  have hstable : (prefixWord ++ tailWord_3068895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068895).length < 2 ^ (prefixWord ++ tailWord_3068895).sum := by decide
  have hdescent : baseEnd_3068895 < baseStart_3068895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068921 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 2, 1, 5]
def baseStart_3068921 : Nat := 118140960795 + 3068921 * 2 ^ 59
def prefixEnd_3068921 : Nat := 4983230072969 + 3 ^ 40 * 3068921 * 2
def baseEnd_3068921 : Nat := 1575831563676892566173795

theorem tailTrace_3068921 : CollatzResearch.WordTrace tailWord_3068921 prefixEnd_3068921 1575831563676892566173795 := by
  unfold tailWord_3068921
  simp only [CollatzResearch.WordTrace]
  refine ⟨111932744514830821823790617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74621829676553881215860411 111932744514830821823790617)
  ·
    refine ⟨83949558386123116367842963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111932744514830821823790617 83949558386123116367842963)
    ·
      refine ⟨125924337579184674551764445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83949558386123116367842963 125924337579184674551764445)
      ·
        refine ⟨47221626592194252956911667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125924337579184674551764445 47221626592194252956911667)
        ·
          refine ⟨70832439888291379435367501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47221626592194252956911667 70832439888291379435367501)
          ·
            refine ⟨26562164958109267288262813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70832439888291379435367501 26562164958109267288262813)
            ·
              refine ⟨9960811859290975233098555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26562164958109267288262813 9960811859290975233098555)
              ·
                refine ⟨14941217788936462849647833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9960811859290975233098555 14941217788936462849647833)
                ·
                  refine ⟨11205913341702347137235875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14941217788936462849647833 11205913341702347137235875)
                  ·
                    refine ⟨16808870012553520705853813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11205913341702347137235875 16808870012553520705853813)
                    ·
                      refine ⟨1575831563676892566173795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16808870012553520705853813 1575831563676892566173795)
                      ·
                        rfl

theorem cell23_3068921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_3068921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068921 prefixEnd_3068921 := by exact prefixLift 3068921
  have htrace : WordTrace (prefixWord ++ tailWord_3068921) baseStart_3068921 baseEnd_3068921 := by
    simpa [prefixWord, tailWord_3068921, baseEnd_3068921] using wordTrace_append hprefix tailTrace_3068921
  have hstable : (prefixWord ++ tailWord_3068921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068921).length < 2 ^ (prefixWord ++ tailWord_3068921).sum := by decide
  have hdescent : baseEnd_3068921 < baseStart_3068921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
