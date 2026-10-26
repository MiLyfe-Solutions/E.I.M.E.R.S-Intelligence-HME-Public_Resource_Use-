import V185TrunkScan22Chunk297

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2658352 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 2, 4]
def baseStart_2658352 : Nat := 118140960795 + 2658352 * 2 ^ 59
def prefixEnd_2658352 : Nat := 4983230072969 + 3 ^ 40 * 2658352 * 2
def baseEnd_2658352 : Nat := 910008216560725612849645

theorem tailTrace_2658352 : CollatzResearch.WordTrace tailWord_2658352 prefixEnd_2658352 910008216560725612849645 := by
  unfold tailWord_2658352
  simp only [CollatzResearch.WordTrace]
  refine ⟨48479031432626094610548655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64638708576834792814064873 48479031432626094610548655)
  ·
    refine ⟨72718547148939141915822983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48479031432626094610548655 72718547148939141915822983)
    ·
      refine ⟨109077820723408712873734475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72718547148939141915822983 109077820723408712873734475)
      ·
        refine ⟨163616731085113069310601713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109077820723408712873734475 163616731085113069310601713)
        ·
          refine ⟨122712548313834801982951285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163616731085113069310601713 122712548313834801982951285)
          ·
            refine ⟨11504301404422012685901683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122712548313834801982951285 11504301404422012685901683)
            ·
              refine ⟨17256452106633019028852525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11504301404422012685901683 17256452106633019028852525)
              ·
                refine ⟨6471169539987382135819697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17256452106633019028852525 6471169539987382135819697)
                ·
                  refine ⟨4853377154990536601864773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6471169539987382135819697 4853377154990536601864773)
                  ·
                    refine ⟨910008216560725612849645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4853377154990536601864773 910008216560725612849645)
                    ·
                      rfl

theorem cell22_2658352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_2658352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658352 prefixEnd_2658352 := by exact prefixLift 2658352
  have htrace : WordTrace (prefixWord ++ tailWord_2658352) baseStart_2658352 baseEnd_2658352 := by
    simpa [prefixWord, tailWord_2658352, baseEnd_2658352] using wordTrace_append hprefix tailTrace_2658352
  have hstable : (prefixWord ++ tailWord_2658352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658352).length < 2 ^ (prefixWord ++ tailWord_2658352).sum := by decide
  have hdescent : baseEnd_2658352 < baseStart_2658352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658369 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2658369 : Nat := 118140960795 + 2658369 * 2 ^ 59
def prefixEnd_2658369 : Nat := 4983230072969 + 3 ^ 40 * 2658369 * 2
def baseEnd_2658369 : Nat := 910014036008143235174593

theorem tailTrace_2658369 : CollatzResearch.WordTrace tailWord_2658369 prefixEnd_2658369 910014036008143235174593 := by
  unfold tailWord_2658369
  simp only [CollatzResearch.WordTrace]
  refine ⟨96958682906190601124466161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64639121937460400749644107 96958682906190601124466161)
  ·
    refine ⟨72719012179642950843349621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96958682906190601124466161 72719012179642950843349621)
    ·
      refine ⟨6817407391841526641564027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72719012179642950843349621 6817407391841526641564027)
      ·
        refine ⟨10226111087762289962346041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6817407391841526641564027 10226111087762289962346041)
        ·
          refine ⟨7669583315821717471759531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10226111087762289962346041 7669583315821717471759531)
          ·
            refine ⟨11504374973732576207639297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7669583315821717471759531 11504374973732576207639297)
            ·
              refine ⟨8628281230299432155729473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11504374973732576207639297 8628281230299432155729473)
              ·
                refine ⟨6471210922724574116797105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8628281230299432155729473 6471210922724574116797105)
                ·
                  refine ⟨4853408192043430587597829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6471210922724574116797105 4853408192043430587597829)
                  ·
                    refine ⟨910014036008143235174593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4853408192043430587597829 910014036008143235174593)
                    ·
                      rfl

theorem cell22_2658369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2658369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658369 prefixEnd_2658369 := by exact prefixLift 2658369
  have htrace : WordTrace (prefixWord ++ tailWord_2658369) baseStart_2658369 baseEnd_2658369 := by
    simpa [prefixWord, tailWord_2658369, baseEnd_2658369] using wordTrace_append hprefix tailTrace_2658369
  have hstable : (prefixWord ++ tailWord_2658369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658369).length < 2 ^ (prefixWord ++ tailWord_2658369).sum := by decide
  have hdescent : baseEnd_2658369 < baseStart_2658369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658416 : List Nat := [2, 1, 1, 1, 5, 2, 1, 5, 1, 3]
def baseStart_2658416 : Nat := 118140960795 + 2658416 * 2 ^ 59
def prefixEnd_2658416 : Nat := 4983230072969 + 3 ^ 40 * 2658416 * 2
def baseEnd_2658416 : Nat := 910030125068650779249449

theorem tailTrace_2658416 : CollatzResearch.WordTrace tailWord_2658416 prefixEnd_2658416 910030125068650779249449 := by
  unfold tailWord_2658416
  simp only [CollatzResearch.WordTrace]
  refine ⟨48480198568510164075713551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64640264758013552100951401 48480198568510164075713551)
  ·
    refine ⟨72720297852765246113570327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48480198568510164075713551 72720297852765246113570327)
    ·
      refine ⟨109080446779147869170355491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72720297852765246113570327 109080446779147869170355491)
      ·
        refine ⟨163620670168721803755533237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109080446779147869170355491 163620670168721803755533237)
        ·
          refine ⟨15339437828317669102081241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163620670168721803755533237 15339437828317669102081241)
          ·
            refine ⟨11504578371238251826560931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15339437828317669102081241 11504578371238251826560931)
            ·
              refine ⟨17256867556857377739841397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11504578371238251826560931 17256867556857377739841397)
              ·
                refine ⟨1617831333455379163110131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17256867556857377739841397 1617831333455379163110131)
                ·
                  refine ⟨2426747000183068744665197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617831333455379163110131 2426747000183068744665197)
                  ·
                    refine ⟨910030125068650779249449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2426747000183068744665197 910030125068650779249449)
                    ·
                      rfl

theorem cell22_2658416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 1, 3].length) (baseStart_2658416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658416 prefixEnd_2658416 := by exact prefixLift 2658416
  have htrace : WordTrace (prefixWord ++ tailWord_2658416) baseStart_2658416 baseEnd_2658416 := by
    simpa [prefixWord, tailWord_2658416, baseEnd_2658416] using wordTrace_append hprefix tailTrace_2658416
  have hstable : (prefixWord ++ tailWord_2658416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658416).length < 2 ^ (prefixWord ++ tailWord_2658416).sum := by decide
  have hdescent : baseEnd_2658416 < baseStart_2658416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658429 : List Nat := [1, 4, 1, 1, 3, 2, 3, 2, 5]
def baseStart_2658429 : Nat := 118140960795 + 2658429 * 2 ^ 59
def prefixEnd_2658429 : Nat := 4983230072969 + 3 ^ 40 * 2658429 * 2
def baseEnd_2658429 : Nat := 303344858411441026224803

theorem tailTrace_2658429 : CollatzResearch.WordTrace tailWord_2658429 prefixEnd_2658429 303344858411441026224803 := by
  unfold tailWord_2658429
  simp only [CollatzResearch.WordTrace]
  refine ⟨96960871285973231371650341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64640580857315487581100227 96960871285973231371650341)
  ·
    refine ⟨18180163366119980882184439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96960871285973231371650341 18180163366119980882184439)
    ·
      refine ⟨27270245049179971323276659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18180163366119980882184439 27270245049179971323276659)
      ·
        refine ⟨40905367573769956984914989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27270245049179971323276659 40905367573769956984914989)
        ·
          refine ⟨15339512840163733869343121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40905367573769956984914989 15339512840163733869343121)
          ·
            refine ⟨11504634630122800402007341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15339512840163733869343121 11504634630122800402007341)
            ·
              refine ⟨4314237986296050150752753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11504634630122800402007341 4314237986296050150752753)
              ·
                refine ⟨3235678489722037613064565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4314237986296050150752753 3235678489722037613064565)
                ·
                  refine ⟨303344858411441026224803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3235678489722037613064565 303344858411441026224803)
                  ·
                    rfl

theorem cell22_2658429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_2658429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658429 prefixEnd_2658429 := by exact prefixLift 2658429
  have htrace : WordTrace (prefixWord ++ tailWord_2658429) baseStart_2658429 baseEnd_2658429 := by
    simpa [prefixWord, tailWord_2658429, baseEnd_2658429] using wordTrace_append hprefix tailTrace_2658429
  have hstable : (prefixWord ++ tailWord_2658429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658429).length < 2 ^ (prefixWord ++ tailWord_2658429).sum := by decide
  have hdescent : baseEnd_2658429 < baseStart_2658429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658484 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2658484 : Nat := 118140960795 + 2658484 * 2 ^ 59
def prefixEnd_2658484 : Nat := 4983230072969 + 3 ^ 40 * 2658484 * 2
def baseEnd_2658484 : Nat := 910053402858321268549241

theorem tailTrace_2658484 : CollatzResearch.WordTrace tailWord_2658484 prefixEnd_2658484 910053402858321268549241 := by
  unfold tailWord_2658484
  simp only [CollatzResearch.WordTrace]
  refine ⟨48481438650386987882451253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64641918200515983843268337 48481438650386987882451253)
  ·
    refine ⟨4545134873473780113979805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48481438650386987882451253 4545134873473780113979805)
    ·
      refine ⟨1704425577552667542742427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4545134873473780113979805 1704425577552667542742427)
      ·
        refine ⟨2556638366329001314113641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1704425577552667542742427 2556638366329001314113641)
        ·
          refine ⟨1917478774746750985585231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2556638366329001314113641 1917478774746750985585231)
          ·
            refine ⟨2876218162120126478377847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917478774746750985585231 2876218162120126478377847)
            ·
              refine ⟨4314327243180189717566771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2876218162120126478377847 4314327243180189717566771)
              ·
                refine ⟨6471490864770284576350157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4314327243180189717566771 6471490864770284576350157)
                ·
                  refine ⟨2426809074288856716131309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6471490864770284576350157 2426809074288856716131309)
                  ·
                    refine ⟨910053402858321268549241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2426809074288856716131309 910053402858321268549241)
                    ·
                      rfl

theorem cell22_2658484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2658484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658484 prefixEnd_2658484 := by exact prefixLift 2658484
  have htrace : WordTrace (prefixWord ++ tailWord_2658484) baseStart_2658484 baseEnd_2658484 := by
    simpa [prefixWord, tailWord_2658484, baseEnd_2658484] using wordTrace_append hprefix tailTrace_2658484
  have hstable : (prefixWord ++ tailWord_2658484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658484).length < 2 ^ (prefixWord ++ tailWord_2658484).sum := by decide
  have hdescent : baseEnd_2658484 < baseStart_2658484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658489 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 4, 3]
def baseStart_2658489 : Nat := 118140960795 + 2658489 * 2 ^ 59
def prefixEnd_2658489 : Nat := 4983230072969 + 3 ^ 40 * 2658489 * 2
def baseEnd_2658489 : Nat := 910055114460502922174225

theorem tailTrace_2658489 : CollatzResearch.WordTrace tailWord_2658489 prefixEnd_2658489 910055114460502922174225 := by
  unfold tailWord_2658489
  simp only [CollatzResearch.WordTrace]
  refine ⟨96963059665755861618834521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64642039777170574412556347 96963059665755861618834521)
  ·
    refine ⟨72722294749316896214125891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96963059665755861618834521 72722294749316896214125891)
    ·
      refine ⟨109083442123975344321188837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72722294749316896214125891 109083442123975344321188837)
      ·
        refine ⟨20453145398245377060222907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109083442123975344321188837 20453145398245377060222907)
        ·
          refine ⟨30679718097368065590334361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20453145398245377060222907 30679718097368065590334361)
          ·
            refine ⟨23009788573026049192750771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30679718097368065590334361 23009788573026049192750771)
            ·
              refine ⟨34514682859539073789126157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23009788573026049192750771 34514682859539073789126157)
              ·
                refine ⟨12943006072327152670922309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34514682859539073789126157 12943006072327152670922309)
                ·
                  refine ⟨2426813638561341125797933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12943006072327152670922309 2426813638561341125797933)
                  ·
                    refine ⟨910055114460502922174225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2426813638561341125797933 910055114460502922174225)
                    ·
                      rfl

theorem cell22_2658489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 3].length) (baseStart_2658489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658489 prefixEnd_2658489 := by exact prefixLift 2658489
  have htrace : WordTrace (prefixWord ++ tailWord_2658489) baseStart_2658489 baseEnd_2658489 := by
    simpa [prefixWord, tailWord_2658489, baseEnd_2658489] using wordTrace_append hprefix tailTrace_2658489
  have hstable : (prefixWord ++ tailWord_2658489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658489).length < 2 ^ (prefixWord ++ tailWord_2658489).sum := by decide
  have hdescent : baseEnd_2658489 < baseStart_2658489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658491 : List Nat := [1, 1, 1, 1, 1, 2, 9, 2, 4]
def baseStart_2658491 : Nat := 118140960795 + 2658491 * 2 ^ 59
def prefixEnd_2658491 : Nat := 4983230072969 + 3 ^ 40 * 2658491 * 2
def baseEnd_2658491 : Nat := 303351933033791861208073

theorem tailTrace_2658491 : CollatzResearch.WordTrace tailWord_2658491 prefixEnd_2658491 303351933033791861208073 := by
  unfold tailWord_2658491
  simp only [CollatzResearch.WordTrace]
  refine ⟨96963132611748615960407327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64642088407832410640271551 96963132611748615960407327)
  ·
    refine ⟨145444698917622923940610991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96963132611748615960407327 145444698917622923940610991)
    ·
      refine ⟨218167048376434385910916487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145444698917622923940610991 218167048376434385910916487)
      ·
        refine ⟨327250572564651578866374731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218167048376434385910916487 327250572564651578866374731)
        ·
          refine ⟨490875858846977368299562097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327250572564651578866374731 490875858846977368299562097)
          ·
            refine ⟨368156894135233026224671573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490875858846977368299562097 368156894135233026224671573)
            ·
              refine ⟨2157169301573631013035185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 368156894135233026224671573 2157169301573631013035185)
              ·
                refine ⟨1617876976180223259776389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2157169301573631013035185 1617876976180223259776389)
                ·
                  refine ⟨303351933033791861208073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1617876976180223259776389 303351933033791861208073)
                  ·
                    rfl

theorem cell22_2658491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 4].length) (baseStart_2658491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658491 prefixEnd_2658491 := by exact prefixLift 2658491
  have htrace : WordTrace (prefixWord ++ tailWord_2658491) baseStart_2658491 baseEnd_2658491 := by
    simpa [prefixWord, tailWord_2658491, baseEnd_2658491] using wordTrace_append hprefix tailTrace_2658491
  have hstable : (prefixWord ++ tailWord_2658491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658491).length < 2 ^ (prefixWord ++ tailWord_2658491).sum := by decide
  have hdescent : baseEnd_2658491 < baseStart_2658491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658506 : List Nat := [3, 1, 2, 1, 3, 1, 3, 3, 2, 3]
def baseStart_2658506 : Nat := 118140960795 + 2658506 * 2 ^ 59
def prefixEnd_2658506 : Nat := 4983230072969 + 3 ^ 40 * 2658506 * 2
def baseEnd_2658506 : Nat := 910060933907920544499173

theorem tailTrace_2658506 : CollatzResearch.WordTrace tailWord_2658506 prefixEnd_2658506 910060933907920544499173 := by
  unfold tailWord_2658506
  simp only [CollatzResearch.WordTrace]
  refine ⟨24240919926673568380550843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64642453137796182348135581 24240919926673568380550843)
  ·
    refine ⟨36361379890010352570826265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24240919926673568380550843 36361379890010352570826265)
    ·
      refine ⟨27271034917507764428119699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36361379890010352570826265 27271034917507764428119699)
      ·
        refine ⟨40906552376261646642179549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27271034917507764428119699 40906552376261646642179549)
        ·
          refine ⟨15339957141098117490817331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40906552376261646642179549 15339957141098117490817331)
          ·
            refine ⟨23009935711647176236225997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15339957141098117490817331 23009935711647176236225997)
            ·
              refine ⟨8628725891867691088584749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23009935711647176236225997 8628725891867691088584749)
              ·
                refine ⟨3235772209450384158219281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8628725891867691088584749 3235772209450384158219281)
                ·
                  refine ⟨2426829157087788118664461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3235772209450384158219281 2426829157087788118664461)
                  ·
                    refine ⟨910060933907920544499173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2426829157087788118664461 910060933907920544499173)
                    ·
                      rfl

theorem cell22_2658506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_2658506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658506 prefixEnd_2658506 := by exact prefixLift 2658506
  have htrace : WordTrace (prefixWord ++ tailWord_2658506) baseStart_2658506 baseEnd_2658506 := by
    simpa [prefixWord, tailWord_2658506, baseEnd_2658506] using wordTrace_append hprefix tailTrace_2658506
  have hstable : (prefixWord ++ tailWord_2658506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658506).length < 2 ^ (prefixWord ++ tailWord_2658506).sum := by decide
  have hdescent : baseEnd_2658506 < baseStart_2658506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658624 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 1, 5]
def baseStart_2658624 : Nat := 118140960795 + 2658624 * 2 ^ 59
def prefixEnd_2658624 : Nat := 4983230072969 + 3 ^ 40 * 2658624 * 2
def baseEnd_2658624 : Nat := 910101327719407570048811

theorem tailTrace_2658624 : CollatzResearch.WordTrace tailWord_2658624 prefixEnd_2658624 910101327719407570048811 := by
  unfold tailWord_2658624
  simp only [CollatzResearch.WordTrace]
  refine ⟨48483991760133389837499463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64645322346844519783332617 48483991760133389837499463)
  ·
    refine ⟨72725987640200084756249195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48483991760133389837499463 72725987640200084756249195)
    ·
      refine ⟨109088981460300127134373793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72725987640200084756249195 109088981460300127134373793)
      ·
        refine ⟨81816736095225095350780345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109088981460300127134373793 81816736095225095350780345)
        ·
          refine ⟨61362552071418821513085259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81816736095225095350780345 61362552071418821513085259)
          ·
            refine ⟨92043828107128232269627889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61362552071418821513085259 92043828107128232269627889)
            ·
              refine ⟨69032871080346174202220917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92043828107128232269627889 69032871080346174202220917)
              ·
                refine ⟨6471831663782453831458211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69032871080346174202220917 6471831663782453831458211)
                ·
                  refine ⟨9707747495673680747187317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6471831663782453831458211 9707747495673680747187317)
                  ·
                    refine ⟨910101327719407570048811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9707747495673680747187317 910101327719407570048811)
                    ·
                      rfl

theorem cell22_2658624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_2658624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658624 prefixEnd_2658624 := by exact prefixLift 2658624
  have htrace : WordTrace (prefixWord ++ tailWord_2658624) baseStart_2658624 baseEnd_2658624 := by
    simpa [prefixWord, tailWord_2658624, baseEnd_2658624] using wordTrace_append hprefix tailTrace_2658624
  have hstable : (prefixWord ++ tailWord_2658624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658624).length < 2 ^ (prefixWord ++ tailWord_2658624).sum := by decide
  have hdescent : baseEnd_2658624 < baseStart_2658624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658641 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 4, 3]
def baseStart_2658641 : Nat := 118140960795 + 2658641 * 2 ^ 59
def prefixEnd_2658641 : Nat := 4983230072969 + 3 ^ 40 * 2658641 * 2
def baseEnd_2658641 : Nat := 910107147166825192373759

theorem tailTrace_2658641 : CollatzResearch.WordTrace tailWord_2658641 prefixEnd_2658641 910107147166825192373759 := by
  unfold tailWord_2658641
  simp only [CollatzResearch.WordTrace]
  refine ⟨96968603561205191578367777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64645735707470127718911851 96968603561205191578367777)
  ·
    refine ⟨72726452670903893683775833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96968603561205191578367777 72726452670903893683775833)
    ·
      refine ⟨54544839503177920262831875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72726452670903893683775833 54544839503177920262831875)
      ·
        refine ⟨81817259254766880394247813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54544839503177920262831875 81817259254766880394247813)
        ·
          refine ⟨15340736110268790073921465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81817259254766880394247813 15340736110268790073921465)
          ·
            refine ⟨11505552082701592555441099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15340736110268790073921465 11505552082701592555441099)
            ·
              refine ⟨17258328124052388833161649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11505552082701592555441099 17258328124052388833161649)
              ·
                refine ⟨12943746093039291624871237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17258328124052388833161649 12943746093039291624871237)
                ·
                  refine ⟨2426952392444867179663357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12943746093039291624871237 2426952392444867179663357)
                  ·
                    refine ⟨910107147166825192373759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2426952392444867179663357 910107147166825192373759)
                    ·
                      rfl

theorem cell22_2658641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_2658641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658641 prefixEnd_2658641 := by exact prefixLift 2658641
  have htrace : WordTrace (prefixWord ++ tailWord_2658641) baseStart_2658641 baseEnd_2658641 := by
    simpa [prefixWord, tailWord_2658641, baseEnd_2658641] using wordTrace_append hprefix tailTrace_2658641
  have hstable : (prefixWord ++ tailWord_2658641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658641).length < 2 ^ (prefixWord ++ tailWord_2658641).sum := by decide
  have hdescent : baseEnd_2658641 < baseStart_2658641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658658 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_2658658 : Nat := 118140960795 + 2658658 * 2 ^ 59
def prefixEnd_2658658 : Nat := 4983230072969 + 3 ^ 40 * 2658658 * 2
def baseEnd_2658658 : Nat := 910112966614242814698707

theorem tailTrace_2658658 : CollatzResearch.WordTrace tailWord_2658658 prefixEnd_2658658 910112966614242814698707 := by
  unfold tailWord_2658658
  simp only [CollatzResearch.WordTrace]
  refine ⟨24242305900535900870434157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64646149068095735654491085 24242305900535900870434157)
  ·
    refine ⟨9090864712700962826412809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24242305900535900870434157 9090864712700962826412809)
    ·
      refine ⟨6818148534525722119809607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9090864712700962826412809 6818148534525722119809607)
      ·
        refine ⟨10227222801788583179714411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6818148534525722119809607 10227222801788583179714411)
        ·
          refine ⟨15340834202682874769571617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10227222801788583179714411 15340834202682874769571617)
          ·
            refine ⟨11505625652012156077178713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15340834202682874769571617 11505625652012156077178713)
            ·
              refine ⟨8629219239009117057884035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11505625652012156077178713 8629219239009117057884035)
              ·
                refine ⟨12943828858513675586826053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8629219239009117057884035 12943828858513675586826053)
                ·
                  refine ⟨2426967910971314172529885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12943828858513675586826053 2426967910971314172529885)
                  ·
                    refine ⟨910112966614242814698707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2426967910971314172529885 910112966614242814698707)
                    ·
                      rfl

theorem cell22_2658658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_2658658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658658 prefixEnd_2658658 := by exact prefixLift 2658658
  have htrace : WordTrace (prefixWord ++ tailWord_2658658) baseStart_2658658 baseEnd_2658658 := by
    simpa [prefixWord, tailWord_2658658, baseEnd_2658658] using wordTrace_append hprefix tailTrace_2658658
  have hstable : (prefixWord ++ tailWord_2658658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658658).length < 2 ^ (prefixWord ++ tailWord_2658658).sum := by decide
  have hdescent : baseEnd_2658658 < baseStart_2658658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658684 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_2658684 : Nat := 118140960795 + 2658684 * 2 ^ 59
def prefixEnd_2658684 : Nat := 4983230072969 + 3 ^ 40 * 2658684 * 2
def baseEnd_2658684 : Nat := 910121866945587413548627

theorem tailTrace_2658684 : CollatzResearch.WordTrace tailWord_2658684 prefixEnd_2658684 910121866945587413548627 := by
  unfold tailWord_2658684
  simp only [CollatzResearch.WordTrace]
  refine ⟨48485085950024704961091553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64646781266699606614788737 48485085950024704961091553)
  ·
    refine ⟨36363814462518528720818665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48485085950024704961091553 36363814462518528720818665)
    ·
      refine ⟨27272860846888896540613999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36363814462518528720818665 27272860846888896540613999)
      ·
        refine ⟨40909291270333344810920999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27272860846888896540613999 40909291270333344810920999)
        ·
          refine ⟨61363936905500017216381499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40909291270333344810920999 61363936905500017216381499)
          ·
            refine ⟨92045905358250025824572249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61363936905500017216381499 92045905358250025824572249)
            ·
              refine ⟨69034429018687519368429187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92045905358250025824572249 69034429018687519368429187)
              ·
                refine ⟨103551643528031279052643781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69034429018687519368429187 103551643528031279052643781)
                ·
                  refine ⟨19415933161505864822370709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103551643528031279052643781 19415933161505864822370709)
                  ·
                    refine ⟨910121866945587413548627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19415933161505864822370709 910121866945587413548627)
                    ·
                      rfl

theorem cell22_2658684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_2658684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658684 prefixEnd_2658684 := by exact prefixLift 2658684
  have htrace : WordTrace (prefixWord ++ tailWord_2658684) baseStart_2658684 baseEnd_2658684 := by
    simpa [prefixWord, tailWord_2658684, baseEnd_2658684] using wordTrace_append hprefix tailTrace_2658684
  have hstable : (prefixWord ++ tailWord_2658684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658684).length < 2 ^ (prefixWord ++ tailWord_2658684).sum := by decide
  have hdescent : baseEnd_2658684 < baseStart_2658684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658718 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2658718 : Nat := 118140960795 + 2658718 * 2 ^ 59
def prefixEnd_2658718 : Nat := 4983230072969 + 3 ^ 40 * 2658718 * 2
def baseEnd_2658718 : Nat := 910133505840422658198523

theorem tailTrace_2658718 : CollatzResearch.WordTrace tailWord_2658718 prefixEnd_2658718 910133505840422658198523 := by
  unfold tailWord_2658718
  simp only [CollatzResearch.WordTrace]
  refine ⟨12121426497740779216115101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64647607987950822485947205 12121426497740779216115101)
  ·
    refine ⟨4545534936652792206043163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12121426497740779216115101 4545534936652792206043163)
    ·
      refine ⟨6818302404979188309064745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4545534936652792206043163 6818302404979188309064745)
      ·
        refine ⟨5113726803734391231798559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6818302404979188309064745 5113726803734391231798559)
        ·
          refine ⟨7670590205601586847697839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5113726803734391231798559 7670590205601586847697839)
          ·
            refine ⟨11505885308402380271546759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7670590205601586847697839 11505885308402380271546759)
            ·
              refine ⟨17258827962603570407320139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11505885308402380271546759 17258827962603570407320139)
              ·
                refine ⟨25888241943905355610980209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17258827962603570407320139 25888241943905355610980209)
                ·
                  refine ⟨19416181457929016708235157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25888241943905355610980209 19416181457929016708235157)
                  ·
                    refine ⟨910133505840422658198523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19416181457929016708235157 910133505840422658198523)
                    ·
                      rfl

theorem cell22_2658718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2658718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658718 prefixEnd_2658718 := by exact prefixLift 2658718
  have htrace : WordTrace (prefixWord ++ tailWord_2658718) baseStart_2658718 baseEnd_2658718 := by
    simpa [prefixWord, tailWord_2658718, baseEnd_2658718] using wordTrace_append hprefix tailTrace_2658718
  have hstable : (prefixWord ++ tailWord_2658718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658718).length < 2 ^ (prefixWord ++ tailWord_2658718).sum := by decide
  have hdescent : baseEnd_2658718 < baseStart_2658718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658720 : List Nat := [2, 1, 1, 4, 1, 4, 1, 4, 1, 3]
def baseStart_2658720 : Nat := 118140960795 + 2658720 * 2 ^ 59
def prefixEnd_2658720 : Nat := 4983230072969 + 3 ^ 40 * 2658720 * 2
def baseEnd_2658720 : Nat := 910134190481295319648517

theorem tailTrace_2658720 : CollatzResearch.WordTrace tailWord_2658720 prefixEnd_2658720 910134190481295319648517 := by
  unfold tailWord_2658720
  simp only [CollatzResearch.WordTrace]
  refine ⟨48485742463959494035246807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64647656618612658713662409 48485742463959494035246807)
  ·
    refine ⟨72728613695939241052870211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48485742463959494035246807 72728613695939241052870211)
    ·
      refine ⟨109092920543908861579305317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72728613695939241052870211 109092920543908861579305317)
      ·
        refine ⟨20454922601982911546119747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109092920543908861579305317 20454922601982911546119747)
        ·
          refine ⟨30682383902974367319179621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20454922601982911546119747 30682383902974367319179621)
          ·
            refine ⟨5752946981807693872346179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30682383902974367319179621 5752946981807693872346179)
            ·
              refine ⟨8629420472711540808519269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5752946981807693872346179 8629420472711540808519269)
              ·
                refine ⟨1618016338633413901597363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8629420472711540808519269 1618016338633413901597363)
                ·
                  refine ⟨2427024507950120852396045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618016338633413901597363 2427024507950120852396045)
                  ·
                    refine ⟨910134190481295319648517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2427024507950120852396045 910134190481295319648517)
                    ·
                      rfl

theorem cell22_2658720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 1, 3].length) (baseStart_2658720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658720 prefixEnd_2658720 := by exact prefixLift 2658720
  have htrace : WordTrace (prefixWord ++ tailWord_2658720) baseStart_2658720 baseEnd_2658720 := by
    simpa [prefixWord, tailWord_2658720, baseEnd_2658720] using wordTrace_append hprefix tailTrace_2658720
  have hstable : (prefixWord ++ tailWord_2658720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658720).length < 2 ^ (prefixWord ++ tailWord_2658720).sum := by decide
  have hdescent : baseEnd_2658720 < baseStart_2658720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658778 : List Nat := [3, 1, 1, 2, 3, 1, 1, 6, 4]
def baseStart_2658778 : Nat := 118140960795 + 2658778 * 2 ^ 59
def prefixEnd_2658778 : Nat := 4983230072969 + 3 ^ 40 * 2658778 * 2
def baseEnd_2658778 : Nat := 303384681688867500566113

theorem tailTrace_2658778 : CollatzResearch.WordTrace tailWord_2658778 prefixEnd_2658778 303384681688867500566113 := by
  unfold tailWord_2658778
  simp only [CollatzResearch.WordTrace]
  refine ⟨24243400090427215994026247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64649066907805909317403325 24243400090427215994026247)
  ·
    refine ⟨36365100135640823991039371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24243400090427215994026247 36365100135640823991039371)
    ·
      refine ⟨54547650203461235986559057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36365100135640823991039371 54547650203461235986559057)
      ·
        refine ⟨40910737652595926989919293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54547650203461235986559057 40910737652595926989919293)
        ·
          refine ⟨15341526619723472621219735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40910737652595926989919293 15341526619723472621219735)
          ·
            refine ⟨23012289929585208931829603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15341526619723472621219735 23012289929585208931829603)
            ·
              refine ⟨34518434894377813397744405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23012289929585208931829603 34518434894377813397744405)
              ·
                refine ⟨1618051635673960003019269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34518434894377813397744405 1618051635673960003019269)
                ·
                  refine ⟨303384681688867500566113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1618051635673960003019269 303384681688867500566113)
                  ·
                    rfl

theorem cell22_2658778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_2658778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658778 prefixEnd_2658778 := by exact prefixLift 2658778
  have htrace : WordTrace (prefixWord ++ tailWord_2658778) baseStart_2658778 baseEnd_2658778 := by
    simpa [prefixWord, tailWord_2658778, baseEnd_2658778] using wordTrace_append hprefix tailTrace_2658778
  have hstable : (prefixWord ++ tailWord_2658778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658778).length < 2 ^ (prefixWord ++ tailWord_2658778).sum := by decide
  have hdescent : baseEnd_2658778 < baseStart_2658778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658791 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2658791 : Nat := 118140960795 + 2658791 * 2 ^ 59
def prefixEnd_2658791 : Nat := 4983230072969 + 3 ^ 40 * 2658791 * 2
def baseEnd_2658791 : Nat := 910158495232274801123299

theorem tailTrace_2658791 : CollatzResearch.WordTrace tailWord_2658791 prefixEnd_2658791 910158495232274801123299 := by
  unfold tailWord_2658791
  simp only [CollatzResearch.WordTrace]
  refine ⟨96974074510661767196328227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64649383007107844797552151 96974074510661767196328227)
  ·
    refine ⟨145461111765992650794492341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96974074510661767196328227 145461111765992650794492341)
    ·
      refine ⟨13636979228061811011983657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145461111765992650794492341 13636979228061811011983657)
      ·
        refine ⟨10227734421046358258987743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13636979228061811011983657 10227734421046358258987743)
        ·
          refine ⟨15341601631569537388481615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10227734421046358258987743 15341601631569537388481615)
          ·
            refine ⟨23012402447354306082722423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15341601631569537388481615 23012402447354306082722423)
            ·
              refine ⟨34518603671031459124083635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23012402447354306082722423 34518603671031459124083635)
              ·
                refine ⟨51777905506547188686125453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34518603671031459124083635 51777905506547188686125453)
                ·
                  refine ⟨19416714564955195757297045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51777905506547188686125453 19416714564955195757297045)
                  ·
                    refine ⟨910158495232274801123299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19416714564955195757297045 910158495232274801123299)
                    ·
                      rfl

theorem cell22_2658791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2658791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658791 prefixEnd_2658791 := by exact prefixLift 2658791
  have htrace : WordTrace (prefixWord ++ tailWord_2658791) baseStart_2658791 baseEnd_2658791 := by
    simpa [prefixWord, tailWord_2658791, baseEnd_2658791] using wordTrace_append hprefix tailTrace_2658791
  have hstable : (prefixWord ++ tailWord_2658791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658791).length < 2 ^ (prefixWord ++ tailWord_2658791).sum := by decide
  have hdescent : baseEnd_2658791 < baseStart_2658791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658823 : List Nat := [1, 1, 4, 3, 3, 2, 8]
def baseStart_2658823 : Nat := 118140960795 + 2658823 * 2 ^ 59
def prefixEnd_2658823 : Nat := 4983230072969 + 3 ^ 40 * 2658823 * 2
def baseEnd_2658823 : Nat := 33709979610601384604563

theorem tailTrace_2658823 : CollatzResearch.WordTrace tailWord_2658823 prefixEnd_2658823 33709979610601384604563 := by
  unfold tailWord_2658823
  simp only [CollatzResearch.WordTrace]
  refine ⟨96975241646545836661493123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64650161097697224440995415 96975241646545836661493123)
  ·
    refine ⟨145462862469818754992239685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96975241646545836661493123 145462862469818754992239685)
    ·
      refine ⟨27274286713091016561044941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145462862469818754992239685 27274286713091016561044941)
      ·
        refine ⟨10227857517409131210391853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27274286713091016561044941 10227857517409131210391853)
        ·
          refine ⟨3835446569028424203896945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10227857517409131210391853 3835446569028424203896945)
          ·
            refine ⟨2876584926771318152922709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3835446569028424203896945 2876584926771318152922709)
            ·
              refine ⟨33709979610601384604563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2876584926771318152922709 33709979610601384604563)
              ·
                rfl

theorem cell22_2658823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 8].length) (baseStart_2658823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658823 prefixEnd_2658823 := by exact prefixLift 2658823
  have htrace : WordTrace (prefixWord ++ tailWord_2658823) baseStart_2658823 baseEnd_2658823 := by
    simpa [prefixWord, tailWord_2658823, baseEnd_2658823] using wordTrace_append hprefix tailTrace_2658823
  have hstable : (prefixWord ++ tailWord_2658823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658823).length < 2 ^ (prefixWord ++ tailWord_2658823).sum := by decide
  have hdescent : baseEnd_2658823 < baseStart_2658823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658898 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_2658898 : Nat := 118140960795 + 2658898 * 2 ^ 59
def prefixEnd_2658898 : Nat := 4983230072969 + 3 ^ 40 * 2658898 * 2
def baseEnd_2658898 : Nat := 910195123518962188697971

theorem tailTrace_2658898 : CollatzResearch.WordTrace tailWord_2658898 prefixEnd_2658898 910195123518962188697971 := by
  unfold tailWord_2658898
  simp only [CollatzResearch.WordTrace]
  refine ⟨24244494280318531117618337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64651984747516082980315565 24244494280318531117618337)
  ·
    refine ⟨18183370710238898338213753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24244494280318531117618337 18183370710238898338213753)
    ·
      refine ⟨13637528032679173753660315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18183370710238898338213753 13637528032679173753660315)
      ·
        refine ⟨20456292049018760630490473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13637528032679173753660315 20456292049018760630490473)
        ·
          refine ⟨15342219036764070472867855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20456292049018760630490473 15342219036764070472867855)
          ·
            refine ⟨23013328555146105709301783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15342219036764070472867855 23013328555146105709301783)
            ·
              refine ⟨34519992832719158563952675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23013328555146105709301783 34519992832719158563952675)
              ·
                refine ⟨51779989249078737845929013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34519992832719158563952675 51779989249078737845929013)
                ·
                  refine ⟨4854373992101131673055845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51779989249078737845929013 4854373992101131673055845)
                  ·
                    refine ⟨910195123518962188697971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4854373992101131673055845 910195123518962188697971)
                    ·
                      rfl

theorem cell22_2658898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_2658898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658898 prefixEnd_2658898 := by exact prefixLift 2658898
  have htrace : WordTrace (prefixWord ++ tailWord_2658898) baseStart_2658898 baseEnd_2658898 := by
    simpa [prefixWord, tailWord_2658898, baseEnd_2658898] using wordTrace_append hprefix tailTrace_2658898
  have hstable : (prefixWord ++ tailWord_2658898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658898).length < 2 ^ (prefixWord ++ tailWord_2658898).sum := by decide
  have hdescent : baseEnd_2658898 < baseStart_2658898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658913 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 6]
def baseStart_2658913 : Nat := 118140960795 + 2658913 * 2 ^ 59
def prefixEnd_2658913 : Nat := 4983230072969 + 3 ^ 40 * 2658913 * 2
def baseEnd_2658913 : Nat := 303400086108502383190975

theorem tailTrace_2658913 : CollatzResearch.WordTrace tailWord_2658913 prefixEnd_2658913 303400086108502383190975 := by
  unfold tailWord_2658913
  simp only [CollatzResearch.WordTrace]
  refine ⟨96978524216219782032269393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64652349477479854688179595 96978524216219782032269393)
  ·
    refine ⟨72733893162164836524202045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96978524216219782032269393 72733893162164836524202045)
    ·
      refine ⟨27275209935811813696575767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72733893162164836524202045 27275209935811813696575767)
      ·
        refine ⟨40912814903717720544863651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27275209935811813696575767 40912814903717720544863651)
        ·
          refine ⟨61369222355576580817295477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40912814903717720544863651 61369222355576580817295477)
          ·
            refine ⟨5753364595835304451621451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61369222355576580817295477 5753364595835304451621451)
            ·
              refine ⟨8630046893752956677432177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5753364595835304451621451 8630046893752956677432177)
              ·
                refine ⟨6472535170314717508074133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8630046893752956677432177 6472535170314717508074133)
                ·
                  refine ⟨303400086108502383190975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6472535170314717508074133 303400086108502383190975)
                  ·
                    rfl

theorem cell22_2658913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 6].length) (baseStart_2658913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658913 prefixEnd_2658913 := by exact prefixLift 2658913
  have htrace : WordTrace (prefixWord ++ tailWord_2658913) baseStart_2658913 baseEnd_2658913 := by
    simpa [prefixWord, tailWord_2658913, baseEnd_2658913] using wordTrace_append hprefix tailTrace_2658913
  have hstable : (prefixWord ++ tailWord_2658913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658913).length < 2 ^ (prefixWord ++ tailWord_2658913).sum := by decide
  have hdescent : baseEnd_2658913 < baseStart_2658913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658945 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 4, 3]
def baseStart_2658945 : Nat := 118140960795 + 2658945 * 2 ^ 59
def prefixEnd_2658945 : Nat := 4983230072969 + 3 ^ 40 * 2658945 * 2
def baseEnd_2658945 : Nat := 910211212579469732772827

theorem tailTrace_2658945 : CollatzResearch.WordTrace tailWord_2658945 prefixEnd_2658945 910211212579469732772827 := by
  unfold tailWord_2658945
  simp only [CollatzResearch.WordTrace]
  refine ⟨96979691352103851497434289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64653127568069234331622859 96979691352103851497434289)
  ·
    refine ⟨72734768514077888623075717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96979691352103851497434289 72734768514077888623075717)
    ·
      refine ⟨13637769096389604116826697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72734768514077888623075717 13637769096389604116826697)
      ·
        refine ⟨10228326822292203087620023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13637769096389604116826697 10228326822292203087620023)
        ·
          refine ⟨15342490233438304631430035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10228326822292203087620023 15342490233438304631430035)
          ·
            refine ⟨23013735350157456947145053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15342490233438304631430035 23013735350157456947145053)
            ·
              refine ⟨8630150756309046355179395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23013735350157456947145053 8630150756309046355179395)
              ·
                refine ⟨12945226134463569532769093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8630150756309046355179395 12945226134463569532769093)
                ·
                  refine ⟨2427229900211919287394205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12945226134463569532769093 2427229900211919287394205)
                  ·
                    refine ⟨910211212579469732772827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2427229900211919287394205 910211212579469732772827)
                    ·
                      rfl

theorem cell22_2658945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_2658945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658945 prefixEnd_2658945 := by exact prefixLift 2658945
  have htrace : WordTrace (prefixWord ++ tailWord_2658945) baseStart_2658945 baseEnd_2658945 := by
    simpa [prefixWord, tailWord_2658945, baseEnd_2658945] using wordTrace_append hprefix tailTrace_2658945
  have hstable : (prefixWord ++ tailWord_2658945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658945).length < 2 ^ (prefixWord ++ tailWord_2658945).sum := by decide
  have hdescent : baseEnd_2658945 < baseStart_2658945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658958 : List Nat := [4, 1, 1, 3, 1, 1, 2, 9]
def baseStart_2658958 : Nat := 118140960795 + 2658958 * 2 ^ 59
def prefixEnd_2658958 : Nat := 4983230072969 + 3 ^ 40 * 2658958 * 2
def baseEnd_2658958 : Nat := 101135073638349114688643

theorem tailTrace_2658958 : CollatzResearch.WordTrace tailWord_2658958 prefixEnd_2658958 101135073638349114688643 := by
  unfold tailWord_2658958
  simp only [CollatzResearch.WordTrace]
  refine ⟨12122520687632094339707191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64653443667371169811771685 12122520687632094339707191)
  ·
    refine ⟨18183781031448141509560787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12122520687632094339707191 18183781031448141509560787)
    ·
      refine ⟨27275671547172212264341181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18183781031448141509560787 27275671547172212264341181)
      ·
        refine ⟨10228376830189579599127943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27275671547172212264341181 10228376830189579599127943)
        ·
          refine ⟨15342565245284369398691915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10228376830189579599127943 15342565245284369398691915)
          ·
            refine ⟨23013847867926554098037873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15342565245284369398691915 23013847867926554098037873)
            ·
              refine ⟨17260385900944915573528405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23013847867926554098037873 17260385900944915573528405)
              ·
                refine ⟨101135073638349114688643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17260385900944915573528405 101135073638349114688643)
                ·
                  rfl

theorem cell22_2658958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_2658958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658958 prefixEnd_2658958 := by exact prefixLift 2658958
  have htrace : WordTrace (prefixWord ++ tailWord_2658958) baseStart_2658958 baseEnd_2658958 := by
    simpa [prefixWord, tailWord_2658958, baseEnd_2658958] using wordTrace_append hprefix tailTrace_2658958
  have hstable : (prefixWord ++ tailWord_2658958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658958).length < 2 ^ (prefixWord ++ tailWord_2658958).sum := by decide
  have hdescent : baseEnd_2658958 < baseStart_2658958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658962 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_2658962 : Nat := 118140960795 + 2658962 * 2 ^ 59
def prefixEnd_2658962 : Nat := 4983230072969 + 3 ^ 40 * 2658962 * 2
def baseEnd_2658962 : Nat := 910217032026887355097775

theorem tailTrace_2658962 : CollatzResearch.WordTrace tailWord_2658962 prefixEnd_2658962 910217032026887355097775 := by
  unfold tailWord_2658962
  simp only [CollatzResearch.WordTrace]
  refine ⟨24245077848260565850200785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64653540928694842267202093 24245077848260565850200785)
  ·
    refine ⟨18183808386195424387650589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24245077848260565850200785 18183808386195424387650589)
    ·
      refine ⟨6818928144823284145368971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18183808386195424387650589 6818928144823284145368971)
      ·
        refine ⟨10228392217234926218053457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6818928144823284145368971 10228392217234926218053457)
        ·
          refine ⟨7671294162926194663540093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10228392217234926218053457 7671294162926194663540093)
          ·
            refine ⟨2876735311097322998827535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7671294162926194663540093 2876735311097322998827535)
            ·
              refine ⟨4315102966645984498241303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2876735311097322998827535 4315102966645984498241303)
              ·
                refine ⟨6472654449968976747361955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4315102966645984498241303 6472654449968976747361955)
                ·
                  refine ⟨9708981674953465121042933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6472654449968976747361955 9708981674953465121042933)
                  ·
                    refine ⟨910217032026887355097775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9708981674953465121042933 910217032026887355097775)
                    ·
                      rfl

theorem cell22_2658962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_2658962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658962 prefixEnd_2658962 := by exact prefixLift 2658962
  have htrace : WordTrace (prefixWord ++ tailWord_2658962) baseStart_2658962 baseEnd_2658962 := by
    simpa [prefixWord, tailWord_2658962, baseEnd_2658962] using wordTrace_append hprefix tailTrace_2658962
  have hstable : (prefixWord ++ tailWord_2658962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658962).length < 2 ^ (prefixWord ++ tailWord_2658962).sum := by decide
  have hdescent : baseEnd_2658962 < baseStart_2658962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659007 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 3, 3]
def baseStart_2659007 : Nat := 118140960795 + 2659007 * 2 ^ 59
def prefixEnd_2659007 : Nat := 4983230072969 + 3 ^ 40 * 2659007 * 2
def baseEnd_2659007 : Nat := 910232436446522237722637

theorem tailTrace_2659007 : CollatzResearch.WordTrace tailWord_2659007 prefixEnd_2659007 910232436446522237722637 := by
  unfold tailWord_2659007
  simp only [CollatzResearch.WordTrace]
  refine ⟨96981952677879236086191275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64654635118586157390794183 96981952677879236086191275)
  ·
    refine ⟨145472929016818854129286913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96981952677879236086191275 145472929016818854129286913)
    ·
      refine ⟨109104696762614140596965185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145472929016818854129286913 109104696762614140596965185)
      ·
        refine ⟨81828522571960605447723889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109104696762614140596965185 81828522571960605447723889)
        ·
          refine ⟨61371391928970454085792917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81828522571960605447723889 61371391928970454085792917)
          ·
            refine ⟨2876783996670490035271543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61371391928970454085792917 2876783996670490035271543)
            ·
              refine ⟨4315175995005735052907315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2876783996670490035271543 4315175995005735052907315)
              ·
                refine ⟨6472763992508602579360973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4315175995005735052907315 6472763992508602579360973)
                ·
                  refine ⟨2427286497190725967260365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6472763992508602579360973 2427286497190725967260365)
                  ·
                    refine ⟨910232436446522237722637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2427286497190725967260365 910232436446522237722637)
                    ·
                      rfl

theorem cell22_2659007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 3].length) (baseStart_2659007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659007 prefixEnd_2659007 := by exact prefixLift 2659007
  have htrace : WordTrace (prefixWord ++ tailWord_2659007) baseStart_2659007 baseEnd_2659007 := by
    simpa [prefixWord, tailWord_2659007, baseEnd_2659007] using wordTrace_append hprefix tailTrace_2659007
  have hstable : (prefixWord ++ tailWord_2659007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659007).length < 2 ^ (prefixWord ++ tailWord_2659007).sum := by decide
  have hdescent : baseEnd_2659007 < baseStart_2659007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659063 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 5, 5]
def baseStart_2659063 : Nat := 118140960795 + 2659063 * 2 ^ 59
def prefixEnd_2659063 : Nat := 4983230072969 + 3 ^ 40 * 2659063 * 2
def baseEnd_2659063 : Nat := 910251606390956758322465

theorem tailTrace_2659063 : CollatzResearch.WordTrace tailWord_2659063 prefixEnd_2659063 910251606390956758322465 := by
  unfold tailWord_2659063
  simp only [CollatzResearch.WordTrace]
  refine ⟨96983995165676357650229843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64655996777117571766819895 96983995165676357650229843)
  ·
    refine ⟨145475992748514536475344765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96983995165676357650229843 145475992748514536475344765)
    ·
      refine ⟨54553497280692951178254287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145475992748514536475344765 54553497280692951178254287)
      ·
        refine ⟨81830245921039426767381431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54553497280692951178254287 81830245921039426767381431)
        ·
          refine ⟨122745368881559140151072147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81830245921039426767381431 122745368881559140151072147)
          ·
            refine ⟨184118053322338710226608221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122745368881559140151072147 184118053322338710226608221)
            ·
              refine ⟨69044269995877016334978083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184118053322338710226608221 69044269995877016334978083)
              ·
                refine ⟨103566404993815524502467125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69044269995877016334978083 103566404993815524502467125)
                ·
                  refine ⟨9709350468170205422106293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103566404993815524502467125 9709350468170205422106293)
                  ·
                    refine ⟨910251606390956758322465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9709350468170205422106293 910251606390956758322465)
                    ·
                      rfl

theorem cell22_2659063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_2659063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659063 prefixEnd_2659063 := by exact prefixLift 2659063
  have htrace : WordTrace (prefixWord ++ tailWord_2659063) baseStart_2659063 baseEnd_2659063 := by
    simpa [prefixWord, tailWord_2659063, baseEnd_2659063] using wordTrace_append hprefix tailTrace_2659063
  have hstable : (prefixWord ++ tailWord_2659063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659063).length < 2 ^ (prefixWord ++ tailWord_2659063).sum := by decide
  have hdescent : baseEnd_2659063 < baseStart_2659063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659080 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 1, 5]
def baseStart_2659080 : Nat := 118140960795 + 2659080 * 2 ^ 59
def prefixEnd_2659080 : Nat := 4983230072969 + 3 ^ 40 * 2659080 * 2
def baseEnd_2659080 : Nat := 910257425838374380647413

theorem tailTrace_2659080 : CollatzResearch.WordTrace tailWord_2659080 prefixEnd_2659080 910257425838374380647413 := by
  unfold tailWord_2659080
  simp only [CollatzResearch.WordTrace]
  refine ⟨48492307603307384776799347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64656410137743179702399129 48492307603307384776799347)
  ·
    refine ⟨72738461404961077165199021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48492307603307384776799347 72738461404961077165199021)
    ·
      refine ⟨27276923026860403936949633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72738461404961077165199021 27276923026860403936949633)
      ·
        refine ⟨20457692270145302952712225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27276923026860403936949633 20457692270145302952712225)
        ·
          refine ⟨15343269202608977214534169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20457692270145302952712225 15343269202608977214534169)
          ·
            refine ⟨11507451901956732910900627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15343269202608977214534169 11507451901956732910900627)
            ·
              refine ⟨17261177852935099366350941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11507451901956732910900627 17261177852935099366350941)
              ·
                refine ⟨6472941694850662262381603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17261177852935099366350941 6472941694850662262381603)
                ·
                  refine ⟨9709412542275993393572405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6472941694850662262381603 9709412542275993393572405)
                  ·
                    refine ⟨910257425838374380647413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9709412542275993393572405 910257425838374380647413)
                    ·
                      rfl

theorem cell22_2659080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_2659080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659080 prefixEnd_2659080 := by exact prefixLift 2659080
  have htrace : WordTrace (prefixWord ++ tailWord_2659080) baseStart_2659080 baseEnd_2659080 := by
    simpa [prefixWord, tailWord_2659080, baseEnd_2659080] using wordTrace_append hprefix tailTrace_2659080
  have hstable : (prefixWord ++ tailWord_2659080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659080).length < 2 ^ (prefixWord ++ tailWord_2659080).sum := by decide
  have hdescent : baseEnd_2659080 < baseStart_2659080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659189 : List Nat := [1, 3, 4, 1, 1, 2, 4, 1, 5]
def baseStart_2659189 : Nat := 118140960795 + 2659189 * 2 ^ 59
def prefixEnd_2659189 : Nat := 4983230072969 + 3 ^ 40 * 2659189 * 2
def baseEnd_2659189 : Nat := 303431579588644809890693

theorem tailTrace_2659189 : CollatzResearch.WordTrace tailWord_2659189 prefixEnd_2659189 303431579588644809890693 := by
  unfold tailWord_2659189
  simp only [CollatzResearch.WordTrace]
  refine ⟨96988590763219881169316621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64659060508813254112877747 96988590763219881169316621)
  ·
    refine ⟨36370721536207455438493733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96988590763219881169316621 36370721536207455438493733)
    ·
      refine ⟨6819510288038897894717575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36370721536207455438493733 6819510288038897894717575)
      ·
        refine ⟨10229265432058346842076363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6819510288038897894717575 10229265432058346842076363)
        ·
          refine ⟨15343898148087520263114545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10229265432058346842076363 15343898148087520263114545)
          ·
            refine ⟨11507923611065640197335909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15343898148087520263114545 11507923611065640197335909)
            ·
              refine ⟨2157735677074807537000483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11507923611065640197335909 2157735677074807537000483)
              ·
                refine ⟨3236603515612211305500725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2157735677074807537000483 3236603515612211305500725)
                ·
                  refine ⟨303431579588644809890693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3236603515612211305500725 303431579588644809890693)
                  ·
                    rfl

theorem cell22_2659189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_2659189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659189 prefixEnd_2659189 := by exact prefixLift 2659189
  have htrace : WordTrace (prefixWord ++ tailWord_2659189) baseStart_2659189 baseEnd_2659189 := by
    simpa [prefixWord, tailWord_2659189, baseEnd_2659189] using wordTrace_append hprefix tailTrace_2659189
  have hstable : (prefixWord ++ tailWord_2659189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659189).length < 2 ^ (prefixWord ++ tailWord_2659189).sum := by decide
  have hdescent : baseEnd_2659189 < baseStart_2659189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659217 : List Nat := [1, 2, 2, 1, 1, 1, 3, 7, 4]
def baseStart_2659217 : Nat := 118140960795 + 2659217 * 2 ^ 59
def prefixEnd_2659217 : Nat := 4983230072969 + 3 ^ 40 * 2659217 * 2
def baseEnd_2659217 : Nat := 303434774579383896657331

theorem tailTrace_2659217 : CollatzResearch.WordTrace tailWord_2659217 prefixEnd_2659217 303434774579383896657331 := by
  unfold tailWord_2659217
  simp only [CollatzResearch.WordTrace]
  refine ⟨96989612007118441951335905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64659741338078961300890603 96989612007118441951335905)
  ·
    refine ⟨72742209005338831463501929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96989612007118441951335905 72742209005338831463501929)
    ·
      refine ⟨54556656754004123597626447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72742209005338831463501929 54556656754004123597626447)
      ·
        refine ⟨81834985131006185396439671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54556656754004123597626447 81834985131006185396439671)
        ·
          refine ⟨122752477696509278094659507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81834985131006185396439671 122752477696509278094659507)
          ·
            refine ⟨184128716544763917141989261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122752477696509278094659507 184128716544763917141989261)
            ·
              refine ⟨69048268704286468928245973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184128716544763917141989261 69048268704286468928245973)
              ·
                refine ⟨1618318797756714115505765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 69048268704286468928245973 1618318797756714115505765)
                ·
                  refine ⟨303434774579383896657331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1618318797756714115505765 303434774579383896657331)
                  ·
                    rfl

theorem cell22_2659217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 4].length) (baseStart_2659217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659217 prefixEnd_2659217 := by exact prefixLift 2659217
  have htrace : WordTrace (prefixWord ++ tailWord_2659217) baseStart_2659217 baseEnd_2659217 := by
    simpa [prefixWord, tailWord_2659217, baseEnd_2659217] using wordTrace_append hprefix tailTrace_2659217
  have hstable : (prefixWord ++ tailWord_2659217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659217).length < 2 ^ (prefixWord ++ tailWord_2659217).sum := by decide
  have hdescent : baseEnd_2659217 < baseStart_2659217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659232 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 4, 3]
def baseStart_2659232 : Nat := 118140960795 + 2659232 * 2 ^ 59
def prefixEnd_2659232 : Nat := 4983230072969 + 3 ^ 40 * 2659232 * 2
def baseEnd_2659232 : Nat := 910309458544696650846947

theorem tailTrace_2659232 : CollatzResearch.WordTrace tailWord_2659232 prefixEnd_2659232 910309458544696650846947 := by
  unfold tailWord_2659232
  simp only [CollatzResearch.WordTrace]
  refine ⟨48495079551032049756565975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64660106068042733008754633 48495079551032049756565975)
  ·
    refine ⟨72742619326548074634848963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48495079551032049756565975 72742619326548074634848963)
    ·
      refine ⟨109113928989822111952273445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72742619326548074634848963 109113928989822111952273445)
      ·
        refine ⟨20458861685591645991051271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109113928989822111952273445 20458861685591645991051271)
        ·
          refine ⟨30688292528387468986576907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20458861685591645991051271 30688292528387468986576907)
          ·
            refine ⟨46032438792581203479865361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30688292528387468986576907 46032438792581203479865361)
            ·
              refine ⟨34524329094435902609899021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46032438792581203479865361 34524329094435902609899021)
              ·
                refine ⟨12946623410413463478712133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34524329094435902609899021 12946623410413463478712133)
                ·
                  refine ⟨2427491889452524402258525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12946623410413463478712133 2427491889452524402258525)
                  ·
                    refine ⟨910309458544696650846947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2427491889452524402258525 910309458544696650846947)
                    ·
                      rfl

theorem cell22_2659232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 4, 3].length) (baseStart_2659232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659232 prefixEnd_2659232 := by exact prefixLift 2659232
  have htrace : WordTrace (prefixWord ++ tailWord_2659232) baseStart_2659232 baseEnd_2659232 := by
    simpa [prefixWord, tailWord_2659232, baseEnd_2659232] using wordTrace_append hprefix tailTrace_2659232
  have hstable : (prefixWord ++ tailWord_2659232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659232).length < 2 ^ (prefixWord ++ tailWord_2659232).sum := by decide
  have hdescent : baseEnd_2659232 < baseStart_2659232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659249 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 1, 5]
def baseStart_2659249 : Nat := 118140960795 + 2659249 * 2 ^ 59
def prefixEnd_2659249 : Nat := 4983230072969 + 3 ^ 40 * 2659249 * 2
def baseEnd_2659249 : Nat := 910315277992114273171895

theorem tailTrace_2659249 : CollatzResearch.WordTrace tailWord_2659249 prefixEnd_2659249 910315277992114273171895 := by
  unfold tailWord_2659249
  simp only [CollatzResearch.WordTrace]
  refine ⟨96990779143002511416500801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64660519428668340944333867 96990779143002511416500801)
  ·
    refine ⟨72743084357251883562375601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96990779143002511416500801 72743084357251883562375601)
    ·
      refine ⟨54557313267938912671781701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72743084357251883562375601 54557313267938912671781701)
      ·
        refine ⟨10229496237738546125959069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54557313267938912671781701 10229496237738546125959069)
        ·
          refine ⟨3836061089151954797234651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10229496237738546125959069 3836061089151954797234651)
          ·
            refine ⟨5754091633727932195851977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3836061089151954797234651 5754091633727932195851977)
            ·
              refine ⟨4315568725295949146888983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5754091633727932195851977 4315568725295949146888983)
              ·
                refine ⟨6473353087943923720333475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4315568725295949146888983 6473353087943923720333475)
                ·
                  refine ⟨9710029631915885580500213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6473353087943923720333475 9710029631915885580500213)
                  ·
                    refine ⟨910315277992114273171895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9710029631915885580500213 910315277992114273171895)
                    ·
                      rfl

theorem cell22_2659249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_2659249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659249 prefixEnd_2659249 := by exact prefixLift 2659249
  have htrace : WordTrace (prefixWord ++ tailWord_2659249) baseStart_2659249 baseEnd_2659249 := by
    simpa [prefixWord, tailWord_2659249, baseEnd_2659249] using wordTrace_append hprefix tailTrace_2659249
  have hstable : (prefixWord ++ tailWord_2659249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659249).length < 2 ^ (prefixWord ++ tailWord_2659249).sum := by decide
  have hdescent : baseEnd_2659249 < baseStart_2659249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659264 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 2, 4]
def baseStart_2659264 : Nat := 118140960795 + 2659264 * 2 ^ 59
def prefixEnd_2659264 : Nat := 4983230072969 + 3 ^ 40 * 2659264 * 2
def baseEnd_2659264 : Nat := 910320412798659234046849

theorem tailTrace_2659264 : CollatzResearch.WordTrace tailWord_2659264 prefixEnd_2659264 910320412798659234046849 := by
  unfold tailWord_2659264
  simp only [CollatzResearch.WordTrace]
  refine ⟨48495663118974084489148423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64660884158632112652197897 48495663118974084489148423)
  ·
    refine ⟨72743494678461126733722635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48495663118974084489148423 72743494678461126733722635)
    ·
      refine ⟨109115242017691690100583953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72743494678461126733722635 109115242017691690100583953)
      ·
        refine ⟨81836431513268767575437965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109115242017691690100583953 81836431513268767575437965)
        ·
          refine ⟨30688661817475787840789237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81836431513268767575437965 30688661817475787840789237)
          ·
            refine ⟨2877062045388355110073991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30688661817475787840789237 2877062045388355110073991)
            ·
              refine ⟨4315593068082532665110987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2877062045388355110073991 4315593068082532665110987)
              ·
                refine ⟨6473389602123798997666481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4315593068082532665110987 6473389602123798997666481)
                ·
                  refine ⟨4855042201592849248249861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6473389602123798997666481 4855042201592849248249861)
                  ·
                    refine ⟨910320412798659234046849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4855042201592849248249861 910320412798659234046849)
                    ·
                      rfl

theorem cell22_2659264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 2, 4].length) (baseStart_2659264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659264 prefixEnd_2659264 := by exact prefixLift 2659264
  have htrace : WordTrace (prefixWord ++ tailWord_2659264) baseStart_2659264 baseEnd_2659264 := by
    simpa [prefixWord, tailWord_2659264, baseEnd_2659264] using wordTrace_append hprefix tailTrace_2659264
  have hstable : (prefixWord ++ tailWord_2659264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659264).length < 2 ^ (prefixWord ++ tailWord_2659264).sum := by decide
  have hdescent : baseEnd_2659264 < baseStart_2659264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659268 : List Nat := [2, 3, 3, 3, 1, 1, 2, 3, 4]
def baseStart_2659268 : Nat := 118140960795 + 2659268 * 2 ^ 59
def prefixEnd_2659268 : Nat := 4983230072969 + 3 ^ 40 * 2659268 * 2
def baseEnd_2659268 : Nat := 303440594026801518982279

theorem tailTrace_2659268 : CollatzResearch.WordTrace tailWord_2659268 prefixEnd_2659268 303440594026801518982279 := by
  unfold tailWord_2659268
  simp only [CollatzResearch.WordTrace]
  refine ⟨48495736064966838830721229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64660981419955785107628305 48495736064966838830721229)
  ·
    refine ⟨18185901024362564561520461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48495736064966838830721229 18185901024362564561520461)
    ·
      refine ⟨6819712884135961710570173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18185901024362564561520461 6819712884135961710570173)
      ·
        refine ⟨2557392331550985641463815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6819712884135961710570173 2557392331550985641463815)
        ·
          refine ⟨3836088497326478462195723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2557392331550985641463815 3836088497326478462195723)
          ·
            refine ⟨5754132745989717693293585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3836088497326478462195723 5754132745989717693293585)
            ·
              refine ⟨4315599559492288269970189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5754132745989717693293585 4315599559492288269970189)
              ·
                refine ⟨1618349834809608101238821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4315599559492288269970189 1618349834809608101238821)
                ·
                  refine ⟨303440594026801518982279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1618349834809608101238821 303440594026801518982279)
                  ·
                    rfl

theorem cell22_2659268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_2659268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659268 prefixEnd_2659268 := by exact prefixLift 2659268
  have htrace : WordTrace (prefixWord ++ tailWord_2659268) baseStart_2659268 baseEnd_2659268 := by
    simpa [prefixWord, tailWord_2659268, baseEnd_2659268] using wordTrace_append hprefix tailTrace_2659268
  have hstable : (prefixWord ++ tailWord_2659268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659268).length < 2 ^ (prefixWord ++ tailWord_2659268).sum := by decide
  have hdescent : baseEnd_2659268 < baseStart_2659268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659384 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 1, 5]
def baseStart_2659384 : Nat := 118140960795 + 2659384 * 2 ^ 59
def prefixEnd_2659384 : Nat := 4983230072969 + 3 ^ 40 * 2659384 * 2
def baseEnd_2659384 : Nat := 910361491251018921046481

theorem tailTrace_2659384 : CollatzResearch.WordTrace tailWord_2659384 prefixEnd_2659384 910361491251018921046481 := by
  unfold tailWord_2659384
  simp only [CollatzResearch.WordTrace]
  refine ⟨48497851498756714736332603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64663801998342286315110137 48497851498756714736332603)
  ·
    refine ⟨72746777248135072104498905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48497851498756714736332603 72746777248135072104498905)
    ·
      refine ⟨54560082936101304078374179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72746777248135072104498905 54560082936101304078374179)
      ·
        refine ⟨81840124404151956117561269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54560082936101304078374179 81840124404151956117561269)
        ·
          refine ⟨7672511662889245886021369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81840124404151956117561269 7672511662889245886021369)
          ·
            refine ⟨5754383747166934414516027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7672511662889245886021369 5754383747166934414516027)
            ·
              refine ⟨8631575620750401621774041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5754383747166934414516027 8631575620750401621774041)
              ·
                refine ⟨6473681715562801216330531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8631575620750401621774041 6473681715562801216330531)
                ·
                  refine ⟨9710522573344201824495797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6473681715562801216330531 9710522573344201824495797)
                  ·
                    refine ⟨910361491251018921046481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9710522573344201824495797 910361491251018921046481)
                    ·
                      rfl

theorem cell22_2659384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_2659384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659384 prefixEnd_2659384 := by exact prefixLift 2659384
  have htrace : WordTrace (prefixWord ++ tailWord_2659384) baseStart_2659384 baseEnd_2659384 := by
    simpa [prefixWord, tailWord_2659384, baseEnd_2659384] using wordTrace_append hprefix tailTrace_2659384
  have hstable : (prefixWord ++ tailWord_2659384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659384).length < 2 ^ (prefixWord ++ tailWord_2659384).sum := by decide
  have hdescent : baseEnd_2659384 < baseStart_2659384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659399 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 2, 4]
def baseStart_2659399 : Nat := 118140960795 + 2659399 * 2 ^ 59
def prefixEnd_2659399 : Nat := 4983230072969 + 3 ^ 40 * 2659399 * 2
def baseEnd_2659399 : Nat := 910366626057563881921435

theorem tailTrace_2659399 : CollatzResearch.WordTrace tailWord_2659399 prefixEnd_2659399 910366626057563881921435 := by
  unfold tailWord_2659399
  simp only [CollatzResearch.WordTrace]
  refine ⟨96996250092459087034461251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64664166728306058022974167 96996250092459087034461251)
  ·
    refine ⟨145494375138688630551691877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96996250092459087034461251 145494375138688630551691877)
    ·
      refine ⟨27280195338504118228442227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145494375138688630551691877 27280195338504118228442227)
      ·
        refine ⟨40920293007756177342663341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27280195338504118228442227 40920293007756177342663341)
        ·
          refine ⟨15345109877908566503498753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40920293007756177342663341 15345109877908566503498753)
          ·
            refine ⟨11508832408431424877624065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15345109877908566503498753 11508832408431424877624065)
            ·
              refine ⟨8631624306323568658218049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11508832408431424877624065 8631624306323568658218049)
              ·
                refine ⟨6473718229742676493663537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8631624306323568658218049 6473718229742676493663537)
                ·
                  refine ⟨4855288672307007370247653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6473718229742676493663537 4855288672307007370247653)
                  ·
                    refine ⟨910366626057563881921435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4855288672307007370247653 910366626057563881921435)
                    ·
                      rfl

theorem cell22_2659399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_2659399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659399 prefixEnd_2659399 := by exact prefixLift 2659399
  have htrace : WordTrace (prefixWord ++ tailWord_2659399) baseStart_2659399 baseEnd_2659399 := by
    simpa [prefixWord, tailWord_2659399, baseEnd_2659399] using wordTrace_append hprefix tailTrace_2659399
  have hstable : (prefixWord ++ tailWord_2659399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659399).length < 2 ^ (prefixWord ++ tailWord_2659399).sum := by decide
  have hdescent : baseEnd_2659399 < baseStart_2659399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659427 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 4, 6]
def baseStart_2659427 : Nat := 118140960795 + 2659427 * 2 ^ 59
def prefixEnd_2659427 : Nat := 4983230072969 + 3 ^ 40 * 2659427 * 2
def baseEnd_2659427 : Nat := 910376211029781142221349

theorem tailTrace_2659427 : CollatzResearch.WordTrace tailWord_2659427 prefixEnd_2659427 910376211029781142221349 := by
  unfold tailWord_2659427
  simp only [CollatzResearch.WordTrace]
  refine ⟨96997271336357647816480535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64664847557571765210987023 96997271336357647816480535)
  ·
    refine ⟨145495907004536471724720803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96997271336357647816480535 145495907004536471724720803)
    ·
      refine ⟨218243860506804707587081205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145495907004536471724720803 218243860506804707587081205)
      ·
        refine ⟨20460361922512941336288863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 218243860506804707587081205 20460361922512941336288863)
        ·
          refine ⟨30690542883769412004433295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20460361922512941336288863 30690542883769412004433295)
          ·
            refine ⟨46035814325654118006649943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30690542883769412004433295 46035814325654118006649943)
            ·
              refine ⟨69053721488481177009974915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46035814325654118006649943 69053721488481177009974915)
              ·
                refine ⟨103580582232721765514962373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69053721488481177009974915 103580582232721765514962373)
                ·
                  refine ⟨19421359168635331034055445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103580582232721765514962373 19421359168635331034055445)
                  ·
                    refine ⟨910376211029781142221349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19421359168635331034055445 910376211029781142221349)
                    ·
                      rfl

theorem cell22_2659427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 6].length) (baseStart_2659427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659427 prefixEnd_2659427 := by exact prefixLift 2659427
  have htrace : WordTrace (prefixWord ++ tailWord_2659427) baseStart_2659427 baseEnd_2659427 := by
    simpa [prefixWord, tailWord_2659427, baseEnd_2659427] using wordTrace_append hprefix tailTrace_2659427
  have hstable : (prefixWord ++ tailWord_2659427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659427).length < 2 ^ (prefixWord ++ tailWord_2659427).sum := by decide
  have hdescent : baseEnd_2659427 < baseStart_2659427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659446 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_2659446 : Nat := 118140960795 + 2659446 * 2 ^ 59
def prefixEnd_2659446 : Nat := 4983230072969 + 3 ^ 40 * 2659446 * 2
def baseEnd_2659446 : Nat := 910382715118071425996291

theorem tailTrace_2659446 : CollatzResearch.WordTrace tailWord_2659446 prefixEnd_2659446 910382715118071425996291 := by
  unfold tailWord_2659446
  simp only [CollatzResearch.WordTrace]
  refine ⟨6062372770205550878838887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64665309548859209374281461 6062372770205550878838887)
  ·
    refine ⟨9093559155308326318258331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6062372770205550878838887 9093559155308326318258331)
    ·
      refine ⟨13640338732962489477387497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9093559155308326318258331 13640338732962489477387497)
      ·
        refine ⟨10230254049721867108040623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13640338732962489477387497 10230254049721867108040623)
        ·
          refine ⟨15345381074582800662060935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10230254049721867108040623 15345381074582800662060935)
          ·
            refine ⟨23018071611874200993091403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15345381074582800662060935 23018071611874200993091403)
            ·
              refine ⟨34527107417811301489637105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23018071611874200993091403 34527107417811301489637105)
              ·
                refine ⟨25895330563358476117227829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34527107417811301489637105 25895330563358476117227829)
                ·
                  refine ⟨2427687240314857135990109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25895330563358476117227829 2427687240314857135990109)
                  ·
                    refine ⟨910382715118071425996291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2427687240314857135990109 910382715118071425996291)
                    ·
                      rfl

theorem cell22_2659446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_2659446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659446 prefixEnd_2659446 := by exact prefixLift 2659446
  have htrace : WordTrace (prefixWord ++ tailWord_2659446) baseStart_2659446 baseEnd_2659446 := by
    simpa [prefixWord, tailWord_2659446, baseEnd_2659446] using wordTrace_append hprefix tailTrace_2659446
  have hstable : (prefixWord ++ tailWord_2659446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659446).length < 2 ^ (prefixWord ++ tailWord_2659446).sum := by decide
  have hdescent : baseEnd_2659446 < baseStart_2659446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659472 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 2, 8]
def baseStart_2659472 : Nat := 118140960795 + 2659472 * 2 ^ 59
def prefixEnd_2659472 : Nat := 4983230072969 + 3 ^ 40 * 2659472 * 2
def baseEnd_2659472 : Nat := 910391615449416024846211

theorem tailTrace_2659472 : CollatzResearch.WordTrace tailWord_2659472 prefixEnd_2659472 910391615449416024846211 := by
  unfold tailWord_2659472
  simp only [CollatzResearch.WordTrace]
  refine ⟨48499456310597310250934335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64665941747463080334579113 48499456310597310250934335)
  ·
    refine ⟨72749184465895965376401503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48499456310597310250934335 72749184465895965376401503)
    ·
      refine ⟨109123776698843948064602255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72749184465895965376401503 109123776698843948064602255)
      ·
        refine ⟨163685665048265922096903383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109123776698843948064602255 163685665048265922096903383)
        ·
          refine ⟨245528497572398883145355075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163685665048265922096903383 245528497572398883145355075)
          ·
            refine ⟨368292746358598324718032613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245528497572398883145355075 368292746358598324718032613)
            ·
              refine ⟨69054889942237185884631115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 368292746358598324718032613 69054889942237185884631115)
              ·
                refine ⟨103582334913355778826946673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69054889942237185884631115 103582334913355778826946673)
                ·
                  refine ⟨77686751185016834120210005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103582334913355778826946673 77686751185016834120210005)
                  ·
                    refine ⟨910391615449416024846211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77686751185016834120210005 910391615449416024846211)
                    ·
                      rfl

theorem cell22_2659472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_2659472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659472 prefixEnd_2659472 := by exact prefixLift 2659472
  have htrace : WordTrace (prefixWord ++ tailWord_2659472) baseStart_2659472 baseEnd_2659472 := by
    simpa [prefixWord, tailWord_2659472, baseEnd_2659472] using wordTrace_append hprefix tailTrace_2659472
  have hstable : (prefixWord ++ tailWord_2659472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659472).length < 2 ^ (prefixWord ++ tailWord_2659472).sum := by decide
  have hdescent : baseEnd_2659472 < baseStart_2659472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659506 : List Nat := [3, 2, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_2659506 : Nat := 118140960795 + 2659506 * 2 ^ 59
def prefixEnd_2659506 : Nat := 4983230072969 + 3 ^ 40 * 2659506 * 2
def baseEnd_2659506 : Nat := 910403254344251269496107

theorem tailTrace_2659506 : CollatzResearch.WordTrace tailWord_2659506 prefixEnd_2659506 910403254344251269496107 := by
  unfold tailWord_2659506
  simp only [CollatzResearch.WordTrace]
  refine ⟨24250038175767861077151593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64666768468714296205737581 24250038175767861077151593)
  ·
    refine ⟨18187528631825895807863695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24250038175767861077151593 18187528631825895807863695)
    ·
      refine ⟨27281292947738843711795543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18187528631825895807863695 27281292947738843711795543)
      ·
        refine ⟨40921939421608265567693315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27281292947738843711795543 40921939421608265567693315)
        ·
          refine ⟨61382909132412398351539973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40921939421608265567693315 61382909132412398351539973)
          ·
            refine ⟨11509295462327324690913745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61382909132412398351539973 11509295462327324690913745)
            ·
              refine ⟨8631971596745493518185309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11509295462327324690913745 8631971596745493518185309)
              ·
                refine ⟨3236989348779560069319491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8631971596745493518185309 3236989348779560069319491)
                ·
                  refine ⟨4855484023169340103979237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3236989348779560069319491 4855484023169340103979237)
                  ·
                    refine ⟨910403254344251269496107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4855484023169340103979237 910403254344251269496107)
                    ·
                      rfl

theorem cell22_2659506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_2659506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659506 prefixEnd_2659506 := by exact prefixLift 2659506
  have htrace : WordTrace (prefixWord ++ tailWord_2659506) baseStart_2659506 baseEnd_2659506 := by
    simpa [prefixWord, tailWord_2659506, baseEnd_2659506] using wordTrace_append hprefix tailTrace_2659506
  have hstable : (prefixWord ++ tailWord_2659506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659506).length < 2 ^ (prefixWord ++ tailWord_2659506).sum := by decide
  have hdescent : baseEnd_2659506 < baseStart_2659506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659570 : List Nat := [3, 2, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_2659570 : Nat := 118140960795 + 2659570 * 2 ^ 59
def prefixEnd_2659570 : Nat := 4983230072969 + 3 ^ 40 * 2659570 * 2
def baseEnd_2659570 : Nat := 910425162852176435895911

theorem tailTrace_2659570 : CollatzResearch.WordTrace tailWord_2659570 prefixEnd_2659570 910425162852176435895911 := by
  unfold tailWord_2659570
  simp only [CollatzResearch.WordTrace]
  refine ⟨24250621743709895809734041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64668324649893055492624109 24250621743709895809734041)
  ·
    refine ⟨18187966307782421857300531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24250621743709895809734041 18187966307782421857300531)
    ·
      refine ⟨27281949461673632785950797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18187966307782421857300531 27281949461673632785950797)
      ·
        refine ⟨10230731048127612294731549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27281949461673632785950797 10230731048127612294731549)
        ·
          refine ⟨3836524143047854610524331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10230731048127612294731549 3836524143047854610524331)
          ·
            refine ⟨5754786214571781915786497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3836524143047854610524331 5754786214571781915786497)
            ·
              refine ⟨4316089660928836436839873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5754786214571781915786497 4316089660928836436839873)
              ·
                refine ⟨3237067245696627327629905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4316089660928836436839873 3237067245696627327629905)
                ·
                  refine ⟨2427800434272470495722429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3237067245696627327629905 2427800434272470495722429)
                  ·
                    refine ⟨910425162852176435895911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2427800434272470495722429 910425162852176435895911)
                    ·
                      rfl

theorem cell22_2659570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_2659570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659570 prefixEnd_2659570 := by exact prefixLift 2659570
  have htrace : WordTrace (prefixWord ++ tailWord_2659570) baseStart_2659570 baseEnd_2659570 := by
    simpa [prefixWord, tailWord_2659570, baseEnd_2659570] using wordTrace_append hprefix tailTrace_2659570
  have hstable : (prefixWord ++ tailWord_2659570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659570).length < 2 ^ (prefixWord ++ tailWord_2659570).sum := by decide
  have hdescent : baseEnd_2659570 < baseStart_2659570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659594 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 9]
def baseStart_2659594 : Nat := 118140960795 + 2659594 * 2 ^ 59
def prefixEnd_2659594 : Nat := 4983230072969 + 3 ^ 40 * 2659594 * 2
def baseEnd_2659594 : Nat := 303477792847549457765279

theorem tailTrace_2659594 : CollatzResearch.WordTrace tailWord_2659594 prefixEnd_2659594 303477792847549457765279 := by
  unfold tailWord_2659594
  simp only [CollatzResearch.WordTrace]
  refine ⟨24250840581688158834452459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64668908217835090225206557 24250840581688158834452459)
  ·
    refine ⟨36376260872532238251678689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24250840581688158834452459 36376260872532238251678689)
    ·
      refine ⟨27282195654399178688759017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36376260872532238251678689 27282195654399178688759017)
      ·
        refine ⟨20461646740799384016569263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27282195654399178688759017 20461646740799384016569263)
        ·
          refine ⟨30692470111199076024853895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20461646740799384016569263 30692470111199076024853895)
          ·
            refine ⟨46038705166798614037280843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30692470111199076024853895 46038705166798614037280843)
            ·
              refine ⟨69058057750197921055921265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46038705166798614037280843 69058057750197921055921265)
              ·
                refine ⟨51793543312648440791940949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69058057750197921055921265 51793543312648440791940949)
                ·
                  refine ⟨303477792847549457765279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51793543312648440791940949 303477792847549457765279)
                  ·
                    rfl

theorem cell22_2659594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_2659594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659594 prefixEnd_2659594 := by exact prefixLift 2659594
  have htrace : WordTrace (prefixWord ++ tailWord_2659594) baseStart_2659594 baseEnd_2659594 := by
    simpa [prefixWord, tailWord_2659594, baseEnd_2659594] using wordTrace_append hprefix tailTrace_2659594
  have hstable : (prefixWord ++ tailWord_2659594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659594).length < 2 ^ (prefixWord ++ tailWord_2659594).sum := by decide
  have hdescent : baseEnd_2659594 < baseStart_2659594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659598 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_2659598 : Nat := 118140960795 + 2659598 * 2 ^ 59
def prefixEnd_2659598 : Nat := 4983230072969 + 3 ^ 40 * 2659598 * 2
def baseEnd_2659598 : Nat := 910434747824393696195825

theorem tailTrace_2659598 : CollatzResearch.WordTrace tailWord_2659598 prefixEnd_2659598 910434747824393696195825 := by
  unfold tailWord_2659598
  simp only [CollatzResearch.WordTrace]
  refine ⟨12125438527342268002619431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64669005479158762680636965 12125438527342268002619431)
  ·
    refine ⟨18188157791013402003929147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12125438527342268002619431 18188157791013402003929147)
    ·
      refine ⟨27282236686520103005893721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18188157791013402003929147 27282236686520103005893721)
      ·
        refine ⟨20461677514890077254420291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27282236686520103005893721 20461677514890077254420291)
        ·
          refine ⟨30692516272335115881630437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20461677514890077254420291 30692516272335115881630437)
          ·
            refine ⟨5754846801062834227805707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30692516272335115881630437 5754846801062834227805707)
            ·
              refine ⟨8632270201594251341708561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5754846801062834227805707 8632270201594251341708561)
              ·
                refine ⟨6474202651195688506281421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8632270201594251341708561 6474202651195688506281421)
                ·
                  refine ⟨2427825994198383189855533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6474202651195688506281421 2427825994198383189855533)
                  ·
                    refine ⟨910434747824393696195825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2427825994198383189855533 910434747824393696195825)
                    ·
                      rfl

theorem cell22_2659598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_2659598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659598 prefixEnd_2659598 := by exact prefixLift 2659598
  have htrace : WordTrace (prefixWord ++ tailWord_2659598) baseStart_2659598 baseEnd_2659598 := by
    simpa [prefixWord, tailWord_2659598, baseEnd_2659598] using wordTrace_append hprefix tailTrace_2659598
  have hstable : (prefixWord ++ tailWord_2659598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659598).length < 2 ^ (prefixWord ++ tailWord_2659598).sum := by decide
  have hdescent : baseEnd_2659598 < baseStart_2659598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659602 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2659602 : Nat := 118140960795 + 2659602 * 2 ^ 59
def prefixEnd_2659602 : Nat := 4983230072969 + 3 ^ 40 * 2659602 * 2
def baseEnd_2659602 : Nat := 910436117106139019095813

theorem tailTrace_2659602 : CollatzResearch.WordTrace tailWord_2659602 prefixEnd_2659602 910436117106139019095813 := by
  unfold tailWord_2659602
  simp only [CollatzResearch.WordTrace]
  refine ⟨24250913527680913176025265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64669102740482435136067373 24250913527680913176025265)
  ·
    refine ⟨18188185145760684882018949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24250913527680913176025265 18188185145760684882018949)
    ·
      refine ⟨3410284714830128415378553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18188185145760684882018949 3410284714830128415378553)
      ·
        refine ⟨2557713536122596311533915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3410284714830128415378553 2557713536122596311533915)
        ·
          refine ⟨3836570304183894467300873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2557713536122596311533915 3836570304183894467300873)
          ·
            refine ⟨2877427728137920850475655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3836570304183894467300873 2877427728137920850475655)
            ·
              refine ⟨4316141592206881275713483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2877427728137920850475655 4316141592206881275713483)
              ·
                refine ⟨6474212388310321913570225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4316141592206881275713483 6474212388310321913570225)
                ·
                  refine ⟨4855659291232741435177669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6474212388310321913570225 4855659291232741435177669)
                  ·
                    refine ⟨910436117106139019095813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4855659291232741435177669 910436117106139019095813)
                    ·
                      rfl

theorem cell22_2659602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2659602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659602 prefixEnd_2659602 := by exact prefixLift 2659602
  have htrace : WordTrace (prefixWord ++ tailWord_2659602) baseStart_2659602 baseEnd_2659602 := by
    simpa [prefixWord, tailWord_2659602, baseEnd_2659602] using wordTrace_append hprefix tailTrace_2659602
  have hstable : (prefixWord ++ tailWord_2659602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659602).length < 2 ^ (prefixWord ++ tailWord_2659602).sum := by decide
  have hdescent : baseEnd_2659602 < baseStart_2659602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659673 : List Nat := [1, 2, 1, 2, 2, 2, 5, 3, 4]
def baseStart_2659673 : Nat := 118140960795 + 2659673 * 2 ^ 59
def prefixEnd_2659673 : Nat := 4983230072969 + 3 ^ 40 * 2659673 * 2
def baseEnd_2659673 : Nat := 303486807285706166856865

theorem tailTrace_2659673 : CollatzResearch.WordTrace tailWord_2659673 prefixEnd_2659673 303486807285706166856865 := by
  unfold tailWord_2659673
  simp only [CollatzResearch.WordTrace]
  refine ⟨97006243693466431829935673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64670829128977621219957115 97006243693466431829935673)
  ·
    refine ⟨72754682770099823872451755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97006243693466431829935673 72754682770099823872451755)
    ·
      refine ⟨109132024155149735808677633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72754682770099823872451755 109132024155149735808677633)
      ·
        refine ⟨81849018116362301856508225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109132024155149735808677633 81849018116362301856508225)
        ·
          refine ⟨61386763587271726392381169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81849018116362301856508225 61386763587271726392381169)
          ·
            refine ⟨46040072690453794794285877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61386763587271726392381169 46040072690453794794285877)
            ·
              refine ⟨4316256814730043261964301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46040072690453794794285877 4316256814730043261964301)
              ·
                refine ⟨1618596305523766223236613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4316256814730043261964301 1618596305523766223236613)
                ·
                  refine ⟨303486807285706166856865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1618596305523766223236613 303486807285706166856865)
                  ·
                    rfl

theorem cell22_2659673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 4].length) (baseStart_2659673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659673 prefixEnd_2659673 := by exact prefixLift 2659673
  have htrace : WordTrace (prefixWord ++ tailWord_2659673) baseStart_2659673 baseEnd_2659673 := by
    simpa [prefixWord, tailWord_2659673, baseEnd_2659673] using wordTrace_append hprefix tailTrace_2659673
  have hstable : (prefixWord ++ tailWord_2659673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659673).length < 2 ^ (prefixWord ++ tailWord_2659673).sum := by decide
  have hdescent : baseEnd_2659673 < baseStart_2659673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659690 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 6]
def baseStart_2659690 : Nat := 118140960795 + 2659690 * 2 ^ 59
def prefixEnd_2659690 : Nat := 4983230072969 + 3 ^ 40 * 2659690 * 2
def baseEnd_2659690 : Nat := 303488747101512040965181

theorem tailTrace_2659690 : CollatzResearch.WordTrace tailWord_2659690 prefixEnd_2659690 303488747101512040965181 := by
  unfold tailWord_2659690
  simp only [CollatzResearch.WordTrace]
  refine ⟨24251715933601210933326131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64671242489603229155536349 24251715933601210933326131)
  ·
    refine ⟨36377573900401816399989197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24251715933601210933326131 36377573900401816399989197)
    ·
      refine ⟨13641590212650681149995949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36377573900401816399989197 13641590212650681149995949)
      ·
        refine ⟨5115596329744005431248481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13641590212650681149995949 5115596329744005431248481)
        ·
          refine ⟨3836697247308004073436361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5115596329744005431248481 3836697247308004073436361)
          ·
            refine ⟨2877522935481003055077271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3836697247308004073436361 2877522935481003055077271)
            ·
              refine ⟨4316284403221504582615907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2877522935481003055077271 4316284403221504582615907)
              ·
                refine ⟨6474426604832256873923861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4316284403221504582615907 6474426604832256873923861)
                ·
                  refine ⟨303488747101512040965181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6474426604832256873923861 303488747101512040965181)
                  ·
                    rfl

theorem cell22_2659690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_2659690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659690 prefixEnd_2659690 := by exact prefixLift 2659690
  have htrace : WordTrace (prefixWord ++ tailWord_2659690) baseStart_2659690 baseEnd_2659690 := by
    simpa [prefixWord, tailWord_2659690, baseEnd_2659690] using wordTrace_append hprefix tailTrace_2659690
  have hstable : (prefixWord ++ tailWord_2659690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659690).length < 2 ^ (prefixWord ++ tailWord_2659690).sum := by decide
  have hdescent : baseEnd_2659690 < baseStart_2659690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659705 : List Nat := [1, 2, 1, 3, 2, 1, 6, 1, 2, 3]
def baseStart_2659705 : Nat := 118140960795 + 2659705 * 2 ^ 59
def prefixEnd_2659705 : Nat := 4983230072969 + 3 ^ 40 * 2659705 * 2
def baseEnd_2659705 : Nat := 910471376111081083770497

theorem tailTrace_2659705 : CollatzResearch.WordTrace tailWord_2659705 prefixEnd_2659705 910471376111081083770497 := by
  unfold tailWord_2659705
  simp only [CollatzResearch.WordTrace]
  refine ⟨97007410829350501295100569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64671607219567000863400379 97007410829350501295100569)
  ·
    refine ⟨72755558122012875971325427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97007410829350501295100569 72755558122012875971325427)
    ·
      refine ⟨109133337183019313956988141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72755558122012875971325427 109133337183019313956988141)
      ·
        refine ⟨40925001443632242733870553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109133337183019313956988141 40925001443632242733870553)
        ·
          refine ⟨30693751082724182050402915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40925001443632242733870553 30693751082724182050402915)
          ·
            refine ⟨46040626624086273075604373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30693751082724182050402915 46040626624086273075604373)
            ·
              refine ⟨2158154373004044050418955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46040626624086273075604373 2158154373004044050418955)
              ·
                refine ⟨3237231559506066075628433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158154373004044050418955 3237231559506066075628433)
                ·
                  refine ⟨2427923669629549556721325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3237231559506066075628433 2427923669629549556721325)
                  ·
                    refine ⟨910471376111081083770497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2427923669629549556721325 910471376111081083770497)
                    ·
                      rfl

theorem cell22_2659705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 2, 3].length) (baseStart_2659705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659705 prefixEnd_2659705 := by exact prefixLift 2659705
  have htrace : WordTrace (prefixWord ++ tailWord_2659705) baseStart_2659705 baseEnd_2659705 := by
    simpa [prefixWord, tailWord_2659705, baseEnd_2659705] using wordTrace_append hprefix tailTrace_2659705
  have hstable : (prefixWord ++ tailWord_2659705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659705).length < 2 ^ (prefixWord ++ tailWord_2659705).sum := by decide
  have hdescent : baseEnd_2659705 < baseStart_2659705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659752 : List Nat := [2, 1, 6, 1, 3, 1, 1, 7]
def baseStart_2659752 : Nat := 118140960795 + 2659752 * 2 ^ 59
def prefixEnd_2659752 : Nat := 4983230072969 + 3 ^ 40 * 2659752 * 2
def baseEnd_2659752 : Nat := 101165273907954291982817

theorem tailTrace_2659752 : CollatzResearch.WordTrace tailWord_2659752 prefixEnd_2659752 101165273907954291982817 := by
  unfold tailWord_2659752
  simp only [CollatzResearch.WordTrace]
  refine ⟨48504562530090114161030755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64672750040120152214707673 48504562530090114161030755)
  ·
    refine ⟨72756843795135171241546133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48504562530090114161030755 72756843795135171241546133)
    ·
      refine ⟨3410477052896961151947475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72756843795135171241546133 3410477052896961151947475)
      ·
        refine ⟨5115715579345441727921213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3410477052896961151947475 5115715579345441727921213)
        ·
          refine ⟨1918393342254540647970455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5115715579345441727921213 1918393342254540647970455)
          ·
            refine ⟨2877590013381810971955683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918393342254540647970455 2877590013381810971955683)
            ·
              refine ⟨4316385020072716457933525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2877590013381810971955683 4316385020072716457933525)
              ·
                refine ⟨101165273907954291982817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4316385020072716457933525 101165273907954291982817)
                ·
                  rfl

theorem cell22_2659752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 7].length) (baseStart_2659752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659752 prefixEnd_2659752 := by exact prefixLift 2659752
  have htrace : WordTrace (prefixWord ++ tailWord_2659752) baseStart_2659752 baseEnd_2659752 := by
    simpa [prefixWord, tailWord_2659752, baseEnd_2659752] using wordTrace_append hprefix tailTrace_2659752
  have hstable : (prefixWord ++ tailWord_2659752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659752).length < 2 ^ (prefixWord ++ tailWord_2659752).sum := by decide
  have hdescent : baseEnd_2659752 < baseStart_2659752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659823 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 1, 5]
def baseStart_2659823 : Nat := 118140960795 + 2659823 * 2 ^ 59
def prefixEnd_2659823 : Nat := 4983230072969 + 3 ^ 40 * 2659823 * 2
def baseEnd_2659823 : Nat := 910511769922568109320135

theorem tailTrace_2659823 : CollatzResearch.WordTrace tailWord_2659823 prefixEnd_2659823 910511769922568109320135 := by
  unfold tailWord_2659823
  simp only [CollatzResearch.WordTrace]
  refine ⟨97011714642923007447896123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64674476428615338298597415 97011714642923007447896123)
  ·
    refine ⟨145517571964384511171844185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97011714642923007447896123 145517571964384511171844185)
    ·
      refine ⟨109138178973288383378883139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145517571964384511171844185 109138178973288383378883139)
      ·
        refine ⟨163707268459932575068324709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109138178973288383378883139 163707268459932575068324709)
        ·
          refine ⟨30695112836237357825310883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163707268459932575068324709 30695112836237357825310883)
          ·
            refine ⟨46042669254356036737966325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30695112836237357825310883 46042669254356036737966325)
            ·
              refine ⟨4316500242595878444184343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46042669254356036737966325 4316500242595878444184343)
              ·
                refine ⟨6474750363893817666276515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4316500242595878444184343 6474750363893817666276515)
                ·
                  refine ⟨9712125545840726499414773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6474750363893817666276515 9712125545840726499414773)
                  ·
                    refine ⟨910511769922568109320135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9712125545840726499414773 910511769922568109320135)
                    ·
                      rfl

theorem cell22_2659823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_2659823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659823 prefixEnd_2659823 := by exact prefixLift 2659823
  have htrace : WordTrace (prefixWord ++ tailWord_2659823) baseStart_2659823 baseEnd_2659823 := by
    simpa [prefixWord, tailWord_2659823, baseEnd_2659823] using wordTrace_append hprefix tailTrace_2659823
  have hstable : (prefixWord ++ tailWord_2659823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659823).length < 2 ^ (prefixWord ++ tailWord_2659823).sum := by decide
  have hdescent : baseEnd_2659823 < baseStart_2659823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659943 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 8]
def baseStart_2659943 : Nat := 118140960795 + 2659943 * 2 ^ 59
def prefixEnd_2659943 : Nat := 4983230072969 + 3 ^ 40 * 2659943 * 2
def baseEnd_2659943 : Nat := 303517616124975932106589

theorem tailTrace_2659943 : CollatzResearch.WordTrace tailWord_2659943 prefixEnd_2659943 303517616124975932106589 := by
  unfold tailWord_2659943
  simp only [CollatzResearch.WordTrace]
  refine ⟨97016091402488267942264483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64677394268325511961509655 97016091402488267942264483)
  ·
    refine ⟨145524137103732401913396725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97016091402488267942264483 145524137103732401913396725)
    ·
      refine ⟨13642887853474912679380943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145524137103732401913396725 13642887853474912679380943)
      ·
        refine ⟨20464331780212369019071415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13642887853474912679380943 20464331780212369019071415)
        ·
          refine ⟨30696497670318553528607123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20464331780212369019071415 30696497670318553528607123)
          ·
            refine ⟨46044746505477830292910685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30696497670318553528607123 46044746505477830292910685)
            ·
              refine ⟨17266779939554186359841507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46044746505477830292910685 17266779939554186359841507)
              ·
                refine ⟨25900169909331279539762261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17266779939554186359841507 25900169909331279539762261)
                ·
                  refine ⟨303517616124975932106589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25900169909331279539762261 303517616124975932106589)
                  ·
                    rfl

theorem cell22_2659943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 8].length) (baseStart_2659943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659943 prefixEnd_2659943 := by exact prefixLift 2659943
  have htrace : WordTrace (prefixWord ++ tailWord_2659943) baseStart_2659943 baseEnd_2659943 := by
    simpa [prefixWord, tailWord_2659943, baseEnd_2659943] using wordTrace_append hprefix tailTrace_2659943
  have hstable : (prefixWord ++ tailWord_2659943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659943).length < 2 ^ (prefixWord ++ tailWord_2659943).sum := by decide
  have hdescent : baseEnd_2659943 < baseStart_2659943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659992 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 1, 5]
def baseStart_2659992 : Nat := 118140960795 + 2659992 * 2 ^ 59
def prefixEnd_2659992 : Nat := 4983230072969 + 3 ^ 40 * 2659992 * 2
def baseEnd_2659992 : Nat := 910569622076308001844617

theorem tailTrace_2659992 : CollatzResearch.WordTrace tailWord_2659992 prefixEnd_2659992 910569622076308001844617 := by
  unfold tailWord_2659992
  simp only [CollatzResearch.WordTrace]
  refine ⟨48508939289655374655399115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64678585719540499540532153 48508939289655374655399115)
  ·
    refine ⟨72763408934483061983098673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48508939289655374655399115 72763408934483061983098673)
    ·
      refine ⟨54572556700862296487324005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72763408934483061983098673 54572556700862296487324005)
      ·
        refine ⟨10232354381411680591373251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54572556700862296487324005 10232354381411680591373251)
        ·
          refine ⟨15348531572117520887059877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10232354381411680591373251 15348531572117520887059877)
          ·
            refine ⟨2877849669772035166323727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15348531572117520887059877 2877849669772035166323727)
            ·
              refine ⟨4316774504658052749485591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2877849669772035166323727 4316774504658052749485591)
              ·
                refine ⟨6475161756987079124228387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4316774504658052749485591 6475161756987079124228387)
                ·
                  refine ⟨9712742635480618686342581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6475161756987079124228387 9712742635480618686342581)
                  ·
                    refine ⟨910569622076308001844617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9712742635480618686342581 910569622076308001844617)
                    ·
                      rfl

theorem cell22_2659992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_2659992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2659992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2659992 prefixEnd_2659992 := by exact prefixLift 2659992
  have htrace : WordTrace (prefixWord ++ tailWord_2659992) baseStart_2659992 baseEnd_2659992 := by
    simpa [prefixWord, tailWord_2659992, baseEnd_2659992] using wordTrace_append hprefix tailTrace_2659992
  have hstable : (prefixWord ++ tailWord_2659992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659992).length < 2 ^ (prefixWord ++ tailWord_2659992).sum := by decide
  have hdescent : baseEnd_2659992 < baseStart_2659992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660003 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 2, 7]
def baseStart_2660003 : Nat := 118140960795 + 2660003 * 2 ^ 59
def prefixEnd_2660003 : Nat := 4983230072969 + 3 ^ 40 * 2660003 * 2
def baseEnd_2660003 : Nat := 910573387601107639819583

theorem tailTrace_2660003 : CollatzResearch.WordTrace tailWord_2660003 prefixEnd_2660003 910573387601107639819583 := by
  unfold tailWord_2660003
  simp only [CollatzResearch.WordTrace]
  refine ⟨97018279782270898189448663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64678853188180598792965775 97018279782270898189448663)
  ·
    refine ⟨145527419673406347284172995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97018279782270898189448663 145527419673406347284172995)
    ·
      refine ⟨218291129510109520926259493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145527419673406347284172995 218291129510109520926259493)
      ·
        refine ⟨40929586783145535173673655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218291129510109520926259493 40929586783145535173673655)
        ·
          refine ⟨61394380174718302760510483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40929586783145535173673655 61394380174718302760510483)
          ·
            refine ⟨92091570262077454140765725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61394380174718302760510483 92091570262077454140765725)
            ·
              refine ⟨34534338848279045302787147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92091570262077454140765725 34534338848279045302787147)
              ·
                refine ⟨51801508272418567954180721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34534338848279045302787147 51801508272418567954180721)
                ·
                  refine ⟨38851131204313925965635541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51801508272418567954180721 38851131204313925965635541)
                  ·
                    refine ⟨910573387601107639819583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38851131204313925965635541 910573387601107639819583)
                    ·
                      rfl

theorem cell22_2660003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_2660003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660003 prefixEnd_2660003 := by exact prefixLift 2660003
  have htrace : WordTrace (prefixWord ++ tailWord_2660003) baseStart_2660003 baseEnd_2660003 := by
    simpa [prefixWord, tailWord_2660003, baseEnd_2660003] using wordTrace_append hprefix tailTrace_2660003
  have hstable : (prefixWord ++ tailWord_2660003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660003).length < 2 ^ (prefixWord ++ tailWord_2660003).sum := by decide
  have hdescent : baseEnd_2660003 < baseStart_2660003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660005 : List Nat := [1, 3, 1, 2, 1, 2, 6, 6]
def baseStart_2660005 : Nat := 118140960795 + 2660005 * 2 ^ 59
def prefixEnd_2660005 : Nat := 4983230072969 + 3 ^ 40 * 2660005 * 2
def baseEnd_2660005 : Nat := 101174896915775589029953

theorem tailTrace_2660005 : CollatzResearch.WordTrace tailWord_2660005 prefixEnd_2660005 101174896915775589029953 := by
  unfold tailWord_2660005
  simp only [CollatzResearch.WordTrace]
  refine ⟨97018352728263652531021469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64678901818842435020680979 97018352728263652531021469)
  ·
    refine ⟨36381882273098869699133051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97018352728263652531021469 36381882273098869699133051)
    ·
      refine ⟨54572823409648304548699577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36381882273098869699133051 54572823409648304548699577)
      ·
        refine ⟨40929617557236228411524683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54572823409648304548699577 40929617557236228411524683)
        ·
          refine ⟨61394426335854342617287025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40929617557236228411524683 61394426335854342617287025)
          ·
            refine ⟨46045819751890756962965269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61394426335854342617287025 46045819751890756962965269)
            ·
              refine ⟨2158397800869879232638997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46045819751890756962965269 2158397800869879232638997)
              ·
                refine ⟨101174896915775589029953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2158397800869879232638997 101174896915775589029953)
                ·
                  rfl

theorem cell22_2660005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 6].length) (baseStart_2660005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660005 prefixEnd_2660005 := by exact prefixLift 2660005
  have htrace : WordTrace (prefixWord ++ tailWord_2660005) baseStart_2660005 baseEnd_2660005 := by
    simpa [prefixWord, tailWord_2660005, baseEnd_2660005] using wordTrace_append hprefix tailTrace_2660005
  have hstable : (prefixWord ++ tailWord_2660005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660005).length < 2 ^ (prefixWord ++ tailWord_2660005).sum := by decide
  have hdescent : baseEnd_2660005 < baseStart_2660005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660022 : List Nat := [5, 1, 3, 1, 1, 1, 10]
def baseStart_2660022 : Nat := 118140960795 + 2660022 * 2 ^ 59
def prefixEnd_2660022 : Nat := 4983230072969 + 3 ^ 40 * 2660022 * 2
def baseEnd_2660022 : Nat := 33725181173681404577575

theorem tailTrace_2660022 : CollatzResearch.WordTrace tailWord_2660022 prefixEnd_2660022 33725181173681404577575 := by
  unfold tailWord_2660022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6063685798075129027149395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64679315179468042956260213 6063685798075129027149395)
  ·
    refine ⟨9095528697112693540724093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6063685798075129027149395 9095528697112693540724093)
    ·
      refine ⟨3410823261417260077771535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9095528697112693540724093 3410823261417260077771535)
      ·
        refine ⟨5116234892125890116657303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3410823261417260077771535 5116234892125890116657303)
        ·
          refine ⟨7674352338188835174985955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5116234892125890116657303 7674352338188835174985955)
          ·
            refine ⟨11511528507283252762478933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7674352338188835174985955 11511528507283252762478933)
            ·
              refine ⟨33725181173681404577575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11511528507283252762478933 33725181173681404577575)
              ·
                rfl

theorem cell22_2660022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 10].length) (baseStart_2660022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660022 prefixEnd_2660022 := by exact prefixLift 2660022
  have htrace : WordTrace (prefixWord ++ tailWord_2660022) baseStart_2660022 baseEnd_2660022 := by
    simpa [prefixWord, tailWord_2660022, baseEnd_2660022] using wordTrace_append hprefix tailTrace_2660022
  have hstable : (prefixWord ++ tailWord_2660022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660022).length < 2 ^ (prefixWord ++ tailWord_2660022).sum := by decide
  have hdescent : baseEnd_2660022 < baseStart_2660022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660114 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2660114 : Nat := 118140960795 + 2660114 * 2 ^ 59
def prefixEnd_2660114 : Nat := 4983230072969 + 3 ^ 40 * 2660114 * 2
def baseEnd_2660114 : Nat := 910611385169540350294243

theorem tailTrace_2660114 : CollatzResearch.WordTrace tailWord_2660114 prefixEnd_2660114 910611385169540350294243 := by
  unfold tailWord_2660114
  simp only [CollatzResearch.WordTrace]
  refine ⟨24255582071217191036684849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64681552189912509431159597 24255582071217191036684849)
  ·
    refine ⟨18191686553412893277513637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24255582071217191036684849 18191686553412893277513637)
    ·
      refine ⟨3410941228764917489533807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18191686553412893277513637 3410941228764917489533807)
      ·
        refine ⟨5116411843147376234300711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3410941228764917489533807 5116411843147376234300711)
        ·
          refine ⟨7674617764721064351451067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5116411843147376234300711 7674617764721064351451067)
          ·
            refine ⟨11511926647081596527176601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7674617764721064351451067 11511926647081596527176601)
            ·
              refine ⟨8633944985311197395382451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11511926647081596527176601 8633944985311197395382451)
              ·
                refine ⟨12950917477966796093073677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8633944985311197395382451 12950917477966796093073677)
                ·
                  refine ⟨4856594054237548534902629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12950917477966796093073677 4856594054237548534902629)
                  ·
                    refine ⟨910611385169540350294243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4856594054237548534902629 910611385169540350294243)
                    ·
                      rfl

theorem cell22_2660114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2660114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660114 prefixEnd_2660114 := by exact prefixLift 2660114
  have htrace : WordTrace (prefixWord ++ tailWord_2660114) baseStart_2660114 baseEnd_2660114 := by
    simpa [prefixWord, tailWord_2660114, baseEnd_2660114] using wordTrace_append hprefix tailTrace_2660114
  have hstable : (prefixWord ++ tailWord_2660114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660114).length < 2 ^ (prefixWord ++ tailWord_2660114).sum := by decide
  have hdescent : baseEnd_2660114 < baseStart_2660114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660127 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 4, 3]
def baseStart_2660127 : Nat := 118140960795 + 2660127 * 2 ^ 59
def prefixEnd_2660127 : Nat := 4983230072969 + 3 ^ 40 * 2660127 * 2
def baseEnd_2660127 : Nat := 910615835335212649719203

theorem tailTrace_2660127 : CollatzResearch.WordTrace tailWord_2660127 prefixEnd_2660127 910615835335212649719203 := by
  unfold tailWord_2660127
  simp only [CollatzResearch.WordTrace]
  refine ⟨97022802433821667366962635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64681868289214444911308423 97022802433821667366962635)
  ·
    refine ⟨145534203650732501050443953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97022802433821667366962635 145534203650732501050443953)
    ·
      refine ⟨109150652738049375787832965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145534203650732501050443953 109150652738049375787832965)
      ·
        refine ⟨20465747388384257960218681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109150652738049375787832965 20465747388384257960218681)
        ·
          refine ⟨15349310541288193470164011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20465747388384257960218681 15349310541288193470164011)
          ·
            refine ⟨23023965811932290205246017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15349310541288193470164011 23023965811932290205246017)
            ·
              refine ⟨17267974358949217653934513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23023965811932290205246017 17267974358949217653934513)
              ·
                refine ⟨12950980769211913240450885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17267974358949217653934513 12950980769211913240450885)
                ·
                  refine ⟨2428308894227233732584541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12950980769211913240450885 2428308894227233732584541)
                  ·
                    refine ⟨910615835335212649719203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2428308894227233732584541 910615835335212649719203)
                    ·
                      rfl

theorem cell22_2660127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 3].length) (baseStart_2660127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660127 prefixEnd_2660127 := by exact prefixLift 2660127
  have htrace : WordTrace (prefixWord ++ tailWord_2660127) baseStart_2660127 baseEnd_2660127 := by
    simpa [prefixWord, tailWord_2660127, baseEnd_2660127] using wordTrace_append hprefix tailTrace_2660127
  have hstable : (prefixWord ++ tailWord_2660127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660127).length < 2 ^ (prefixWord ++ tailWord_2660127).sum := by decide
  have hdescent : baseEnd_2660127 < baseStart_2660127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660129 : List Nat := [1, 2, 3, 2, 1, 4, 2, 3, 4]
def baseStart_2660129 : Nat := 118140960795 + 2660129 * 2 ^ 59
def prefixEnd_2660129 : Nat := 4983230072969 + 3 ^ 40 * 2660129 * 2
def baseEnd_2660129 : Nat := 303538839992028437056399

theorem tailTrace_2660129 : CollatzResearch.WordTrace tailWord_2660129 prefixEnd_2660129 303538839992028437056399 := by
  unfold tailWord_2660129
  simp only [CollatzResearch.WordTrace]
  refine ⟨97022875379814421708535441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64681916919876281139023627 97022875379814421708535441)
  ·
    refine ⟨72767156534860816281401581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97022875379814421708535441 72767156534860816281401581)
    ·
      refine ⟨27287683700572806105525593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72767156534860816281401581 27287683700572806105525593)
      ·
        refine ⟨20465762775429604579144195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27287683700572806105525593 20465762775429604579144195)
        ·
          refine ⟨30698644163144406868716293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20465762775429604579144195 30698644163144406868716293)
          ·
            refine ⟨5755995780589576287884305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30698644163144406868716293 5755995780589576287884305)
            ·
              refine ⟨4316996835442182215913229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5755995780589576287884305 4316996835442182215913229)
              ·
                refine ⟨1618873813290818330967461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4316996835442182215913229 1618873813290818330967461)
                ·
                  refine ⟨303538839992028437056399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1618873813290818330967461 303538839992028437056399)
                  ·
                    rfl

theorem cell22_2660129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 4].length) (baseStart_2660129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660129 prefixEnd_2660129 := by exact prefixLift 2660129
  have htrace : WordTrace (prefixWord ++ tailWord_2660129) baseStart_2660129 baseEnd_2660129 := by
    simpa [prefixWord, tailWord_2660129, baseEnd_2660129] using wordTrace_append hprefix tailTrace_2660129
  have hstable : (prefixWord ++ tailWord_2660129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660129).length < 2 ^ (prefixWord ++ tailWord_2660129).sum := by decide
  have hdescent : baseEnd_2660129 < baseStart_2660129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660140 : List Nat := [2, 2, 1, 1, 1, 6, 9]
def baseStart_2660140 : Nat := 118140960795 + 2660140 * 2 ^ 59
def prefixEnd_2660140 : Nat := 4983230072969 + 3 ^ 40 * 2660140 * 2
def baseEnd_2660140 : Nat := 33726677240773516634969

theorem tailTrace_2660140 : CollatzResearch.WordTrace tailWord_2660140 prefixEnd_2660140 33726677240773516634969 := by
  unfold tailWord_2660140
  simp only [CollatzResearch.WordTrace]
  refine ⟨48511638291387285293592937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64682184388516380391457249 48511638291387285293592937)
  ·
    refine ⟨36383728718540463970194703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48511638291387285293592937 36383728718540463970194703)
    ·
      refine ⟨54575593077810695955292055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36383728718540463970194703 54575593077810695955292055)
      ·
        refine ⟨81863389616716043932938083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54575593077810695955292055 81863389616716043932938083)
        ·
          refine ⟨122795084425074065899407125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81863389616716043932938083 122795084425074065899407125)
          ·
            refine ⟨5756019582425346839034709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122795084425074065899407125 5756019582425346839034709)
            ·
              refine ⟨33726677240773516634969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5756019582425346839034709 33726677240773516634969)
              ·
                rfl

theorem cell22_2660140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 9].length) (baseStart_2660140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660140 prefixEnd_2660140 := by exact prefixLift 2660140
  have htrace : WordTrace (prefixWord ++ tailWord_2660140) baseStart_2660140 baseEnd_2660140 := by
    simpa [prefixWord, tailWord_2660140, baseEnd_2660140] using wordTrace_append hprefix tailTrace_2660140
  have hstable : (prefixWord ++ tailWord_2660140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660140).length < 2 ^ (prefixWord ++ tailWord_2660140).sum := by decide
  have hdescent : baseEnd_2660140 < baseStart_2660140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660185 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 9]
def baseStart_2660185 : Nat := 118140960795 + 2660185 * 2 ^ 59
def prefixEnd_2660185 : Nat := 4983230072969 + 3 ^ 40 * 2660185 * 2
def baseEnd_2660185 : Nat := 303545229973506610589675

theorem tailTrace_2660185 : CollatzResearch.WordTrace tailWord_2660185 prefixEnd_2660185 303545229973506610589675 := by
  unfold tailWord_2660185
  simp only [CollatzResearch.WordTrace]
  refine ⟨97024917867611543272574009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64683278578407695515049339 97024917867611543272574009)
  ·
    refine ⟨72768688400708657454430507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97024917867611543272574009 72768688400708657454430507)
    ·
      refine ⟨109153032601062986181645761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72768688400708657454430507 109153032601062986181645761)
      ·
        refine ⟨81864774450797239636234321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109153032601062986181645761 81864774450797239636234321)
        ·
          refine ⟨61398580838097929727175741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81864774450797239636234321 61398580838097929727175741)
          ·
            refine ⟨23024467814286723647690903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61398580838097929727175741 23024467814286723647690903)
            ·
              refine ⟨34536701721430085471536355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23024467814286723647690903 34536701721430085471536355)
              ·
                refine ⟨51805052582145128207304533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34536701721430085471536355 51805052582145128207304533)
                ·
                  refine ⟨303545229973506610589675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51805052582145128207304533 303545229973506610589675)
                  ·
                    rfl

theorem cell22_2660185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_2660185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660185 prefixEnd_2660185 := by exact prefixLift 2660185
  have htrace : WordTrace (prefixWord ++ tailWord_2660185) baseStart_2660185 baseEnd_2660185 := by
    simpa [prefixWord, tailWord_2660185, baseEnd_2660185] using wordTrace_append hprefix tailTrace_2660185
  have hstable : (prefixWord ++ tailWord_2660185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660185).length < 2 ^ (prefixWord ++ tailWord_2660185).sum := by decide
  have hdescent : baseEnd_2660185 < baseStart_2660185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660206 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_2660206 : Nat := 118140960795 + 2660206 * 2 ^ 59
def prefixEnd_2660206 : Nat := 4983230072969 + 3 ^ 40 * 2660206 * 2
def baseEnd_2660206 : Nat := 910642878649682776993961

theorem tailTrace_2660206 : CollatzResearch.WordTrace tailWord_2660206 prefixEnd_2660206 910642878649682776993961 := by
  unfold tailWord_2660206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12128210475066932982386059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64683789200356975906058981 12128210475066932982386059)
  ·
    refine ⟨18192315712600399473579089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12128210475066932982386059 18192315712600399473579089)
    ·
      refine ⟨13644236784450299605184317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18192315712600399473579089 13644236784450299605184317)
      ·
        refine ⟨5116588794168862351944119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13644236784450299605184317 5116588794168862351944119)
        ·
          refine ⟨7674883191253293527916179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5116588794168862351944119 7674883191253293527916179)
          ·
            refine ⟨11512324786879940291874269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7674883191253293527916179 11512324786879940291874269)
            ·
              refine ⟨4317121795079977609452851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11512324786879940291874269 4317121795079977609452851)
              ·
                refine ⟨6475682692619966414179277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4317121795079977609452851 6475682692619966414179277)
                ·
                  refine ⟨2428381009732487405317229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6475682692619966414179277 2428381009732487405317229)
                  ·
                    refine ⟨910642878649682776993961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2428381009732487405317229 910642878649682776993961)
                    ·
                      rfl

theorem cell22_2660206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_2660206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660206 prefixEnd_2660206 := by exact prefixLift 2660206
  have htrace : WordTrace (prefixWord ++ tailWord_2660206) baseStart_2660206 baseEnd_2660206 := by
    simpa [prefixWord, tailWord_2660206, baseEnd_2660206] using wordTrace_append hprefix tailTrace_2660206
  have hstable : (prefixWord ++ tailWord_2660206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660206).length < 2 ^ (prefixWord ++ tailWord_2660206).sum := by decide
  have hdescent : baseEnd_2660206 < baseStart_2660206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660215 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 1, 10]
def baseStart_2660215 : Nat := 118140960795 + 2660215 * 2 ^ 59
def prefixEnd_2660215 : Nat := 4983230072969 + 3 ^ 40 * 2660215 * 2
def baseEnd_2660215 : Nat := 910645959533609753518933

theorem tailTrace_2660215 : CollatzResearch.WordTrace tailWord_2660215 prefixEnd_2660215 910645959533609753518933 := by
  unfold tailWord_2660215
  simp only [CollatzResearch.WordTrace]
  refine ⟨97026012057502858396166099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64684008038335238930777399 97026012057502858396166099)
  ·
    refine ⟨145539018086254287594249149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97026012057502858396166099 145539018086254287594249149)
    ·
      refine ⟨54577131782345357847843431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145539018086254287594249149 54577131782345357847843431)
      ·
        refine ⟨81865697673518036771765147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54577131782345357847843431 81865697673518036771765147)
        ·
          refine ⟨122798546510277055157647721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81865697673518036771765147 122798546510277055157647721)
          ·
            refine ⟨92098909882707791368235791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122798546510277055157647721 92098909882707791368235791)
            ·
              refine ⟨138148364824061687052353687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92098909882707791368235791 138148364824061687052353687)
              ·
                refine ⟨207222547236092530578530531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138148364824061687052353687 207222547236092530578530531)
                ·
                  refine ⟨310833820854138795867795797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207222547236092530578530531 310833820854138795867795797)
                  ·
                    refine ⟨910645959533609753518933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 310833820854138795867795797 910645959533609753518933)
                    ·
                      rfl

theorem cell22_2660215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_2660215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660215 prefixEnd_2660215 := by exact prefixLift 2660215
  have htrace : WordTrace (prefixWord ++ tailWord_2660215) baseStart_2660215 baseEnd_2660215 := by
    simpa [prefixWord, tailWord_2660215, baseEnd_2660215] using wordTrace_append hprefix tailTrace_2660215
  have hstable : (prefixWord ++ tailWord_2660215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660215).length < 2 ^ (prefixWord ++ tailWord_2660215).sum := by decide
  have hdescent : baseEnd_2660215 < baseStart_2660215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660257 : List Nat := [1, 2, 3, 4, 3, 1, 2, 2, 1, 3]
def baseStart_2660257 : Nat := 118140960795 + 2660257 * 2 ^ 59
def prefixEnd_2660257 : Nat := 4983230072969 + 3 ^ 40 * 2660257 * 2
def baseEnd_2660257 : Nat := 910660336991935643968805

theorem tailTrace_2660257 : CollatzResearch.WordTrace tailWord_2660257 prefixEnd_2660257 910660336991935643968805 := by
  unfold tailWord_2660257
  simp only [CollatzResearch.WordTrace]
  refine ⟨97027543923350699569195025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64685029282233799712796683 97027543923350699569195025)
  ·
    refine ⟨72770657942513024676896269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97027543923350699569195025 72770657942513024676896269)
    ·
      refine ⟨27288996728442384253836101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72770657942513024676896269 27288996728442384253836101)
      ·
        refine ⟨5116686886582947047594269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27288996728442384253836101 5116686886582947047594269)
        ·
          refine ⟨1918757582468605142847851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5116686886582947047594269 1918757582468605142847851)
          ·
            refine ⟨2878136373702907714271777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918757582468605142847851 2878136373702907714271777)
            ·
              refine ⟨2158602280277180785703833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2878136373702907714271777 2158602280277180785703833)
              ·
                refine ⟨1618951710207885589277875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2158602280277180785703833 1618951710207885589277875)
                ·
                  refine ⟨2428427565311828383916813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618951710207885589277875 2428427565311828383916813)
                  ·
                    refine ⟨910660336991935643968805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2428427565311828383916813 910660336991935643968805)
                    ·
                      rfl

theorem cell22_2660257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_2660257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660257 prefixEnd_2660257 := by exact prefixLift 2660257
  have htrace : WordTrace (prefixWord ++ tailWord_2660257) baseStart_2660257 baseEnd_2660257 := by
    simpa [prefixWord, tailWord_2660257, baseEnd_2660257] using wordTrace_append hprefix tailTrace_2660257
  have hstable : (prefixWord ++ tailWord_2660257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660257).length < 2 ^ (prefixWord ++ tailWord_2660257).sum := by decide
  have hdescent : baseEnd_2660257 < baseStart_2660257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660313 : List Nat := [1, 2, 1, 2, 6, 2, 1, 2, 2, 3]
def baseStart_2660313 : Nat := 118140960795 + 2660313 * 2 ^ 59
def prefixEnd_2660313 : Nat := 4983230072969 + 3 ^ 40 * 2660313 * 2
def baseEnd_2660313 : Nat := 910679506936370164568633

theorem tailTrace_2660313 : CollatzResearch.WordTrace tailWord_2660313 prefixEnd_2660313 910679506936370164568633 := by
  unfold tailWord_2660313
  simp only [CollatzResearch.WordTrace]
  refine ⟨97029586411147821133233593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64686390940765214088822395 97029586411147821133233593)
  ·
    refine ⟨72772189808360865849925195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97029586411147821133233593 72772189808360865849925195)
    ·
      refine ⟨109158284712541298774887793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72772189808360865849925195 109158284712541298774887793)
      ·
        refine ⟨81868713534405974081165845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109158284712541298774887793 81868713534405974081165845)
        ·
          refine ⟨3837595946925280035054649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81868713534405974081165845 3837595946925280035054649)
          ·
            refine ⟨2878196960193960026290987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3837595946925280035054649 2878196960193960026290987)
            ·
              refine ⟨4317295440290940039436481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2878196960193960026290987 4317295440290940039436481)
              ·
                refine ⟨3237971580218205029577361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4317295440290940039436481 3237971580218205029577361)
                ·
                  refine ⟨2428478685163653772183021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3237971580218205029577361 2428478685163653772183021)
                  ·
                    refine ⟨910679506936370164568633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2428478685163653772183021 910679506936370164568633)
                    ·
                      rfl

theorem cell22_2660313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 3].length) (baseStart_2660313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660313 prefixEnd_2660313 := by exact prefixLift 2660313
  have htrace : WordTrace (prefixWord ++ tailWord_2660313) baseStart_2660313 baseEnd_2660313 := by
    simpa [prefixWord, tailWord_2660313, baseEnd_2660313] using wordTrace_append hprefix tailTrace_2660313
  have hstable : (prefixWord ++ tailWord_2660313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660313).length < 2 ^ (prefixWord ++ tailWord_2660313).sum := by decide
  have hdescent : baseEnd_2660313 < baseStart_2660313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660352 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 4, 5]
def baseStart_2660352 : Nat := 118140960795 + 2660352 * 2 ^ 59
def prefixEnd_2660352 : Nat := 4983230072969 + 3 ^ 40 * 2660352 * 2
def baseEnd_2660352 : Nat := 910692857433387062843513

theorem tailTrace_2660352 : CollatzResearch.WordTrace tailWord_2660352 prefixEnd_2660352 910692857433387062843513 := by
  unfold tailWord_2660352
  simp only [CollatzResearch.WordTrace]
  refine ⟨48515504429003265396951655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64687339238671020529268873 48515504429003265396951655)
  ·
    refine ⟨72773256643504898095427483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48515504429003265396951655 72773256643504898095427483)
    ·
      refine ⟨109159884965257347143141225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72773256643504898095427483 109159884965257347143141225)
      ·
        refine ⟨81869913723943010357355919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109159884965257347143141225 81869913723943010357355919)
        ·
          refine ⟨122804870585914515536033879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81869913723943010357355919 122804870585914515536033879)
          ·
            refine ⟨184207305878871773304050819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122804870585914515536033879 184207305878871773304050819)
            ·
              refine ⟨276310958818307659956076229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184207305878871773304050819 276310958818307659956076229)
              ·
                refine ⟨51808304778432686241764293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 276310958818307659956076229 51808304778432686241764293)
                ·
                  refine ⟨9714057145956128670330805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51808304778432686241764293 9714057145956128670330805)
                  ·
                    refine ⟨910692857433387062843513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9714057145956128670330805 910692857433387062843513)
                    ·
                      rfl

theorem cell22_2660352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_2660352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660352 prefixEnd_2660352 := by exact prefixLift 2660352
  have htrace : WordTrace (prefixWord ++ tailWord_2660352) baseStart_2660352 baseEnd_2660352 := by
    simpa [prefixWord, tailWord_2660352, baseEnd_2660352] using wordTrace_append hprefix tailTrace_2660352
  have hstable : (prefixWord ++ tailWord_2660352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660352).length < 2 ^ (prefixWord ++ tailWord_2660352).sum := by decide
  have hdescent : baseEnd_2660352 < baseStart_2660352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660375 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 3, 3]
def baseStart_2660375 : Nat := 118140960795 + 2660375 * 2 ^ 59
def prefixEnd_2660375 : Nat := 4983230072969 + 3 ^ 40 * 2660375 * 2
def baseEnd_2660375 : Nat := 910700730803422669518443

theorem tailTrace_2660375 : CollatzResearch.WordTrace tailWord_2660375 prefixEnd_2660375 910700730803422669518443 := by
  unfold tailWord_2660375
  simp only [CollatzResearch.WordTrace]
  refine ⟨97031847736923205721990579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64687898491282137147993719 97031847736923205721990579)
  ·
    refine ⟨145547771605384808582985869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97031847736923205721990579 145547771605384808582985869)
    ·
      refine ⟨54580414352019303218619701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145547771605384808582985869 54580414352019303218619701)
      ·
        refine ⟨5116913845501809676745597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54580414352019303218619701 5116913845501809676745597)
        ·
          refine ⟨1918842692063178628779599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5116913845501809676745597 1918842692063178628779599)
          ·
            refine ⟨2878264038094767943169399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918842692063178628779599 2878264038094767943169399)
            ·
              refine ⟨4317396057142151914754099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2878264038094767943169399 4317396057142151914754099)
              ·
                refine ⟨6476094085713227872131149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4317396057142151914754099 6476094085713227872131149)
                ·
                  refine ⟨2428535282142460452049181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6476094085713227872131149 2428535282142460452049181)
                  ·
                    refine ⟨910700730803422669518443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2428535282142460452049181 910700730803422669518443)
                    ·
                      rfl

theorem cell22_2660375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_2660375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660375 prefixEnd_2660375 := by exact prefixLift 2660375
  have htrace : WordTrace (prefixWord ++ tailWord_2660375) baseStart_2660375 baseEnd_2660375 := by
    simpa [prefixWord, tailWord_2660375, baseEnd_2660375] using wordTrace_append hprefix tailTrace_2660375
  have hstable : (prefixWord ++ tailWord_2660375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660375).length < 2 ^ (prefixWord ++ tailWord_2660375).sum := by decide
  have hdescent : baseEnd_2660375 < baseStart_2660375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660401 : List Nat := [1, 2, 2, 3, 1, 3, 3, 2, 1, 4]
def baseStart_2660401 : Nat := 118140960795 + 2660401 * 2 ^ 59
def prefixEnd_2660401 : Nat := 4983230072969 + 3 ^ 40 * 2660401 * 2
def baseEnd_2660401 : Nat := 910709631134767268368363

theorem tailTrace_2660401 : CollatzResearch.WordTrace tailWord_2660401 prefixEnd_2660401 910709631134767268368363 := by
  unfold tailWord_2660401
  simp only [CollatzResearch.WordTrace]
  refine ⟨97032796034829012162437057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64688530689886008108291371 97032796034829012162437057)
  ·
    refine ⟨72774597026121759121827793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97032796034829012162437057 72774597026121759121827793)
    ·
      refine ⟨54580947769591319341370845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72774597026121759121827793 54580947769591319341370845)
      ·
        refine ⟨20467855413596744753014067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54580947769591319341370845 20467855413596744753014067)
        ·
          refine ⟨30701783120395117129521101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20467855413596744753014067 30701783120395117129521101)
          ·
            refine ⟨11513168670148168923570413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30701783120395117129521101 11513168670148168923570413)
            ·
              refine ⟨4317438251305563346338905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11513168670148168923570413 4317438251305563346338905)
              ·
                refine ⟨3238078688479172509754179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4317438251305563346338905 3238078688479172509754179)
                ·
                  refine ⟨4857118032718758764631269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238078688479172509754179 4857118032718758764631269)
                  ·
                    refine ⟨910709631134767268368363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4857118032718758764631269 910709631134767268368363)
                    ·
                      rfl

theorem cell22_2660401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_2660401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660401 prefixEnd_2660401 := by exact prefixLift 2660401
  have htrace : WordTrace (prefixWord ++ tailWord_2660401) baseStart_2660401 baseEnd_2660401 := by
    simpa [prefixWord, tailWord_2660401, baseEnd_2660401] using wordTrace_append hprefix tailTrace_2660401
  have hstable : (prefixWord ++ tailWord_2660401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660401).length < 2 ^ (prefixWord ++ tailWord_2660401).sum := by decide
  have hdescent : baseEnd_2660401 < baseStart_2660401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660461 : List Nat := [1, 5, 1, 1, 2, 1, 5, 6]
def baseStart_2660461 : Nat := 118140960795 + 2660461 * 2 ^ 59
def prefixEnd_2660461 : Nat := 4983230072969 + 3 ^ 40 * 2660461 * 2
def baseEnd_2660461 : Nat := 101192241151216345763131

theorem tailTrace_2660461 : CollatzResearch.WordTrace tailWord_2660461 prefixEnd_2660461 101192241151216345763131 := by
  unfold tailWord_2660461
  simp only [CollatzResearch.WordTrace]
  refine ⟨97034984414611642409621237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64689989609741094939747491 97034984414611642409621237)
  ·
    refine ⟨9097029788869841475901991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97034984414611642409621237 9097029788869841475901991)
    ·
      refine ⟨13645544683304762213852987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9097029788869841475901991 13645544683304762213852987)
      ·
        refine ⟨20468317024957143320779481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13645544683304762213852987 20468317024957143320779481)
        ·
          refine ⟨15351237768717857490584611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20468317024957143320779481 15351237768717857490584611)
          ·
            refine ⟨23026856653076786235876917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15351237768717857490584611 23026856653076786235876917)
            ·
              refine ⟨2158767811225948709613461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23026856653076786235876917 2158767811225948709613461)
              ·
                refine ⟨101192241151216345763131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2158767811225948709613461 101192241151216345763131)
                ·
                  rfl

theorem cell22_2660461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 6].length) (baseStart_2660461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660461 prefixEnd_2660461 := by exact prefixLift 2660461
  have htrace : WordTrace (prefixWord ++ tailWord_2660461) baseStart_2660461 baseEnd_2660461 := by
    simpa [prefixWord, tailWord_2660461, baseEnd_2660461] using wordTrace_append hprefix tailTrace_2660461
  have hstable : (prefixWord ++ tailWord_2660461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660461).length < 2 ^ (prefixWord ++ tailWord_2660461).sum := by decide
  have hdescent : baseEnd_2660461 < baseStart_2660461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660489 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 7]
def baseStart_2660489 : Nat := 118140960795 + 2660489 * 2 ^ 59
def prefixEnd_2660489 : Nat := 4983230072969 + 3 ^ 40 * 2660489 * 2
def baseEnd_2660489 : Nat := 303579918444388124056031

theorem tailTrace_2660489 : CollatzResearch.WordTrace tailWord_2660489 prefixEnd_2660489 303579918444388124056031 := by
  unfold tailWord_2660489
  simp only [CollatzResearch.WordTrace]
  refine ⟨97036005658510203191640521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64690670439006802127760347 97036005658510203191640521)
  ·
    refine ⟨72777004243882652393730391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97036005658510203191640521 72777004243882652393730391)
    ·
      refine ⟨109165506365823978590595587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72777004243882652393730391 109165506365823978590595587)
      ·
        refine ⟨163748259548735967885893381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109165506365823978590595587 163748259548735967885893381)
        ·
          refine ⟨30702798665387993978605009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163748259548735967885893381 30702798665387993978605009)
          ·
            refine ⟨23027098999040995483953757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30702798665387993978605009 23027098999040995483953757)
            ·
              refine ⟨8635162124640373306482659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23027098999040995483953757 8635162124640373306482659)
              ·
                refine ⟨12952743186960559959723989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8635162124640373306482659 12952743186960559959723989)
                ·
                  refine ⟨303579918444388124056031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12952743186960559959723989 303579918444388124056031)
                  ·
                    rfl

theorem cell22_2660489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 7].length) (baseStart_2660489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660489 prefixEnd_2660489 := by exact prefixLift 2660489
  have htrace : WordTrace (prefixWord ++ tailWord_2660489) baseStart_2660489 baseEnd_2660489 := by
    simpa [prefixWord, tailWord_2660489, baseEnd_2660489] using wordTrace_append hprefix tailTrace_2660489
  have hstable : (prefixWord ++ tailWord_2660489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660489).length < 2 ^ (prefixWord ++ tailWord_2660489).sum := by decide
  have hdescent : baseEnd_2660489 < baseStart_2660489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660536 : List Nat := [2, 1, 2, 1, 2, 1, 3, 5, 1, 4]
def baseStart_2660536 : Nat := 118140960795 + 2660536 * 2 ^ 59
def prefixEnd_2660536 : Nat := 4983230072969 + 3 ^ 40 * 2660536 * 2
def baseEnd_2660536 : Nat := 910755844393671916242949

theorem tailTrace_2660536 : CollatzResearch.WordTrace tailWord_2660536 prefixEnd_2660536 910755844393671916242949 := by
  unfold tailWord_2660536
  simp only [CollatzResearch.WordTrace]
  refine ⟨48518859944669965109300731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64691813259559953479067641 48518859944669965109300731)
  ·
    refine ⟨72778289917004947663951097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48518859944669965109300731 72778289917004947663951097)
    ·
      refine ⟨54583717437753710747963323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72778289917004947663951097 54583717437753710747963323)
      ·
        refine ⟨81875576156630566121944985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54583717437753710747963323 81875576156630566121944985)
        ·
          refine ⟨61406682117472924591458739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81875576156630566121944985 61406682117472924591458739)
          ·
            refine ⟨92110023176209386887188109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61406682117472924591458739 92110023176209386887188109)
            ·
              refine ⟨34541258691078520082695541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92110023176209386887188109 34541258691078520082695541)
              ·
                refine ⟨3238243002288611257752707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34541258691078520082695541 3238243002288611257752707)
                ·
                  refine ⟨4857364503432916886629061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238243002288611257752707 4857364503432916886629061)
                  ·
                    refine ⟨910755844393671916242949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4857364503432916886629061 910755844393671916242949)
                    ·
                      rfl

theorem cell22_2660536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_2660536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660536 prefixEnd_2660536 := by exact prefixLift 2660536
  have htrace : WordTrace (prefixWord ++ tailWord_2660536) baseStart_2660536 baseEnd_2660536 := by
    simpa [prefixWord, tailWord_2660536, baseEnd_2660536] using wordTrace_append hprefix tailTrace_2660536
  have hstable : (prefixWord ++ tailWord_2660536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660536).length < 2 ^ (prefixWord ++ tailWord_2660536).sum := by decide
  have hdescent : baseEnd_2660536 < baseStart_2660536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660583 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 1, 5]
def baseStart_2660583 : Nat := 118140960795 + 2660583 * 2 ^ 59
def prefixEnd_2660583 : Nat := 4983230072969 + 3 ^ 40 * 2660583 * 2
def baseEnd_2660583 : Nat := 910771933454179460317805

theorem tailTrace_2660583 : CollatzResearch.WordTrace tailWord_2660583 prefixEnd_2660583 910771933454179460317805 := by
  unfold tailWord_2660583
  simp only [CollatzResearch.WordTrace]
  refine ⟨97039434120169657245562403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64692956080113104830374935 97039434120169657245562403)
  ·
    refine ⟨145559151180254485868343605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97039434120169657245562403 145559151180254485868343605)
    ·
      refine ⟨13646170423148858050157213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145559151180254485868343605 13646170423148858050157213)
      ·
        refine ⟨5117313908680821768808955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13646170423148858050157213 5117313908680821768808955)
        ·
          refine ⟨7675970863021232653213433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5117313908680821768808955 7675970863021232653213433)
          ·
            refine ⟨5756978147265924489910075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7675970863021232653213433 5756978147265924489910075)
            ·
              refine ⟨8635467220898886734865113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5756978147265924489910075 8635467220898886734865113)
              ·
                refine ⟨6476600415674165051148835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8635467220898886734865113 6476600415674165051148835)
                ·
                  refine ⟨9714900623511247576723253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6476600415674165051148835 9714900623511247576723253)
                  ·
                    refine ⟨910771933454179460317805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9714900623511247576723253 910771933454179460317805)
                    ·
                      rfl

theorem cell22_2660583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_2660583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660583 prefixEnd_2660583 := by exact prefixLift 2660583
  have htrace : WordTrace (prefixWord ++ tailWord_2660583) baseStart_2660583 baseEnd_2660583 := by
    simpa [prefixWord, tailWord_2660583, baseEnd_2660583] using wordTrace_append hprefix tailTrace_2660583
  have hstable : (prefixWord ++ tailWord_2660583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660583).length < 2 ^ (prefixWord ++ tailWord_2660583).sum := by decide
  have hdescent : baseEnd_2660583 < baseStart_2660583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660598 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_2660598 : Nat := 118140960795 + 2660598 * 2 ^ 59
def prefixEnd_2660598 : Nat := 4983230072969 + 3 ^ 40 * 2660598 * 2
def baseEnd_2660598 : Nat := 910777068260724421192759

theorem tailTrace_2660598 : CollatzResearch.WordTrace tailWord_2660598 prefixEnd_2660598 910777068260724421192759 := by
  unfold tailWord_2660598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6064998825944707175459903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64693320810076876538238965 6064998825944707175459903)
  ·
    refine ⟨9097498238917060763189855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6064998825944707175459903 9097498238917060763189855)
    ·
      refine ⟨13646247358375591144784783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9097498238917060763189855 13646247358375591144784783)
      ·
        refine ⟨20469371037563386717177175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13646247358375591144784783 20469371037563386717177175)
        ·
          refine ⟨30704056556345080075765763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20469371037563386717177175 30704056556345080075765763)
          ·
            refine ⟨46056084834517620113648645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30704056556345080075765763 46056084834517620113648645)
            ·
              refine ⟨8635515906472053771309121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46056084834517620113648645 8635515906472053771309121)
              ·
                refine ⟨6476636929854040328481841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8635515906472053771309121 6476636929854040328481841)
                ·
                  refine ⟨4857477697390530246361381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6476636929854040328481841 4857477697390530246361381)
                  ·
                    refine ⟨910777068260724421192759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4857477697390530246361381 910777068260724421192759)
                    ·
                      rfl

theorem cell22_2660598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_2660598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660598 prefixEnd_2660598 := by exact prefixLift 2660598
  have htrace : WordTrace (prefixWord ++ tailWord_2660598) baseStart_2660598 baseEnd_2660598 := by
    simpa [prefixWord, tailWord_2660598, baseEnd_2660598] using wordTrace_append hprefix tailTrace_2660598
  have hstable : (prefixWord ++ tailWord_2660598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660598).length < 2 ^ (prefixWord ++ tailWord_2660598).sum := by decide
  have hdescent : baseEnd_2660598 < baseStart_2660598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660658 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 7]
def baseStart_2660658 : Nat := 118140960795 + 2660658 * 2 ^ 59
def prefixEnd_2660658 : Nat := 4983230072969 + 3 ^ 40 * 2660658 * 2
def baseEnd_2660658 : Nat := 303599202495634754897525

theorem tailTrace_2660658 : CollatzResearch.WordTrace tailWord_2660658 prefixEnd_2660658 303599202495634754897525 := by
  unfold tailWord_2660658
  simp only [CollatzResearch.WordTrace]
  refine ⟨24260542398724486263635657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64694779729931963369695085 24260542398724486263635657)
  ·
    refine ⟨18195406799043364697726743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24260542398724486263635657 18195406799043364697726743)
    ·
      refine ⟨27293110198565047046590115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18195406799043364697726743 27293110198565047046590115)
      ·
        refine ⟨40939665297847570569885173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27293110198565047046590115 40939665297847570569885173)
        ·
          refine ⟨3838093621673209740926735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40939665297847570569885173 3838093621673209740926735)
          ·
            refine ⟨5757140432509814611390103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3838093621673209740926735 5757140432509814611390103)
            ·
              refine ⟨8635710648764721917085155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5757140432509814611390103 8635710648764721917085155)
              ·
                refine ⟨12953565973147082875627733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8635710648764721917085155 12953565973147082875627733)
                ·
                  refine ⟨303599202495634754897525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12953565973147082875627733 303599202495634754897525)
                  ·
                    rfl

theorem cell22_2660658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_2660658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660658 prefixEnd_2660658 := by exact prefixLift 2660658
  have htrace : WordTrace (prefixWord ++ tailWord_2660658) baseStart_2660658 baseEnd_2660658 := by
    simpa [prefixWord, tailWord_2660658, baseEnd_2660658] using wordTrace_append hprefix tailTrace_2660658
  have hstable : (prefixWord ++ tailWord_2660658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660658).length < 2 ^ (prefixWord ++ tailWord_2660658).sum := by decide
  have hdescent : baseEnd_2660658 < baseStart_2660658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660686 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_2660686 : Nat := 118140960795 + 2660686 * 2 ^ 59
def prefixEnd_2660686 : Nat := 4983230072969 + 3 ^ 40 * 2660686 * 2
def baseEnd_2660686 : Nat := 303602397486373841664163

theorem tailTrace_2660686 : CollatzResearch.WordTrace tailWord_2660686 prefixEnd_2660686 303602397486373841664163 := by
  unfold tailWord_2660686
  simp only [CollatzResearch.WordTrace]
  refine ⟨12130398854849563229570239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64695460559197670557707941 12130398854849563229570239)
  ·
    refine ⟨18195598282274344844355359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12130398854849563229570239 18195598282274344844355359)
    ·
      refine ⟨27293397423411517266533039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18195598282274344844355359 27293397423411517266533039)
      ·
        refine ⟨40940096135117275899799559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27293397423411517266533039 40940096135117275899799559)
        ·
          refine ⟨61410144202675913849699339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40940096135117275899799559 61410144202675913849699339)
          ·
            refine ⟨92115216304013870774549009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61410144202675913849699339 92115216304013870774549009)
            ·
              refine ⟨69086412228010403080911757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92115216304013870774549009 69086412228010403080911757)
              ·
                refine ⟨25907404585503901155341909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69086412228010403080911757 25907404585503901155341909)
                ·
                  refine ⟨303602397486373841664163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25907404585503901155341909 303602397486373841664163)
                  ·
                    rfl

theorem cell22_2660686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_2660686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660686 prefixEnd_2660686 := by exact prefixLift 2660686
  have htrace : WordTrace (prefixWord ++ tailWord_2660686) baseStart_2660686 baseEnd_2660686 := by
    simpa [prefixWord, tailWord_2660686, baseEnd_2660686] using wordTrace_append hprefix tailTrace_2660686
  have hstable : (prefixWord ++ tailWord_2660686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660686).length < 2 ^ (prefixWord ++ tailWord_2660686).sum := by decide
  have hdescent : baseEnd_2660686 < baseStart_2660686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660688 : List Nat := [2, 1, 1, 1, 1, 6, 1, 4, 1, 4]
def baseStart_2660688 : Nat := 118140960795 + 2660688 * 2 ^ 59
def prefixEnd_2660688 : Nat := 4983230072969 + 3 ^ 40 * 2660688 * 2
def baseEnd_2660688 : Nat := 910807877099994186442483

theorem tailTrace_2660688 : CollatzResearch.WordTrace tailWord_2660688 prefixEnd_2660688 910807877099994186442483 := by
  unfold tailWord_2660688
  simp only [CollatzResearch.WordTrace]
  refine ⟨48521631892394630089067359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64695509189859506785423145 48521631892394630089067359)
  ·
    refine ⟨72782447838591945133601039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48521631892394630089067359 72782447838591945133601039)
    ·
      refine ⟨109173671757887917700401559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72782447838591945133601039 109173671757887917700401559)
      ·
        refine ⟨163760507636831876550602339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109173671757887917700401559 163760507636831876550602339)
        ·
          refine ⟨245640761455247814825903509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163760507636831876550602339 245640761455247814825903509)
          ·
            refine ⟨11514410693214741319964227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 245640761455247814825903509 11514410693214741319964227)
            ·
              refine ⟨17271616039822111979946341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11514410693214741319964227 17271616039822111979946341)
              ·
                refine ⟨3238428007466645996239939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17271616039822111979946341 3238428007466645996239939)
                ·
                  refine ⟨4857642011199968994359909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238428007466645996239939 4857642011199968994359909)
                  ·
                    refine ⟨910807877099994186442483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4857642011199968994359909 910807877099994186442483)
                    ·
                      rfl

theorem cell22_2660688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_2660688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660688 prefixEnd_2660688 := by exact prefixLift 2660688
  have htrace : WordTrace (prefixWord ++ tailWord_2660688) baseStart_2660688 baseEnd_2660688 := by
    simpa [prefixWord, tailWord_2660688, baseEnd_2660688] using wordTrace_append hprefix tailTrace_2660688
  have hstable : (prefixWord ++ tailWord_2660688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660688).length < 2 ^ (prefixWord ++ tailWord_2660688).sum := by decide
  have hdescent : baseEnd_2660688 < baseStart_2660688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660726 : List Nat := [5, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_2660726 : Nat := 118140960795 + 2660726 * 2 ^ 59
def prefixEnd_2660726 : Nat := 4983230072969 + 3 ^ 40 * 2660726 * 2
def baseEnd_2660726 : Nat := 303606961758858251330789

theorem tailTrace_2660726 : CollatzResearch.WordTrace tailWord_2660726 prefixEnd_2660726 303606961758858251330789 := by
  unfold tailWord_2660726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6065290609915724541751127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64696433172434395112012021 6065290609915724541751127)
  ·
    refine ⟨9097935914873586812626691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6065290609915724541751127 9097935914873586812626691)
    ·
      refine ⟨13646903872310380218940037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9097935914873586812626691 13646903872310380218940037)
      ·
        refine ⟨2558794476058196291051257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13646903872310380218940037 2558794476058196291051257)
        ·
          refine ⟨1919095857043647218288443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2558794476058196291051257 1919095857043647218288443)
          ·
            refine ⟨2878643785565470827432665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919095857043647218288443 2878643785565470827432665)
            ·
              refine ⟨2158982839174103120574499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2878643785565470827432665 2158982839174103120574499)
              ·
                refine ⟨3238474258761154680861749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158982839174103120574499 3238474258761154680861749)
                ·
                  refine ⟨303606961758858251330789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3238474258761154680861749 303606961758858251330789)
                  ·
                    rfl

theorem cell22_2660726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_2660726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660726 prefixEnd_2660726 := by exact prefixLift 2660726
  have htrace : WordTrace (prefixWord ++ tailWord_2660726) baseStart_2660726 baseEnd_2660726 := by
    simpa [prefixWord, tailWord_2660726, baseEnd_2660726] using wordTrace_append hprefix tailTrace_2660726
  have hstable : (prefixWord ++ tailWord_2660726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660726).length < 2 ^ (prefixWord ++ tailWord_2660726).sum := by decide
  have hdescent : baseEnd_2660726 < baseStart_2660726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660731 : List Nat := [1, 1, 1, 1, 1, 7, 1, 9]
def baseStart_2660731 : Nat := 118140960795 + 2660731 * 2 ^ 59
def prefixEnd_2660731 : Nat := 4983230072969 + 3 ^ 40 * 2660731 * 2
def baseEnd_2660731 : Nat := 101202510764306267513039

theorem tailTrace_2660731 : CollatzResearch.WordTrace tailWord_2660731 prefixEnd_2660731 101202510764306267513039 := by
  unfold tailWord_2660731
  simp only [CollatzResearch.WordTrace]
  refine ⟨97044832123633478521950047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64696554749088985681300031 97044832123633478521950047)
  ·
    refine ⟨145567248185450217782925071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97044832123633478521950047 145567248185450217782925071)
    ·
      refine ⟨218350872278175326674387607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145567248185450217782925071 218350872278175326674387607)
      ·
        refine ⟨327526308417262990011581411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218350872278175326674387607 327526308417262990011581411)
        ·
          refine ⟨491289462625894485017372117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327526308417262990011581411 491289462625894485017372117)
          ·
            refine ⟨11514596780294401992594659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 491289462625894485017372117 11514596780294401992594659)
            ·
              refine ⟨17271895170441602988891989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11514596780294401992594659 17271895170441602988891989)
              ·
                refine ⟨101202510764306267513039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17271895170441602988891989 101202510764306267513039)
                ·
                  rfl

theorem cell22_2660731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 9].length) (baseStart_2660731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660731 prefixEnd_2660731 := by exact prefixLift 2660731
  have htrace : WordTrace (prefixWord ++ tailWord_2660731) baseStart_2660731 baseEnd_2660731 := by
    simpa [prefixWord, tailWord_2660731, baseEnd_2660731] using wordTrace_append hprefix tailTrace_2660731
  have hstable : (prefixWord ++ tailWord_2660731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660731).length < 2 ^ (prefixWord ++ tailWord_2660731).sum := by decide
  have hdescent : baseEnd_2660731 < baseStart_2660731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660750 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_2660750 : Nat := 118140960795 + 2660750 * 2 ^ 59
def prefixEnd_2660750 : Nat := 4983230072969 + 3 ^ 40 * 2660750 * 2
def baseEnd_2660750 : Nat := 910829100967046691392293

theorem tailTrace_2660750 : CollatzResearch.WordTrace tailWord_2660750 prefixEnd_2660750 910829100967046691392293 := by
  unfold tailWord_2660750
  simp only [CollatzResearch.WordTrace]
  refine ⟨12130690638820580595861463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64697016740376429844594469 12130690638820580595861463)
  ·
    refine ⟨18196035958230870893792195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12130690638820580595861463 18196035958230870893792195)
    ·
      refine ⟨27294053937346306340688293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18196035958230870893792195 27294053937346306340688293)
      ·
        refine ⟨5117635113252432438879055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27294053937346306340688293 5117635113252432438879055)
        ·
          refine ⟨7676452669878648658318583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5117635113252432438879055 7676452669878648658318583)
          ·
            refine ⟨11514679004817972987477875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7676452669878648658318583 11514679004817972987477875)
            ·
              refine ⟨17272018507226959481216813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11514679004817972987477875 17272018507226959481216813)
              ·
                refine ⟨6477006940210109805456305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17272018507226959481216813 6477006940210109805456305)
                ·
                  refine ⟨4857755205157582354092229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6477006940210109805456305 4857755205157582354092229)
                  ·
                    refine ⟨910829100967046691392293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4857755205157582354092229 910829100967046691392293)
                    ·
                      rfl

theorem cell22_2660750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_2660750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660750 prefixEnd_2660750 := by exact prefixLift 2660750
  have htrace : WordTrace (prefixWord ++ tailWord_2660750) baseStart_2660750 baseEnd_2660750 := by
    simpa [prefixWord, tailWord_2660750, baseEnd_2660750] using wordTrace_append hprefix tailTrace_2660750
  have hstable : (prefixWord ++ tailWord_2660750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660750).length < 2 ^ (prefixWord ++ tailWord_2660750).sum := by decide
  have hdescent : baseEnd_2660750 < baseStart_2660750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660769 : List Nat := [1, 2, 3, 5, 1, 1, 2, 2, 2, 3]
def baseStart_2660769 : Nat := 118140960795 + 2660769 * 2 ^ 59
def prefixEnd_2660769 : Nat := 4983230072969 + 3 ^ 40 * 2660769 * 2
def baseEnd_2660769 : Nat := 910835605055336975167235

theorem tailTrace_2660769 : CollatzResearch.WordTrace tailWord_2660769 prefixEnd_2660769 910835605055336975167235 := by
  unfold tailWord_2660769
  simp only [CollatzResearch.WordTrace]
  refine ⟨97046218097495811011833361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64697478731663874007888907 97046218097495811011833361)
  ·
    refine ⟨72784663573121858258875021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97046218097495811011833361 72784663573121858258875021)
    ·
      refine ⟨27294248839920696847078133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72784663573121858258875021 27294248839920696847078133)
      ·
        refine ⟨2558835828742565329413575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27294248839920696847078133 2558835828742565329413575)
        ·
          refine ⟨3838253743113847994120363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558835828742565329413575 3838253743113847994120363)
          ·
            refine ⟨5757380614670771991180545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3838253743113847994120363 5757380614670771991180545)
            ·
              refine ⟨4318035461003078993385409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5757380614670771991180545 4318035461003078993385409)
              ·
                refine ⟨3238526595752309245039057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4318035461003078993385409 3238526595752309245039057)
                ·
                  refine ⟨2428894946814231933779293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3238526595752309245039057 2428894946814231933779293)
                  ·
                    refine ⟨910835605055336975167235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2428894946814231933779293 910835605055336975167235)
                    ·
                      rfl

theorem cell22_2660769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_2660769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660769 prefixEnd_2660769 := by exact prefixLift 2660769
  have htrace : WordTrace (prefixWord ++ tailWord_2660769) baseStart_2660769 baseEnd_2660769 := by
    simpa [prefixWord, tailWord_2660769, baseEnd_2660769] using wordTrace_append hprefix tailTrace_2660769
  have hstable : (prefixWord ++ tailWord_2660769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660769).length < 2 ^ (prefixWord ++ tailWord_2660769).sum := by decide
  have hdescent : baseEnd_2660769 < baseStart_2660769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660801 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 2, 4]
def baseStart_2660801 : Nat := 118140960795 + 2660801 * 2 ^ 59
def prefixEnd_2660801 : Nat := 4983230072969 + 3 ^ 40 * 2660801 * 2
def baseEnd_2660801 : Nat := 910846559309299558367137

theorem tailTrace_2660801 : CollatzResearch.WordTrace tailWord_2660801 prefixEnd_2660801 910846559309299558367137 := by
  unfold tailWord_2660801
  simp only [CollatzResearch.WordTrace]
  refine ⟨97047385233379880476998257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64698256822253253651332171 97047385233379880476998257)
  ·
    refine ⟨72785538925034910357748693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97047385233379880476998257 72785538925034910357748693)
    ·
      refine ⟨1705911068555505711509735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 72785538925034910357748693 1705911068555505711509735)
      ·
        refine ⟨2558866602833258567264603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705911068555505711509735 2558866602833258567264603)
        ·
          refine ⟨3838299904249887850896905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558866602833258567264603 3838299904249887850896905)
          ·
            refine ⟨2878724928187415888172679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3838299904249887850896905 2878724928187415888172679)
            ·
              refine ⟨4318087392281123832259019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2878724928187415888172679 4318087392281123832259019)
              ·
                refine ⟨6477131088421685748388529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4318087392281123832259019 6477131088421685748388529)
                ·
                  refine ⟨4857848316316264311291397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6477131088421685748388529 4857848316316264311291397)
                  ·
                    refine ⟨910846559309299558367137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4857848316316264311291397 910846559309299558367137)
                    ·
                      rfl

theorem cell22_2660801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_2660801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660801 prefixEnd_2660801 := by exact prefixLift 2660801
  have htrace : WordTrace (prefixWord ++ tailWord_2660801) baseStart_2660801 baseEnd_2660801 := by
    simpa [prefixWord, tailWord_2660801, baseEnd_2660801] using wordTrace_append hprefix tailTrace_2660801
  have hstable : (prefixWord ++ tailWord_2660801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660801).length < 2 ^ (prefixWord ++ tailWord_2660801).sum := by decide
  have hdescent : baseEnd_2660801 < baseStart_2660801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660885 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_2660885 : Nat := 118140960795 + 2660885 * 2 ^ 59
def prefixEnd_2660885 : Nat := 4983230072969 + 3 ^ 40 * 2660885 * 2
def baseEnd_2660885 : Nat := 910875314225951339266879

theorem tailTrace_2660885 : CollatzResearch.WordTrace tailWord_2660885 prefixEnd_2660885 910875314225951339266879 := by
  unfold tailWord_2660885
  simp only [CollatzResearch.WordTrace]
  refine ⟨97050448965075562823056109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64700299310050375215370739 97050448965075562823056109)
  ·
    refine ⟨36393918361903336058646041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97050448965075562823056109 36393918361903336058646041)
    ·
      refine ⟨27295438771427502043984531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36393918361903336058646041 27295438771427502043984531)
      ·
        refine ⟨40943158157141253065976797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27295438771427502043984531 40943158157141253065976797)
        ·
          refine ⟨15353684308927969899741299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40943158157141253065976797 15353684308927969899741299)
          ·
            refine ⟨23030526463391954849611949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15353684308927969899741299 23030526463391954849611949)
            ·
              refine ⟨8636447423771983068604481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23030526463391954849611949 8636447423771983068604481)
              ·
                refine ⟨6477335567828987301453361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8636447423771983068604481 6477335567828987301453361)
                ·
                  refine ⟨4858001675871740476090021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6477335567828987301453361 4858001675871740476090021)
                  ·
                    refine ⟨910875314225951339266879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4858001675871740476090021 910875314225951339266879)
                    ·
                      rfl

theorem cell22_2660885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_2660885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660885 prefixEnd_2660885 := by exact prefixLift 2660885
  have htrace : WordTrace (prefixWord ++ tailWord_2660885) baseStart_2660885 baseEnd_2660885 := by
    simpa [prefixWord, tailWord_2660885, baseEnd_2660885] using wordTrace_append hprefix tailTrace_2660885
  have hstable : (prefixWord ++ tailWord_2660885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660885).length < 2 ^ (prefixWord ++ tailWord_2660885).sum := by decide
  have hdescent : baseEnd_2660885 < baseStart_2660885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660904 : List Nat := [2, 1, 5, 2, 1, 2, 1, 3, 2, 3]
def baseStart_2660904 : Nat := 118140960795 + 2660904 * 2 ^ 59
def prefixEnd_2660904 : Nat := 4983230072969 + 3 ^ 40 * 2660904 * 2
def baseEnd_2660904 : Nat := 910881818314241623041821

theorem tailTrace_2660904 : CollatzResearch.WordTrace tailWord_2660904 prefixEnd_2660904 910881818314241623041821 := by
  unfold tailWord_2660904
  simp only [CollatzResearch.WordTrace]
  refine ⟨48525570976003364533998883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64700761301337819378665177 48525570976003364533998883)
  ·
    refine ⟨72788356464005046800998325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48525570976003364533998883 72788356464005046800998325)
    ·
      refine ⟨6823908418500473137593593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72788356464005046800998325 6823908418500473137593593)
      ·
        refine ⟨5117931313875354853195195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6823908418500473137593593 5117931313875354853195195)
        ·
          refine ⟨7676896970813032279792793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5117931313875354853195195 7676896970813032279792793)
          ·
            refine ⟨5757672728109774209844595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7676896970813032279792793 5757672728109774209844595)
            ·
              refine ⟨8636509092164661314766893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5757672728109774209844595 8636509092164661314766893)
              ·
                refine ⟨3238690909561747993037585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8636509092164661314766893 3238690909561747993037585)
                ·
                  refine ⟨2429018182171310994778189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3238690909561747993037585 2429018182171310994778189)
                  ·
                    refine ⟨910881818314241623041821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2429018182171310994778189 910881818314241623041821)
                    ·
                      rfl

theorem cell22_2660904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_2660904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660904 prefixEnd_2660904 := by exact prefixLift 2660904
  have htrace : WordTrace (prefixWord ++ tailWord_2660904) baseStart_2660904 baseEnd_2660904 := by
    simpa [prefixWord, tailWord_2660904, baseEnd_2660904] using wordTrace_append hprefix tailTrace_2660904
  have hstable : (prefixWord ++ tailWord_2660904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660904).length < 2 ^ (prefixWord ++ tailWord_2660904).sum := by decide
  have hdescent : baseEnd_2660904 < baseStart_2660904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660915 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 5, 3]
def baseStart_2660915 : Nat := 118140960795 + 2660915 * 2 ^ 59
def prefixEnd_2660915 : Nat := 4983230072969 + 3 ^ 40 * 2660915 * 2
def baseEnd_2660915 : Nat := 910885583839041261016787

theorem tailTrace_2660915 : CollatzResearch.WordTrace tailWord_2660915 prefixEnd_2660915 910885583839041261016787 := by
  unfold tailWord_2660915
  simp only [CollatzResearch.WordTrace]
  refine ⟨97051543154966877946648199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64701028769977918631098799 97051543154966877946648199)
  ·
    refine ⟨145577314732450316919972299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97051543154966877946648199 145577314732450316919972299)
    ·
      refine ⟨218365972098675475379958449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145577314732450316919972299 218365972098675475379958449)
      ·
        refine ⟨163774479074006606534968837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218365972098675475379958449 163774479074006606534968837)
        ·
          refine ⟨30707714826376238725306657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163774479074006606534968837 30707714826376238725306657)
          ·
            refine ⟨23030786119782179043979993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30707714826376238725306657 23030786119782179043979993)
            ·
              refine ⟨17273089589836634282984995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23030786119782179043979993 17273089589836634282984995)
              ·
                refine ⟨25909634384754951424477493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17273089589836634282984995 25909634384754951424477493)
                ·
                  refine ⟨2429028223570776696044765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25909634384754951424477493 2429028223570776696044765)
                  ·
                    refine ⟨910885583839041261016787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2429028223570776696044765 910885583839041261016787)
                    ·
                      rfl

theorem cell22_2660915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 3].length) (baseStart_2660915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660915 prefixEnd_2660915 := by exact prefixLift 2660915
  have htrace : WordTrace (prefixWord ++ tailWord_2660915) baseStart_2660915 baseEnd_2660915 := by
    simpa [prefixWord, tailWord_2660915, baseEnd_2660915] using wordTrace_append hprefix tailTrace_2660915
  have hstable : (prefixWord ++ tailWord_2660915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660915).length < 2 ^ (prefixWord ++ tailWord_2660915).sum := by decide
  have hdescent : baseEnd_2660915 < baseStart_2660915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660928 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 9]
def baseStart_2660928 : Nat := 118140960795 + 2660928 * 2 ^ 59
def prefixEnd_2660928 : Nat := 4983230072969 + 3 ^ 40 * 2660928 * 2
def baseEnd_2660928 : Nat := 303630011334904520147249

theorem tailTrace_2660928 : CollatzResearch.WordTrace tailWord_2660928 prefixEnd_2660928 303630011334904520147249 := by
  unfold tailWord_2660928
  simp only [CollatzResearch.WordTrace]
  refine ⟨48526008651959890583435719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64701344869279854111247625 48526008651959890583435719)
  ·
    refine ⟨72789012977939835875153579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48526008651959890583435719 72789012977939835875153579)
    ·
      refine ⟨109183519466909753812730369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72789012977939835875153579 109183519466909753812730369)
      ·
        refine ⟨81887639600182315359547777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109183519466909753812730369 81887639600182315359547777)
        ·
          refine ⟨61415729700136736519660833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81887639600182315359547777 61415729700136736519660833)
          ·
            refine ⟨46061797275102552389745625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61415729700136736519660833 46061797275102552389745625)
            ·
              refine ⟨34546347956326914292309219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46061797275102552389745625 34546347956326914292309219)
              ·
                refine ⟨51819521934490371438463829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34546347956326914292309219 51819521934490371438463829)
                ·
                  refine ⟨303630011334904520147249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51819521934490371438463829 303630011334904520147249)
                  ·
                    rfl

theorem cell22_2660928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_2660928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660928 prefixEnd_2660928 := by exact prefixLift 2660928
  have htrace : WordTrace (prefixWord ++ tailWord_2660928) baseStart_2660928 baseEnd_2660928 := by
    simpa [prefixWord, tailWord_2660928, baseEnd_2660928] using wordTrace_append hprefix tailTrace_2660928
  have hstable : (prefixWord ++ tailWord_2660928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660928).length < 2 ^ (prefixWord ++ tailWord_2660928).sum := by decide
  have hdescent : baseEnd_2660928 < baseStart_2660928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660945 : List Nat := [1, 2, 2, 1, 3, 3, 1, 4, 5]
def baseStart_2660945 : Nat := 118140960795 + 2660945 * 2 ^ 59
def prefixEnd_2660945 : Nat := 4983230072969 + 3 ^ 40 * 2660945 * 2
def baseEnd_2660945 : Nat := 303631951150710394255565

theorem tailTrace_2660945 : CollatzResearch.WordTrace tailWord_2660945 prefixEnd_2660945 303631951150710394255565 := by
  unfold tailWord_2660945
  simp only [CollatzResearch.WordTrace]
  refine ⟨97052637344858193070240289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64701758229905462046826859 97052637344858193070240289)
  ·
    refine ⟨72789478008643644802680217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97052637344858193070240289 72789478008643644802680217)
    ·
      refine ⟨54592108506482733602010163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72789478008643644802680217 54592108506482733602010163)
      ·
        refine ⟨81888162759724100403015245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54592108506482733602010163 81888162759724100403015245)
        ·
          refine ⟨30708061034896537651130717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81888162759724100403015245 30708061034896537651130717)
          ·
            refine ⟨11515522888086201619174019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30708061034896537651130717 11515522888086201619174019)
            ·
              refine ⟨17273284332129302428761029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11515522888086201619174019 17273284332129302428761029)
              ·
                refine ⟨3238740812274244205392693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17273284332129302428761029 3238740812274244205392693)
                ·
                  refine ⟨303631951150710394255565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3238740812274244205392693 303631951150710394255565)
                  ·
                    rfl

theorem cell22_2660945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 5].length) (baseStart_2660945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660945 prefixEnd_2660945 := by exact prefixLift 2660945
  have htrace : WordTrace (prefixWord ++ tailWord_2660945) baseStart_2660945 baseEnd_2660945 := by
    simpa [prefixWord, tailWord_2660945, baseEnd_2660945] using wordTrace_append hprefix tailTrace_2660945
  have hstable : (prefixWord ++ tailWord_2660945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660945).length < 2 ^ (prefixWord ++ tailWord_2660945).sum := by decide
  have hdescent : baseEnd_2660945 < baseStart_2660945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660975 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 3, 4]
def baseStart_2660975 : Nat := 118140960795 + 2660975 * 2 ^ 59
def prefixEnd_2660975 : Nat := 4983230072969 + 3 ^ 40 * 2660975 * 2
def baseEnd_2660975 : Nat := 910906123065221104516603

theorem tailTrace_2660975 : CollatzResearch.WordTrace tailWord_2660975 prefixEnd_2660975 910906123065221104516603 := by
  unfold tailWord_2660975
  simp only [CollatzResearch.WordTrace]
  refine ⟨97053731534749508193832379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64702487689833005462554919 97053731534749508193832379)
  ·
    refine ⟨145580597302124262290748569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97053731534749508193832379 145580597302124262290748569)
    ·
      refine ⟨109185447976593196718061427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145580597302124262290748569 109185447976593196718061427)
      ·
        refine ⟨163778171964889795077092141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109185447976593196718061427 163778171964889795077092141)
        ·
          refine ⟨61416814486833673153909553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163778171964889795077092141 61416814486833673153909553)
          ·
            refine ⟨46062610865125254865432165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61416814486833673153909553 46062610865125254865432165)
            ·
              refine ⟨8636739537210985287268531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46062610865125254865432165 8636739537210985287268531)
              ·
                refine ⟨12955109305816477930902797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8636739537210985287268531 12955109305816477930902797)
                ·
                  refine ⟨4858165989681179224088549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12955109305816477930902797 4858165989681179224088549)
                  ·
                    refine ⟨910906123065221104516603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4858165989681179224088549 910906123065221104516603)
                    ·
                      rfl

theorem cell22_2660975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_2660975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660975 prefixEnd_2660975 := by exact prefixLift 2660975
  have htrace : WordTrace (prefixWord ++ tailWord_2660975) baseStart_2660975 baseEnd_2660975 := by
    simpa [prefixWord, tailWord_2660975, baseEnd_2660975] using wordTrace_append hprefix tailTrace_2660975
  have hstable : (prefixWord ++ tailWord_2660975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660975).length < 2 ^ (prefixWord ++ tailWord_2660975).sum := by decide
  have hdescent : baseEnd_2660975 < baseStart_2660975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660992 : List Nat := [2, 1, 1, 2, 1, 6, 1, 3, 1, 4]
def baseStart_2660992 : Nat := 118140960795 + 2660992 * 2 ^ 59
def prefixEnd_2660992 : Nat := 4983230072969 + 3 ^ 40 * 2660992 * 2
def baseEnd_2660992 : Nat := 910911942512638726841551

theorem tailTrace_2660992 : CollatzResearch.WordTrace tailWord_2660992 prefixEnd_2660992 910911942512638726841551 := by
  unfold tailWord_2660992
  simp only [CollatzResearch.WordTrace]
  refine ⟨48527175787843960048600615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64702901050458613398134153 48527175787843960048600615)
  ·
    refine ⟨72790763681765940072900923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48527175787843960048600615 72790763681765940072900923)
    ·
      refine ⟨109186145522648910109351385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72790763681765940072900923 109186145522648910109351385)
      ·
        refine ⟨81889609141986682582013539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109186145522648910109351385 81889609141986682582013539)
        ·
          refine ⟨122834413712980023873020309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81889609141986682582013539 122834413712980023873020309)
          ·
            refine ⟨5757863142795938619047827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122834413712980023873020309 5757863142795938619047827)
            ·
              refine ⟨8636794714193907928571741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5757863142795938619047827 8636794714193907928571741)
              ·
                refine ⟨3238798017822715473214403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8636794714193907928571741 3238798017822715473214403)
                ·
                  refine ⟨4858197026734073209821605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238798017822715473214403 4858197026734073209821605)
                  ·
                    refine ⟨910911942512638726841551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4858197026734073209821605 910911942512638726841551)
                    ·
                      rfl

theorem cell22_2660992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_2660992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2660992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2660992 prefixEnd_2660992 := by exact prefixLift 2660992
  have htrace : WordTrace (prefixWord ++ tailWord_2660992) baseStart_2660992 baseEnd_2660992 := by
    simpa [prefixWord, tailWord_2660992, baseEnd_2660992] using wordTrace_append hprefix tailTrace_2660992
  have hstable : (prefixWord ++ tailWord_2660992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660992).length < 2 ^ (prefixWord ++ tailWord_2660992).sum := by decide
  have hdescent : baseEnd_2660992 < baseStart_2660992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661037 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_2661037 : Nat := 118140960795 + 2661037 * 2 ^ 59
def prefixEnd_2661037 : Nat := 4983230072969 + 3 ^ 40 * 2661037 * 2
def baseEnd_2661037 : Nat := 910927346932273609466413

theorem tailTrace_2661037 : CollatzResearch.WordTrace tailWord_2661037 prefixEnd_2661037 910927346932273609466413 := by
  unfold tailWord_2661037
  simp only [CollatzResearch.WordTrace]
  refine ⟨97055992860524892782589365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64703995240349928521726243 97055992860524892782589365)
  ·
    refine ⟨9098999330674208698367753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97055992860524892782589365 9098999330674208698367753)
    ·
      refine ⟨6824249498005656523775815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9098999330674208698367753 6824249498005656523775815)
      ·
        refine ⟨10236374247008484785663723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6824249498005656523775815 10236374247008484785663723)
        ·
          refine ⟨15354561370512727178495585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10236374247008484785663723 15354561370512727178495585)
          ·
            refine ⟨11515921027884545383871689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15354561370512727178495585 11515921027884545383871689)
            ·
              refine ⟨8636940770913409037903767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11515921027884545383871689 8636940770913409037903767)
              ·
                refine ⟨12955411156370113556855651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8636940770913409037903767 12955411156370113556855651)
                ·
                  refine ⟨19433116734555170335283477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12955411156370113556855651 19433116734555170335283477)
                  ·
                    refine ⟨910927346932273609466413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19433116734555170335283477 910927346932273609466413)
                    ·
                      rfl

theorem cell22_2661037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_2661037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661037 prefixEnd_2661037 := by exact prefixLift 2661037
  have htrace : WordTrace (prefixWord ++ tailWord_2661037) baseStart_2661037 baseEnd_2661037 := by
    simpa [prefixWord, tailWord_2661037, baseEnd_2661037] using wordTrace_append hprefix tailTrace_2661037
  have hstable : (prefixWord ++ tailWord_2661037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661037).length < 2 ^ (prefixWord ++ tailWord_2661037).sum := by decide
  have hdescent : baseEnd_2661037 < baseStart_2661037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661101 : List Nat := [1, 5, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_2661101 : Nat := 118140960795 + 2661101 * 2 ^ 59
def prefixEnd_2661101 : Nat := 4983230072969 + 3 ^ 40 * 2661101 * 2
def baseEnd_2661101 : Nat := 910949255440198775866217

theorem tailTrace_2661101 : CollatzResearch.WordTrace tailWord_2661101 prefixEnd_2661101 910949255440198775866217 := by
  unfold tailWord_2661101
  simp only [CollatzResearch.WordTrace]
  refine ⟨97058327132293031712919157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64705551421528687808612771 97058327132293031712919157)
  ·
    refine ⟨9099218168652471723086171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97058327132293031712919157 9099218168652471723086171)
    ·
      refine ⟨13648827252978707584629257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9099218168652471723086171 13648827252978707584629257)
      ·
        refine ⟨10236620439734030688471943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13648827252978707584629257 10236620439734030688471943)
        ·
          refine ⟨15354930659601046032707915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10236620439734030688471943 15354930659601046032707915)
          ·
            refine ⟨23032395989401569049061873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15354930659601046032707915 23032395989401569049061873)
            ·
              refine ⟨17274296992051176786796405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23032395989401569049061873 17274296992051176786796405)
              ·
                refine ⟨1619465343004797823762163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17274296992051176786796405 1619465343004797823762163)
                ·
                  refine ⟨2429198014507196735643245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619465343004797823762163 2429198014507196735643245)
                  ·
                    refine ⟨910949255440198775866217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2429198014507196735643245 910949255440198775866217)
                    ·
                      rfl

theorem cell22_2661101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_2661101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661101 prefixEnd_2661101 := by exact prefixLift 2661101
  have htrace : WordTrace (prefixWord ++ tailWord_2661101) baseStart_2661101 baseEnd_2661101 := by
    simpa [prefixWord, tailWord_2661101, baseEnd_2661101] using wordTrace_append hprefix tailTrace_2661101
  have hstable : (prefixWord ++ tailWord_2661101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661101).length < 2 ^ (prefixWord ++ tailWord_2661101).sum := by decide
  have hdescent : baseEnd_2661101 < baseStart_2661101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661118 : List Nat := [4, 2, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_2661118 : Nat := 118140960795 + 2661118 * 2 ^ 59
def prefixEnd_2661118 : Nat := 4983230072969 + 3 ^ 40 * 2661118 * 2
def baseEnd_2661118 : Nat := 910955074887616398191165

theorem tailTrace_2661118 : CollatzResearch.WordTrace tailWord_2661118 prefixEnd_2661118 910955074887616398191165 := by
  unfold tailWord_2661118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12132368396653930452036001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64705964782154295744192005 12132368396653930452036001)
  ·
    refine ⟨9099276297490447839027001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12132368396653930452036001 9099276297490447839027001)
    ·
      refine ⟨6824457223117835879270251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9099276297490447839027001 6824457223117835879270251)
      ·
        refine ⟨10236685834676753818905377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6824457223117835879270251 10236685834676753818905377)
        ·
          refine ⟨7677514376007565364179033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10236685834676753818905377 7677514376007565364179033)
          ·
            refine ⟨5758135782005674023134275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7677514376007565364179033 5758135782005674023134275)
            ·
              refine ⟨8637203673008511034701413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5758135782005674023134275 8637203673008511034701413)
              ·
                refine ⟨1619475688689095819006515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8637203673008511034701413 1619475688689095819006515)
                ·
                  refine ⟨2429213533033643728509773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619475688689095819006515 2429213533033643728509773)
                  ·
                    refine ⟨910955074887616398191165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2429213533033643728509773 910955074887616398191165)
                    ·
                      rfl

theorem cell22_2661118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_2661118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661118 prefixEnd_2661118 := by exact prefixLift 2661118
  have htrace : WordTrace (prefixWord ++ tailWord_2661118) baseStart_2661118 baseEnd_2661118 := by
    simpa [prefixWord, tailWord_2661118, baseEnd_2661118] using wordTrace_append hprefix tailTrace_2661118
  have hstable : (prefixWord ++ tailWord_2661118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661118).length < 2 ^ (prefixWord ++ tailWord_2661118).sum := by decide
  have hdescent : baseEnd_2661118 < baseStart_2661118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661125 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 10]
def baseStart_2661125 : Nat := 118140960795 + 2661125 * 2 ^ 59
def prefixEnd_2661125 : Nat := 4983230072969 + 3 ^ 40 * 2661125 * 2
def baseEnd_2661125 : Nat := 303652490376890237755381

theorem tailTrace_2661125 : CollatzResearch.WordTrace tailWord_2661125 prefixEnd_2661125 303652490376890237755381 := by
  unfold tailWord_2661125
  simp only [CollatzResearch.WordTrace]
  refine ⟨97059202484206083811792829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64706134989470722541195219 97059202484206083811792829)
  ·
    refine ⟨36397200931577281429422311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97059202484206083811792829 36397200931577281429422311)
    ·
      refine ⟨54595801397365922144133467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36397200931577281429422311 54595801397365922144133467)
      ·
        refine ⟨81893702096048883216200201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54595801397365922144133467 81893702096048883216200201)
        ·
          refine ⟨61420276572036662412150151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81893702096048883216200201 61420276572036662412150151)
          ·
            refine ⟨92130414858054993618225227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61420276572036662412150151 92130414858054993618225227)
            ·
              refine ⟨138195622287082490427337841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92130414858054993618225227 138195622287082490427337841)
              ·
                refine ⟨103646716715311867820503381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138195622287082490427337841 103646716715311867820503381)
                ·
                  refine ⟨303652490376890237755381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 103646716715311867820503381 303652490376890237755381)
                  ·
                    rfl

theorem cell22_2661125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_2661125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661125 prefixEnd_2661125 := by exact prefixLift 2661125
  have htrace : WordTrace (prefixWord ++ tailWord_2661125) baseStart_2661125 baseEnd_2661125 := by
    simpa [prefixWord, tailWord_2661125, baseEnd_2661125] using wordTrace_append hprefix tailTrace_2661125
  have hstable : (prefixWord ++ tailWord_2661125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661125).length < 2 ^ (prefixWord ++ tailWord_2661125).sum := by decide
  have hdescent : baseEnd_2661125 < baseStart_2661125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661157 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_2661157 : Nat := 118140960795 + 2661157 * 2 ^ 59
def prefixEnd_2661157 : Nat := 4983230072969 + 3 ^ 40 * 2661157 * 2
def baseEnd_2661157 : Nat := 910968425384633296466045

theorem tailTrace_2661157 : CollatzResearch.WordTrace tailWord_2661157 prefixEnd_2661157 910968425384633296466045 := by
  unfold tailWord_2661157
  simp only [CollatzResearch.WordTrace]
  refine ⟨97060369620090153276957725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64706913080060102184638483 97060369620090153276957725)
  ·
    refine ⟨36397638607533807478859147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97060369620090153276957725 36397638607533807478859147)
    ·
      refine ⟨54596457911300711218288721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36397638607533807478859147 54596457911300711218288721)
      ·
        refine ⟨40947343433475533413716541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54596457911300711218288721 40947343433475533413716541)
        ·
          refine ⟨15355253787553325030143703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40947343433475533413716541 15355253787553325030143703)
          ·
            refine ⟨23032880681329987545215555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15355253787553325030143703 23032880681329987545215555)
            ·
              refine ⟨34549321021994981317823333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23032880681329987545215555 34549321021994981317823333)
              ·
                refine ⟨6477997691624058997091875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34549321021994981317823333 6477997691624058997091875)
                ·
                  refine ⟨9716996537436088495637813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6477997691624058997091875 9716996537436088495637813)
                  ·
                    refine ⟨910968425384633296466045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9716996537436088495637813 910968425384633296466045)
                    ·
                      rfl

theorem cell22_2661157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_2661157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661157 prefixEnd_2661157 := by exact prefixLift 2661157
  have htrace : WordTrace (prefixWord ++ tailWord_2661157) baseStart_2661157 baseEnd_2661157 := by
    simpa [prefixWord, tailWord_2661157, baseEnd_2661157] using wordTrace_append hprefix tailTrace_2661157
  have hstable : (prefixWord ++ tailWord_2661157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661157).length < 2 ^ (prefixWord ++ tailWord_2661157).sum := by decide
  have hdescent : baseEnd_2661157 < baseStart_2661157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661165 : List Nat := [1, 5, 3, 2, 2, 1, 1, 2, 5]
def baseStart_2661165 : Nat := 118140960795 + 2661165 * 2 ^ 59
def prefixEnd_2661165 : Nat := 4983230072969 + 3 ^ 40 * 2661165 * 2
def baseEnd_2661165 : Nat := 303657054649374647422007

theorem tailTrace_2661165 : CollatzResearch.WordTrace tailWord_2661165 prefixEnd_2661165 303657054649374647422007 := by
  unfold tailWord_2661165
  simp only [CollatzResearch.WordTrace]
  refine ⟨97060661404061170643248949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64707107602707447095499299 97060661404061170643248949)
  ·
    refine ⟨9099437006630734747804589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97060661404061170643248949 9099437006630734747804589)
    ·
      refine ⟨3412288877486525530426721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9099437006630734747804589 3412288877486525530426721)
      ·
        refine ⟨2559216658114894147820041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3412288877486525530426721 2559216658114894147820041)
        ·
          refine ⟨1919412493586170610865031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2559216658114894147820041 1919412493586170610865031)
          ·
            refine ⟨2879118740379255916297547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919412493586170610865031 2879118740379255916297547)
            ·
              refine ⟨4318678110568883874446321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879118740379255916297547 4318678110568883874446321)
              ·
                refine ⟨3239008582926662905834741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4318678110568883874446321 3239008582926662905834741)
                ·
                  refine ⟨303657054649374647422007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3239008582926662905834741 303657054649374647422007)
                  ·
                    rfl

theorem cell22_2661165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_2661165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661165 prefixEnd_2661165 := by exact prefixLift 2661165
  have htrace : WordTrace (prefixWord ++ tailWord_2661165) baseStart_2661165 baseEnd_2661165 := by
    simpa [prefixWord, tailWord_2661165, baseEnd_2661165] using wordTrace_append hprefix tailTrace_2661165
  have hstable : (prefixWord ++ tailWord_2661165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661165).length < 2 ^ (prefixWord ++ tailWord_2661165).sum := by decide
  have hdescent : baseEnd_2661165 < baseStart_2661165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661202 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_2661202 : Nat := 118140960795 + 2661202 * 2 ^ 59
def prefixEnd_2661202 : Nat := 4983230072969 + 3 ^ 40 * 2661202 * 2
def baseEnd_2661202 : Nat := 910983829804268179090907

theorem tailTrace_2661202 : CollatzResearch.WordTrace tailWord_2661202 prefixEnd_2661202 910983829804268179090907 := by
  unfold tailWord_2661202
  simp only [CollatzResearch.WordTrace]
  refine ⟨24265502726231781490586465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64708007269951417308230573 24265502726231781490586465)
  ·
    refine ⟨18199127044673836117939849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24265502726231781490586465 18199127044673836117939849)
    ·
      refine ⟨13649345283505377088454887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18199127044673836117939849 13649345283505377088454887)
      ·
        refine ⟨20474017925258065632682331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13649345283505377088454887 20474017925258065632682331)
        ·
          refine ⟨30711026887887098449023497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20474017925258065632682331 30711026887887098449023497)
          ·
            refine ⟨23033270165915323836767623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30711026887887098449023497 23033270165915323836767623)
            ·
              refine ⟨34549905248872985755151435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23033270165915323836767623 34549905248872985755151435)
              ·
                refine ⟨51824857873309478632727153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34549905248872985755151435 51824857873309478632727153)
                ·
                  refine ⟨38868643404982108974545365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51824857873309478632727153 38868643404982108974545365)
                  ·
                    refine ⟨910983829804268179090907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38868643404982108974545365 910983829804268179090907)
                    ·
                      rfl

theorem cell22_2661202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_2661202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661202 prefixEnd_2661202 := by exact prefixLift 2661202
  have htrace : WordTrace (prefixWord ++ tailWord_2661202) baseStart_2661202 baseEnd_2661202 := by
    simpa [prefixWord, tailWord_2661202, baseEnd_2661202] using wordTrace_append hprefix tailTrace_2661202
  have hstable : (prefixWord ++ tailWord_2661202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661202).length < 2 ^ (prefixWord ++ tailWord_2661202).sum := by decide
  have hdescent : baseEnd_2661202 < baseStart_2661202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661204 : List Nat := [2, 4, 1, 1, 4, 1, 1, 8]
def baseStart_2661204 : Nat := 118140960795 + 2661204 * 2 ^ 59
def prefixEnd_2661204 : Nat := 4983230072969 + 3 ^ 40 * 2661204 * 2
def baseEnd_2661204 : Nat := 101220501605015648948989

theorem tailTrace_2661204 : CollatzResearch.WordTrace tailWord_2661204 prefixEnd_2661204 101220501605015648948989 := by
  unfold tailWord_2661204
  simp only [CollatzResearch.WordTrace]
  refine ⟨48531041925459940151959333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64708055900613253535945777 48531041925459940151959333)
  ·
    refine ⟨9099570361023738778492375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48531041925459940151959333 9099570361023738778492375)
    ·
      refine ⟨13649355541535608167738563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9099570361023738778492375 13649355541535608167738563)
      ·
        refine ⟨20474033312303412251607845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13649355541535608167738563 20474033312303412251607845)
        ·
          refine ⟨3838881246056889797176471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20474033312303412251607845 3838881246056889797176471)
          ·
            refine ⟨5758321869085334695764707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3838881246056889797176471 5758321869085334695764707)
            ·
              refine ⟨8637482803628002043647061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5758321869085334695764707 8637482803628002043647061)
              ·
                refine ⟨101220501605015648948989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8637482803628002043647061 101220501605015648948989)
                ·
                  rfl

theorem cell22_2661204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 8].length) (baseStart_2661204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661204 prefixEnd_2661204 := by exact prefixLift 2661204
  have htrace : WordTrace (prefixWord ++ tailWord_2661204) baseStart_2661204 baseEnd_2661204 := by
    simpa [prefixWord, tailWord_2661204, baseEnd_2661204] using wordTrace_append hprefix tailTrace_2661204
  have hstable : (prefixWord ++ tailWord_2661204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661204).length < 2 ^ (prefixWord ++ tailWord_2661204).sum := by decide
  have hdescent : baseEnd_2661204 < baseStart_2661204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661232 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 7]
def baseStart_2661232 : Nat := 118140960795 + 2661232 * 2 ^ 59
def prefixEnd_2661232 : Nat := 4983230072969 + 3 ^ 40 * 2661232 * 2
def baseEnd_2661232 : Nat := 303664699805786033613605

theorem tailTrace_2661232 : CollatzResearch.WordTrace tailWord_2661232 prefixEnd_2661232 303664699805786033613605 := by
  unfold tailWord_2661232
  simp only [CollatzResearch.WordTrace]
  refine ⟨48531552547409220542968975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64708736729878960723958633 48531552547409220542968975)
  ·
    refine ⟨72797328821113830814453463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48531552547409220542968975 72797328821113830814453463)
    ·
      refine ⟨109195993231670746221680195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72797328821113830814453463 109195993231670746221680195)
      ·
        refine ⟨163793989847506119332520293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109195993231670746221680195 163793989847506119332520293)
        ·
          refine ⟨30711373096407397374847555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163793989847506119332520293 30711373096407397374847555)
          ·
            refine ⟨46067059644611096062271333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30711373096407397374847555 46067059644611096062271333)
            ·
              refine ⟨8637573683364580511675875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46067059644611096062271333 8637573683364580511675875)
              ·
                refine ⟨12956360525046870767513813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8637573683364580511675875 12956360525046870767513813)
                ·
                  refine ⟨303664699805786033613605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12956360525046870767513813 303664699805786033613605)
                  ·
                    rfl

theorem cell22_2661232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 7].length) (baseStart_2661232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661232 prefixEnd_2661232 := by exact prefixLift 2661232
  have htrace : WordTrace (prefixWord ++ tailWord_2661232) baseStart_2661232 baseEnd_2661232 := by
    simpa [prefixWord, tailWord_2661232, baseEnd_2661232] using wordTrace_append hprefix tailTrace_2661232
  have hstable : (prefixWord ++ tailWord_2661232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661232).length < 2 ^ (prefixWord ++ tailWord_2661232).sum := by decide
  have hdescent : baseEnd_2661232 < baseStart_2661232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661247 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 2, 5]
def baseStart_2661247 : Nat := 118140960795 + 2661247 * 2 ^ 59
def prefixEnd_2661247 : Nat := 4983230072969 + 3 ^ 40 * 2661247 * 2
def baseEnd_2661247 : Nat := 910999234223903061715769

theorem tailTrace_2661247 : CollatzResearch.WordTrace tailWord_2661247 prefixEnd_2661247 910999234223903061715769 := by
  unfold tailWord_2661247
  simp only [CollatzResearch.WordTrace]
  refine ⟨97063652189764098647733995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64709101459842732431822663 97063652189764098647733995)
  ·
    refine ⟨145595478284646147971600993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97063652189764098647733995 145595478284646147971600993)
    ·
      refine ⟨109196608713484610978700745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145595478284646147971600993 109196608713484610978700745)
      ·
        refine ⟨81897456535113458234025559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109196608713484610978700745 81897456535113458234025559)
        ·
          refine ⟨122846184802670187351038339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81897456535113458234025559 122846184802670187351038339)
          ·
            refine ⟨184269277204005281026557509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122846184802670187351038339 184269277204005281026557509)
            ·
              refine ⟨34550489475750990192479533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184269277204005281026557509 34550489475750990192479533)
              ·
                refine ⟨12956433553406621322179825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34550489475750990192479533 12956433553406621322179825)
                ·
                  refine ⟨9717325165054965991634869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12956433553406621322179825 9717325165054965991634869)
                  ·
                    refine ⟨910999234223903061715769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9717325165054965991634869 910999234223903061715769)
                    ·
                      rfl

theorem cell22_2661247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_2661247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661247 prefixEnd_2661247 := by exact prefixLift 2661247
  have htrace : WordTrace (prefixWord ++ tailWord_2661247) baseStart_2661247 baseEnd_2661247 := by
    simpa [prefixWord, tailWord_2661247, baseEnd_2661247] using wordTrace_append hprefix tailTrace_2661247
  have hstable : (prefixWord ++ tailWord_2661247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661247).length < 2 ^ (prefixWord ++ tailWord_2661247).sum := by decide
  have hdescent : baseEnd_2661247 < baseStart_2661247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661287 : List Nat := [1, 1, 6, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2661287 : Nat := 118140960795 + 2661287 * 2 ^ 59
def prefixEnd_2661287 : Nat := 4983230072969 + 3 ^ 40 * 2661287 * 2
def baseEnd_2661287 : Nat := 911012927041356290715647

theorem tailTrace_2661287 : CollatzResearch.WordTrace tailWord_2661287 prefixEnd_2661287 911012927041356290715647 := by
  unfold tailWord_2661287
  simp only [CollatzResearch.WordTrace]
  refine ⟨97065111109619185479190115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64710074073079456986126743 97065111109619185479190115)
  ·
    refine ⟨145597666664428778218785173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97065111109619185479190115 145597666664428778218785173)
    ·
      refine ⟨6824890624895098979005555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 145597666664428778218785173 6824890624895098979005555)
      ·
        refine ⟨10237335937342648468508333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6824890624895098979005555 10237335937342648468508333)
        ·
          refine ⟨3839000976503493175690625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10237335937342648468508333 3839000976503493175690625)
          ·
            refine ⟨2879250732377619881767969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3839000976503493175690625 2879250732377619881767969)
            ·
              refine ⟨2159438049283214911325977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2879250732377619881767969 2159438049283214911325977)
              ·
                refine ⟨1619578536962411183494483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2159438049283214911325977 1619578536962411183494483)
                ·
                  refine ⟨2429367805443616775241725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619578536962411183494483 2429367805443616775241725)
                  ·
                    refine ⟨911012927041356290715647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2429367805443616775241725 911012927041356290715647)
                    ·
                      rfl

theorem cell22_2661287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2661287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661287 prefixEnd_2661287 := by exact prefixLift 2661287
  have htrace : WordTrace (prefixWord ++ tailWord_2661287) baseStart_2661287 baseEnd_2661287 := by
    simpa [prefixWord, tailWord_2661287, baseEnd_2661287] using wordTrace_append hprefix tailTrace_2661287
  have hstable : (prefixWord ++ tailWord_2661287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661287).length < 2 ^ (prefixWord ++ tailWord_2661287).sum := by decide
  have hdescent : baseEnd_2661287 < baseStart_2661287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661324 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_2661324 : Nat := 118140960795 + 2661324 * 2 ^ 59
def prefixEnd_2661324 : Nat := 4983230072969 + 3 ^ 40 * 2661324 * 2
def baseEnd_2661324 : Nat := 911025592897500527540533

theorem tailTrace_2661324 : CollatzResearch.WordTrace tailWord_2661324 prefixEnd_2661324 911025592897500527540533 := by
  unfold tailWord_2661324
  simp only [CollatzResearch.WordTrace]
  refine ⟨48533230305242570399143513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64710973740323427198858017 48533230305242570399143513)
  ·
    refine ⟨36399922728931927799357635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48533230305242570399143513 36399922728931927799357635)
    ·
      refine ⟨54599884093397891699036453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36399922728931927799357635 54599884093397891699036453)
      ·
        refine ⟨10237478267512104693569335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54599884093397891699036453 10237478267512104693569335)
        ·
          refine ⟨15356217401268157040354003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10237478267512104693569335 15356217401268157040354003)
          ·
            refine ⟨23034326101902235560531005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15356217401268157040354003 23034326101902235560531005)
            ·
              refine ⟨8637872288213338335199127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23034326101902235560531005 8637872288213338335199127)
              ·
                refine ⟨12956808432320007502798691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8637872288213338335199127 12956808432320007502798691)
                ·
                  refine ⟨19435212648480011254198037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12956808432320007502798691 19435212648480011254198037)
                  ·
                    refine ⟨911025592897500527540533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19435212648480011254198037 911025592897500527540533)
                    ·
                      rfl

theorem cell22_2661324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_2661324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661324 prefixEnd_2661324 := by exact prefixLift 2661324
  have htrace : WordTrace (prefixWord ++ tailWord_2661324) baseStart_2661324 baseEnd_2661324 := by
    simpa [prefixWord, tailWord_2661324, baseEnd_2661324] using wordTrace_append hprefix tailTrace_2661324
  have hstable : (prefixWord ++ tailWord_2661324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661324).length < 2 ^ (prefixWord ++ tailWord_2661324).sum := by decide
  have hdescent : baseEnd_2661324 < baseStart_2661324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661330 : List Nat := [3, 2, 2, 3, 1, 3, 2, 1, 1, 4]
def baseStart_2661330 : Nat := 118140960795 + 2661330 * 2 ^ 59
def prefixEnd_2661330 : Nat := 4983230072969 + 3 ^ 40 * 2661330 * 2
def baseEnd_2661330 : Nat := 911027646820118511890515

theorem tailTrace_2661330 : CollatzResearch.WordTrace tailWord_2661330 prefixEnd_2661330 911027646820118511890515 := by
  unfold tailWord_2661330
  simp only [CollatzResearch.WordTrace]
  refine ⟨24266669862115850955751361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64711119632308935882003629 24266669862115850955751361)
  ·
    refine ⟨18200002396586888216813521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24266669862115850955751361 18200002396586888216813521)
    ·
      refine ⟨13650001797440166162610141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18200002396586888216813521 13650001797440166162610141)
      ·
        refine ⟨5118750674040062310978803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13650001797440166162610141 5118750674040062310978803)
        ·
          refine ⟨7678126011060093466468205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5118750674040062310978803 7678126011060093466468205)
          ·
            refine ⟨2879297254147535049925577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7678126011060093466468205 2879297254147535049925577)
            ·
              refine ⟨2159472940610651287444183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2879297254147535049925577 2159472940610651287444183)
              ·
                refine ⟨3239209410915976931166275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159472940610651287444183 3239209410915976931166275)
                ·
                  refine ⟨4858814116373965396749413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3239209410915976931166275 4858814116373965396749413)
                  ·
                    refine ⟨911027646820118511890515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4858814116373965396749413 911027646820118511890515)
                    ·
                      rfl

theorem cell22_2661330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_2661330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661330 prefixEnd_2661330 := by exact prefixLift 2661330
  have htrace : WordTrace (prefixWord ++ tailWord_2661330) baseStart_2661330 baseEnd_2661330 := by
    simpa [prefixWord, tailWord_2661330, baseEnd_2661330] using wordTrace_append hprefix tailTrace_2661330
  have hstable : (prefixWord ++ tailWord_2661330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661330).length < 2 ^ (prefixWord ++ tailWord_2661330).sum := by decide
  have hdescent : baseEnd_2661330 < baseStart_2661330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661364 : List Nat := [2, 6, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2661364 : Nat := 118140960795 + 2661364 * 2 ^ 59
def prefixEnd_2661364 : Nat := 4983230072969 + 3 ^ 40 * 2661364 * 2
def baseEnd_2661364 : Nat := 911039285714953756540411

theorem tailTrace_2661364 : CollatzResearch.WordTrace tailWord_2661364 prefixEnd_2661364 911039285714953756540411 := by
  unfold tailWord_2661364
  simp only [CollatzResearch.WordTrace]
  refine ⟨48533959765170113814871573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64711946353560151753162097 48533959765170113814871573)
  ·
    refine ⟨2275029363992349085072105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48533959765170113814871573 2275029363992349085072105)
    ·
      refine ⟨1706272022994261813804079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2275029363992349085072105 1706272022994261813804079)
      ·
        refine ⟨2559408034491392720706119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1706272022994261813804079 2559408034491392720706119)
        ·
          refine ⟨3839112051737089081059179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2559408034491392720706119 3839112051737089081059179)
          ·
            refine ⟨5758668077605633621588769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3839112051737089081059179 5758668077605633621588769)
            ·
              refine ⟨4319001058204225216191577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5758668077605633621588769 4319001058204225216191577)
              ·
                refine ⟨3239250793653168912143683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4319001058204225216191577 3239250793653168912143683)
                ·
                  refine ⟨4858876190479753368215525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3239250793653168912143683 4858876190479753368215525)
                  ·
                    refine ⟨911039285714953756540411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4858876190479753368215525 911039285714953756540411)
                    ·
                      rfl

theorem cell22_2661364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2661364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661364 prefixEnd_2661364 := by exact prefixLift 2661364
  have htrace : WordTrace (prefixWord ++ tailWord_2661364) baseStart_2661364 baseEnd_2661364 := by
    simpa [prefixWord, tailWord_2661364, baseEnd_2661364] using wordTrace_append hprefix tailTrace_2661364
  have hstable : (prefixWord ++ tailWord_2661364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661364).length < 2 ^ (prefixWord ++ tailWord_2661364).sum := by decide
  have hdescent : baseEnd_2661364 < baseStart_2661364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661384 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 7]
def baseStart_2661384 : Nat := 118140960795 + 2661384 * 2 ^ 59
def prefixEnd_2661384 : Nat := 4983230072969 + 3 ^ 40 * 2661384 * 2
def baseEnd_2661384 : Nat := 303682044041226790346783

theorem tailTrace_2661384 : CollatzResearch.WordTrace tailWord_2661384 prefixEnd_2661384 303682044041226790346783 := by
  unfold tailWord_2661384
  simp only [CollatzResearch.WordTrace]
  refine ⟨48534324495133885522735603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64712432660178514030314137 48534324495133885522735603)
  ·
    refine ⟨72801486742700828284103405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48534324495133885522735603 72801486742700828284103405)
    ·
      refine ⟨27300557528512810606538777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72801486742700828284103405 27300557528512810606538777)
      ·
        refine ⟨20475418146384607954904083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27300557528512810606538777 20475418146384607954904083)
        ·
          refine ⟨30713127219576911932356125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20475418146384607954904083 30713127219576911932356125)
          ·
            refine ⟨11517422707341341974633547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30713127219576911932356125 11517422707341341974633547)
            ·
              refine ⟨17276134061012012961950321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11517422707341341974633547 17276134061012012961950321)
              ·
                refine ⟨12957100545759009721462741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17276134061012012961950321 12957100545759009721462741)
                ·
                  refine ⟨303682044041226790346783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12957100545759009721462741 303682044041226790346783)
                  ·
                    rfl

theorem cell22_2661384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_2661384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661384 prefixEnd_2661384 := by exact prefixLift 2661384
  have htrace : WordTrace (prefixWord ++ tailWord_2661384) baseStart_2661384 baseEnd_2661384 := by
    simpa [prefixWord, tailWord_2661384, baseEnd_2661384] using wordTrace_append hprefix tailTrace_2661384
  have hstable : (prefixWord ++ tailWord_2661384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661384).length < 2 ^ (prefixWord ++ tailWord_2661384).sum := by decide
  have hdescent : baseEnd_2661384 < baseStart_2661384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661405 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_2661405 : Nat := 118140960795 + 2661405 * 2 ^ 59
def prefixEnd_2661405 : Nat := 4983230072969 + 3 ^ 40 * 2661405 * 2
def baseEnd_2661405 : Nat := 911053320852843316265285

theorem tailTrace_2661405 : CollatzResearch.WordTrace tailWord_2661405 prefixEnd_2661405 911053320852843316265285 := by
  unfold tailWord_2661405
  simp only [CollatzResearch.WordTrace]
  refine ⟨97069414923191691631985669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64712943282127794421323779 97069414923191691631985669)
  ·
    refine ⟨18200515298098442180997313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97069414923191691631985669 18200515298098442180997313)
    ·
      refine ⟨13650386473573831635747985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18200515298098442180997313 13650386473573831635747985)
      ·
        refine ⟨10237789855180373726810989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13650386473573831635747985 10237789855180373726810989)
        ·
          refine ⟨3839171195692640147554121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10237789855180373726810989 3839171195692640147554121)
          ·
            refine ⟨2879378396769480110665591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3839171195692640147554121 2879378396769480110665591)
            ·
              refine ⟨4319067595154220165998387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879378396769480110665591 4319067595154220165998387)
              ·
                refine ⟨6478601392731330248997581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4319067595154220165998387 6478601392731330248997581)
                ·
                  refine ⟨2429475522274248843374093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6478601392731330248997581 2429475522274248843374093)
                  ·
                    refine ⟨911053320852843316265285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2429475522274248843374093 911053320852843316265285)
                    ·
                      rfl

theorem cell22_2661405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_2661405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661405 prefixEnd_2661405 := by exact prefixLift 2661405
  have htrace : WordTrace (prefixWord ++ tailWord_2661405) baseStart_2661405 baseEnd_2661405 := by
    simpa [prefixWord, tailWord_2661405, baseEnd_2661405] using wordTrace_append hprefix tailTrace_2661405
  have hstable : (prefixWord ++ tailWord_2661405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661405).length < 2 ^ (prefixWord ++ tailWord_2661405).sum := by decide
  have hdescent : baseEnd_2661405 < baseStart_2661405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661418 : List Nat := [3, 1, 4, 1, 3, 1, 1, 3, 5]
def baseStart_2661418 : Nat := 118140960795 + 2661418 * 2 ^ 59
def prefixEnd_2661418 : Nat := 4983230072969 + 3 ^ 40 * 2661418 * 2
def baseEnd_2661418 : Nat := 303685923672838538563415

theorem tailTrace_2661418 : CollatzResearch.WordTrace tailWord_2661418 prefixEnd_2661418 303685923672838538563415 := by
  unfold tailWord_2661418
  simp only [CollatzResearch.WordTrace]
  refine ⟨24267472268036148713052227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64713259381429729901472605 24267472268036148713052227)
  ·
    refine ⟨36401208402054223069578341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24267472268036148713052227 36401208402054223069578341)
    ·
      refine ⟨6825226575385166825545939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36401208402054223069578341 6825226575385166825545939)
      ·
        refine ⟨10237839863077750238318909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6825226575385166825545939 10237839863077750238318909)
        ·
          refine ⟨3839189948654156339369591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10237839863077750238318909 3839189948654156339369591)
          ·
            refine ⟨5758784922981234509054387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3839189948654156339369591 5758784922981234509054387)
            ·
              refine ⟨8638177384471851763581581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5758784922981234509054387 8638177384471851763581581)
              ·
                refine ⟨3239316519176944411343093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8638177384471851763581581 3239316519176944411343093)
                ·
                  refine ⟨303685923672838538563415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3239316519176944411343093 303685923672838538563415)
                  ·
                    rfl

theorem cell22_2661418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_2661418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661418 prefixEnd_2661418 := by exact prefixLift 2661418
  have htrace : WordTrace (prefixWord ++ tailWord_2661418) baseStart_2661418 baseEnd_2661418 := by
    simpa [prefixWord, tailWord_2661418, baseEnd_2661418] using wordTrace_append hprefix tailTrace_2661418
  have hstable : (prefixWord ++ tailWord_2661418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661418).length < 2 ^ (prefixWord ++ tailWord_2661418).sum := by decide
  have hdescent : baseEnd_2661418 < baseStart_2661418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661429 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 8]
def baseStart_2661429 : Nat := 118140960795 + 2661429 * 2 ^ 59
def prefixEnd_2661429 : Nat := 4983230072969 + 3 ^ 40 * 2661429 * 2
def baseEnd_2661429 : Nat := 303687178847771751221737

theorem tailTrace_2661429 : CollatzResearch.WordTrace tailWord_2661429 prefixEnd_2661429 303687178847771751221737 := by
  unfold tailWord_2661429
  simp only [CollatzResearch.WordTrace]
  refine ⟨97070290275104743730859341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64713526850069829153906227 97070290275104743730859341)
  ·
    refine ⟨36401358853164278899072253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97070290275104743730859341 36401358853164278899072253)
    ·
      refine ⟨13650509569936604587152095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36401358853164278899072253 13650509569936604587152095)
      ·
        refine ⟨20475764354904906880728143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13650509569936604587152095 20475764354904906880728143)
        ·
          refine ⟨30713646532357360321092215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20475764354904906880728143 30713646532357360321092215)
          ·
            refine ⟨46070469798536040481638323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30713646532357360321092215 46070469798536040481638323)
            ·
              refine ⟨69105704697804060722457485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46070469798536040481638323 69105704697804060722457485)
              ·
                refine ⟨25914639261676522770921557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69105704697804060722457485 25914639261676522770921557)
                ·
                  refine ⟨303687178847771751221737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25914639261676522770921557 303687178847771751221737)
                  ·
                    rfl

theorem cell22_2661429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_2661429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661429 prefixEnd_2661429 := by exact prefixLift 2661429
  have htrace : WordTrace (prefixWord ++ tailWord_2661429) baseStart_2661429 baseEnd_2661429 := by
    simpa [prefixWord, tailWord_2661429, baseEnd_2661429] using wordTrace_append hprefix tailTrace_2661429
  have hstable : (prefixWord ++ tailWord_2661429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661429).length < 2 ^ (prefixWord ++ tailWord_2661429).sum := by decide
  have hdescent : baseEnd_2661429 < baseStart_2661429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661448 : List Nat := [2, 1, 3, 1, 1, 1, 7, 1, 1, 4]
def baseStart_2661448 : Nat := 118140960795 + 2661448 * 2 ^ 59
def prefixEnd_2661448 : Nat := 4983230072969 + 3 ^ 40 * 2661448 * 2
def baseEnd_2661448 : Nat := 911068040631605537440153

theorem tailTrace_2661448 : CollatzResearch.WordTrace tailWord_2661448 prefixEnd_2661448 911068040631605537440153 := by
  unfold tailWord_2661448
  simp only [CollatzResearch.WordTrace]
  refine ⟨48535491631017954987900499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64713988841357273317200665 48535491631017954987900499)
  ·
    refine ⟨72803237446526932481850749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48535491631017954987900499 72803237446526932481850749)
    ·
      refine ⟨27301214042447599680694031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72803237446526932481850749 27301214042447599680694031)
      ·
        refine ⟨40951821063671399521041047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27301214042447599680694031 40951821063671399521041047)
        ·
          refine ⟨61427731595507099281561571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40951821063671399521041047 61427731595507099281561571)
          ·
            refine ⟨92141597393260648922342357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61427731595507099281561571 92141597393260648922342357)
            ·
              refine ⟨2159568688904546459117399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 92141597393260648922342357 2159568688904546459117399)
              ·
                refine ⟨3239353033356819688676099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159568688904546459117399 3239353033356819688676099)
                ·
                  refine ⟨4859029550035229533014149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3239353033356819688676099 4859029550035229533014149)
                  ·
                    refine ⟨911068040631605537440153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4859029550035229533014149 911068040631605537440153)
                    ·
                      rfl

theorem cell22_2661448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_2661448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661448 prefixEnd_2661448 := by exact prefixLift 2661448
  have htrace : WordTrace (prefixWord ++ tailWord_2661448) baseStart_2661448 baseEnd_2661448 := by
    simpa [prefixWord, tailWord_2661448, baseEnd_2661448] using wordTrace_append hprefix tailTrace_2661448
  have hstable : (prefixWord ++ tailWord_2661448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661448).length < 2 ^ (prefixWord ++ tailWord_2661448).sum := by decide
  have hdescent : baseEnd_2661448 < baseStart_2661448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661489 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 1, 9]
def baseStart_2661489 : Nat := 118140960795 + 2661489 * 2 ^ 59
def prefixEnd_2661489 : Nat := 4983230072969 + 3 ^ 40 * 2661489 * 2
def baseEnd_2661489 : Nat := 911082075769495097165027

theorem tailTrace_2661489 : CollatzResearch.WordTrace tailWord_2661489 prefixEnd_2661489 911082075769495097165027 := by
  unfold tailWord_2661489
  simp only [CollatzResearch.WordTrace]
  refine ⟨97072478654887373978043521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64714985769924915985362347 97072478654887373978043521)
  ·
    refine ⟨72804358991165530483532641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97072478654887373978043521 72804358991165530483532641)
    ·
      refine ⟨54603269243374147862649481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72804358991165530483532641 54603269243374147862649481)
      ·
        refine ⟨40952451932530610896987111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54603269243374147862649481 40952451932530610896987111)
        ·
          refine ⟨61428677898795916345480667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40952451932530610896987111 61428677898795916345480667)
          ·
            refine ⟨92143016848193874518221001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61428677898795916345480667 92143016848193874518221001)
            ·
              refine ⟨69107262636145405888665751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92143016848193874518221001 69107262636145405888665751)
              ·
                refine ⟨103660893954218108832998627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69107262636145405888665751 103660893954218108832998627)
                ·
                  refine ⟨155491340931327163249497941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103660893954218108832998627 155491340931327163249497941)
                  ·
                    refine ⟨911082075769495097165027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 155491340931327163249497941 911082075769495097165027)
                    ·
                      rfl

theorem cell22_2661489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_2661489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661489 prefixEnd_2661489 := by exact prefixLift 2661489
  have htrace : WordTrace (prefixWord ++ tailWord_2661489) baseStart_2661489 baseEnd_2661489 := by
    simpa [prefixWord, tailWord_2661489, baseEnd_2661489] using wordTrace_append hprefix tailTrace_2661489
  have hstable : (prefixWord ++ tailWord_2661489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661489).length < 2 ^ (prefixWord ++ tailWord_2661489).sum := by decide
  have hdescent : baseEnd_2661489 < baseStart_2661489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661512 : List Nat := [2, 1, 3, 4, 2, 2, 1, 2, 2, 3]
def baseStart_2661512 : Nat := 118140960795 + 2661512 * 2 ^ 59
def prefixEnd_2661512 : Nat := 4983230072969 + 3 ^ 40 * 2661512 * 2
def baseEnd_2661512 : Nat := 911089949139530703839957

theorem tailTrace_2661512 : CollatzResearch.WordTrace tailWord_2661512 prefixEnd_2661512 911089949139530703839957 := by
  unfold tailWord_2661512
  simp only [CollatzResearch.WordTrace]
  refine ⟨48536658766902024453065395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64715545022536032604087193 48536658766902024453065395)
  ·
    refine ⟨72804988150353036679598093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48536658766902024453065395 72804988150353036679598093)
    ·
      refine ⟨27301870556382388754849285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72804988150353036679598093 27301870556382388754849285)
      ·
        refine ⟨5119100729321697891534241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27301870556382388754849285 5119100729321697891534241)
        ·
          refine ⟨3839325546991273418650681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5119100729321697891534241 3839325546991273418650681)
          ·
            refine ⟨2879494160243455063988011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3839325546991273418650681 2879494160243455063988011)
            ·
              refine ⟨4319241240365182595982017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879494160243455063988011 4319241240365182595982017)
              ·
                refine ⟨3239430930273886946986513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4319241240365182595982017 3239430930273886946986513)
                ·
                  refine ⟨2429573197705415210239885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3239430930273886946986513 2429573197705415210239885)
                  ·
                    refine ⟨911089949139530703839957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2429573197705415210239885 911089949139530703839957)
                    ·
                      rfl

theorem cell22_2661512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_2661512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661512 prefixEnd_2661512 := by exact prefixLift 2661512
  have htrace : WordTrace (prefixWord ++ tailWord_2661512) baseStart_2661512 baseEnd_2661512 := by
    simpa [prefixWord, tailWord_2661512, baseEnd_2661512] using wordTrace_append hprefix tailTrace_2661512
  have hstable : (prefixWord ++ tailWord_2661512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661512).length < 2 ^ (prefixWord ++ tailWord_2661512).sum := by decide
  have hdescent : baseEnd_2661512 < baseStart_2661512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661600 : List Nat := [2, 1, 1, 3, 1, 6, 1, 2, 1, 4]
def baseStart_2661600 : Nat := 118140960795 + 2661600 * 2 ^ 59
def prefixEnd_2661600 : Nat := 4983230072969 + 3 ^ 40 * 2661600 * 2
def baseEnd_2661600 : Nat := 911120073337927807639687

theorem tailTrace_2661600 : CollatzResearch.WordTrace tailWord_2661600 prefixEnd_2661600 911120073337927807639687 := by
  unfold tailWord_2661600
  simp only [CollatzResearch.WordTrace]
  refine ⟨48538263578742619967667127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64717684771656826623556169 48538263578742619967667127)
  ·
    refine ⟨72807395368113929951500691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48538263578742619967667127 72807395368113929951500691)
    ·
      refine ⟨109211093052170894927251037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72807395368113929951500691 109211093052170894927251037)
      ·
        refine ⟨40954159894564085597719139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109211093052170894927251037 40954159894564085597719139)
        ·
          refine ⟨61431239841846128396578709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40954159894564085597719139 61431239841846128396578709)
          ·
            refine ⟨2879589367586537268589627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61431239841846128396578709 2879589367586537268589627)
            ·
              refine ⟨4319384051379805902884441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879589367586537268589627 4319384051379805902884441)
              ·
                refine ⟨3239538038534854427163331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4319384051379805902884441 3239538038534854427163331)
                ·
                  refine ⟨4859307057802281640744997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3239538038534854427163331 4859307057802281640744997)
                  ·
                    refine ⟨911120073337927807639687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4859307057802281640744997 911120073337927807639687)
                    ·
                      rfl

theorem cell22_2661600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 1, 4].length) (baseStart_2661600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661600 prefixEnd_2661600 := by exact prefixLift 2661600
  have htrace : WordTrace (prefixWord ++ tailWord_2661600) baseStart_2661600 baseEnd_2661600 := by
    simpa [prefixWord, tailWord_2661600, baseEnd_2661600] using wordTrace_append hprefix tailTrace_2661600
  have hstable : (prefixWord ++ tailWord_2661600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661600).length < 2 ^ (prefixWord ++ tailWord_2661600).sum := by decide
  have hdescent : baseEnd_2661600 < baseStart_2661600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661613 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_2661613 : Nat := 118140960795 + 2661613 * 2 ^ 59
def prefixEnd_2661613 : Nat := 4983230072969 + 3 ^ 40 * 2661613 * 2
def baseEnd_2661613 : Nat := 911124523503600107064647

theorem tailTrace_2661613 : CollatzResearch.WordTrace tailWord_2661613 prefixEnd_2661613 911124523503600107064647 := by
  unfold tailWord_2661613
  simp only [CollatzResearch.WordTrace]
  refine ⟨97077001306438143155557493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64718000870958762103704995 97077001306438143155557493)
  ·
    refine ⟨9100968872478575920833515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97077001306438143155557493 9100968872478575920833515)
    ·
      refine ⟨13651453308717863881250273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9100968872478575920833515 13651453308717863881250273)
      ·
        refine ⟨10238589981538397910937705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13651453308717863881250273 10238589981538397910937705)
        ·
          refine ⟨7678942486153798433203279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10238589981538397910937705 7678942486153798433203279)
          ·
            refine ⟨11518413729230697649804919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7678942486153798433203279 11518413729230697649804919)
            ·
              refine ⟨17277620593846046474707379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11518413729230697649804919 17277620593846046474707379)
              ·
                refine ⟨25916430890769069712061069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17277620593846046474707379 25916430890769069712061069)
                ·
                  refine ⟨9718661584038401142022901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25916430890769069712061069 9718661584038401142022901)
                  ·
                    refine ⟨911124523503600107064647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9718661584038401142022901 911124523503600107064647)
                    ·
                      rfl

theorem cell22_2661613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_2661613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661613 prefixEnd_2661613 := by exact prefixLift 2661613
  have htrace : WordTrace (prefixWord ++ tailWord_2661613) baseStart_2661613 baseEnd_2661613 := by
    simpa [prefixWord, tailWord_2661613, baseEnd_2661613] using wordTrace_append hprefix tailTrace_2661613
  have hstable : (prefixWord ++ tailWord_2661613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661613).length < 2 ^ (prefixWord ++ tailWord_2661613).sum := by decide
  have hdescent : baseEnd_2661613 < baseStart_2661613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661643 : List Nat := [1, 1, 1, 1, 5, 5, 1, 7]
def baseStart_2661643 : Nat := 118140960795 + 2661643 * 2 ^ 59
def prefixEnd_2661643 : Nat := 4983230072969 + 3 ^ 40 * 2661643 * 2
def baseEnd_2661643 : Nat := 101237199235187780979395

theorem tailTrace_2661643 : CollatzResearch.WordTrace tailWord_2661643 prefixEnd_2661643 101237199235187780979395 := by
  unfold tailWord_2661643
  simp only [CollatzResearch.WordTrace]
  refine ⟨97078095496329458279149583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64718730330886305519433055 97078095496329458279149583)
  ·
    refine ⟨145617143244494187418724375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97078095496329458279149583 145617143244494187418724375)
    ·
      refine ⟨218425714866741281128086563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145617143244494187418724375 218425714866741281128086563)
      ·
        refine ⟨327638572300111921692129845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218425714866741281128086563 327638572300111921692129845)
        ·
          refine ⟨30716116153135492658637173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 327638572300111921692129845 30716116153135492658637173)
          ·
            refine ⟨2879635889356452436747235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30716116153135492658637173 2879635889356452436747235)
            ·
              refine ⟨4319453834034678655120853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879635889356452436747235 4319453834034678655120853)
              ·
                refine ⟨101237199235187780979395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4319453834034678655120853 101237199235187780979395)
                ·
                  rfl

theorem cell22_2661643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 7].length) (baseStart_2661643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661643 prefixEnd_2661643 := by exact prefixLift 2661643
  have htrace : WordTrace (prefixWord ++ tailWord_2661643) baseStart_2661643 baseEnd_2661643 := by
    simpa [prefixWord, tailWord_2661643, baseEnd_2661643] using wordTrace_append hprefix tailTrace_2661643
  have hstable : (prefixWord ++ tailWord_2661643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661643).length < 2 ^ (prefixWord ++ tailWord_2661643).sum := by decide
  have hdescent : baseEnd_2661643 < baseStart_2661643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661662 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2661662 : Nat := 118140960795 + 2661662 * 2 ^ 59
def prefixEnd_2661662 : Nat := 4983230072969 + 3 ^ 40 * 2661662 * 2
def baseEnd_2661662 : Nat := 911141297204980312589497

theorem tailTrace_2661662 : CollatzResearch.WordTrace tailWord_2661662 prefixEnd_2661662 911141297204980312589497 := by
  unfold tailWord_2661662
  simp only [CollatzResearch.WordTrace]
  refine ⟨12134848560407578065511405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64719192322173749682727493 12134848560407578065511405)
  ·
    refine ⟨4550568210152841774566777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12134848560407578065511405 4550568210152841774566777)
    ·
      refine ⟨3412926157614631330925083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4550568210152841774566777 3412926157614631330925083)
      ·
        refine ⟨5119389236421946996387625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3412926157614631330925083 5119389236421946996387625)
        ·
          refine ⟨3839541927316460247290719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5119389236421946996387625 3839541927316460247290719)
          ·
            refine ⟨5759312890974690370936079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3839541927316460247290719 5759312890974690370936079)
            ·
              refine ⟨8638969336462035556404119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5759312890974690370936079 8638969336462035556404119)
              ·
                refine ⟨12958454004693053334606179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8638969336462035556404119 12958454004693053334606179)
                ·
                  refine ⟨19437681007039580001909269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12958454004693053334606179 19437681007039580001909269)
                  ·
                    refine ⟨911141297204980312589497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19437681007039580001909269 911141297204980312589497)
                    ·
                      rfl

theorem cell22_2661662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2661662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661662 prefixEnd_2661662 := by exact prefixLift 2661662
  have htrace : WordTrace (prefixWord ++ tailWord_2661662) baseStart_2661662 baseEnd_2661662 := by
    simpa [prefixWord, tailWord_2661662, baseEnd_2661662] using wordTrace_append hprefix tailTrace_2661662
  have hstable : (prefixWord ++ tailWord_2661662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661662).length < 2 ^ (prefixWord ++ tailWord_2661662).sum := by decide
  have hdescent : baseEnd_2661662 < baseStart_2661662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661692 : List Nat := [2, 2, 2, 2, 1, 3, 2, 4, 1, 3]
def baseStart_2661692 : Nat := 118140960795 + 2661692 * 2 ^ 59
def prefixEnd_2661692 : Nat := 4983230072969 + 3 ^ 40 * 2661692 * 2
def baseEnd_2661692 : Nat := 911151566818070234339405

theorem tailTrace_2661692 : CollatzResearch.WordTrace tailWord_2661692 prefixEnd_2661692 911151566818070234339405 := by
  unfold tailWord_2661692
  simp only [CollatzResearch.WordTrace]
  refine ⟨48539941336575969823841665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64719921782101293098455553 48539941336575969823841665)
  ·
    refine ⟨36404956002431977367881249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48539941336575969823841665 36404956002431977367881249)
    ·
      refine ⟨27303717001823983025910937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36404956002431977367881249 27303717001823983025910937)
      ·
        refine ⟨20477787751367987269433203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27303717001823983025910937 20477787751367987269433203)
        ·
          refine ⟨30716681627051980904149805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20477787751367987269433203 30716681627051980904149805)
          ·
            refine ⟨11518755610144492839056177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30716681627051980904149805 11518755610144492839056177)
            ·
              refine ⟨8639066707608369629292133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11518755610144492839056177 8639066707608369629292133)
              ·
                refine ⟨1619825007676569305492275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8639066707608369629292133 1619825007676569305492275)
                ·
                  refine ⟨2429737511514853958238413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619825007676569305492275 2429737511514853958238413)
                  ·
                    refine ⟨911151566818070234339405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2429737511514853958238413 911151566818070234339405)
                    ·
                      rfl

theorem cell22_2661692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_2661692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661692 prefixEnd_2661692 := by exact prefixLift 2661692
  have htrace : WordTrace (prefixWord ++ tailWord_2661692) baseStart_2661692 baseEnd_2661692 := by
    simpa [prefixWord, tailWord_2661692, baseEnd_2661692] using wordTrace_append hprefix tailTrace_2661692
  have hstable : (prefixWord ++ tailWord_2661692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661692).length < 2 ^ (prefixWord ++ tailWord_2661692).sum := by decide
  have hdescent : baseEnd_2661692 < baseStart_2661692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661703 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 2, 5]
def baseStart_2661703 : Nat := 118140960795 + 2661703 * 2 ^ 59
def prefixEnd_2661703 : Nat := 4983230072969 + 3 ^ 40 * 2661703 * 2
def baseEnd_2661703 : Nat := 911155332342869872314371

theorem tailTrace_2661703 : CollatzResearch.WordTrace tailWord_2661703 prefixEnd_2661703 911155332342869872314371 := by
  unfold tailWord_2661703
  simp only [CollatzResearch.WordTrace]
  refine ⟨97080283876112088526333763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64720189250741392350889175 97080283876112088526333763)
  ·
    refine ⟨145620425814168132789500645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97080283876112088526333763 145620425814168132789500645)
    ·
      refine ⟨27303829840156524898031371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145620425814168132789500645 27303829840156524898031371)
      ·
        refine ⟨40955744760234787347047057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27303829840156524898031371 40955744760234787347047057)
        ·
          refine ⟨30716808570176090510285293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40955744760234787347047057 30716808570176090510285293)
          ·
            refine ⟨11518803213816033941356985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30716808570176090510285293 11518803213816033941356985)
            ·
              refine ⟨8639102410362025456017739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11518803213816033941356985 8639102410362025456017739)
              ·
                refine ⟨12958653615543038184026609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8639102410362025456017739 12958653615543038184026609)
                ·
                  refine ⟨9718990211657278638019957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12958653615543038184026609 9718990211657278638019957)
                  ·
                    refine ⟨911155332342869872314371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9718990211657278638019957 911155332342869872314371)
                    ·
                      rfl

theorem cell22_2661703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_2661703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661703 prefixEnd_2661703 := by exact prefixLift 2661703
  have htrace : WordTrace (prefixWord ++ tailWord_2661703) baseStart_2661703 baseEnd_2661703 := by
    simpa [prefixWord, tailWord_2661703, baseEnd_2661703] using wordTrace_append hprefix tailTrace_2661703
  have hstable : (prefixWord ++ tailWord_2661703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661703).length < 2 ^ (prefixWord ++ tailWord_2661703).sum := by decide
  have hdescent : baseEnd_2661703 < baseStart_2661703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661769 : List Nat := [1, 2, 1, 1, 8, 1, 1, 2, 1, 4]
def baseStart_2661769 : Nat := 118140960795 + 2661769 * 2 ^ 59
def prefixEnd_2661769 : Nat := 4983230072969 + 3 ^ 40 * 2661769 * 2
def baseEnd_2661769 : Nat := 911177925491667700164169

theorem tailTrace_2661769 : CollatzResearch.WordTrace tailWord_2661769 prefixEnd_2661769 911177925491667700164169 := by
  unfold tailWord_2661769
  simp only [CollatzResearch.WordTrace]
  refine ⟨97082691093872981798236361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64721794062581987865490907 97082691093872981798236361)
  ·
    refine ⟨72812018320404736348677271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97082691093872981798236361 72812018320404736348677271)
    ·
      refine ⟨109218027480607104523015907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72812018320404736348677271 109218027480607104523015907)
      ·
        refine ⟨163827041220910656784523861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109218027480607104523015907 163827041220910656784523861)
        ·
          refine ⟨1919848139307546759193639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 163827041220910656784523861 1919848139307546759193639)
          ·
            refine ⟨2879772208961320138790459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919848139307546759193639 2879772208961320138790459)
            ·
              refine ⟨4319658313441980208185689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879772208961320138790459 4319658313441980208185689)
              ·
                refine ⟨3239743735081485156139267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4319658313441980208185689 3239743735081485156139267)
                ·
                  refine ⟨4859615602622227734208901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3239743735081485156139267 4859615602622227734208901)
                  ·
                    refine ⟨911177925491667700164169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4859615602622227734208901 911177925491667700164169)
                    ·
                      rfl

theorem cell22_2661769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 1, 4].length) (baseStart_2661769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661769 prefixEnd_2661769 := by exact prefixLift 2661769
  have htrace : WordTrace (prefixWord ++ tailWord_2661769) baseStart_2661769 baseEnd_2661769 := by
    simpa [prefixWord, tailWord_2661769, baseEnd_2661769] using wordTrace_append hprefix tailTrace_2661769
  have hstable : (prefixWord ++ tailWord_2661769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661769).length < 2 ^ (prefixWord ++ tailWord_2661769).sum := by decide
  have hdescent : baseEnd_2661769 < baseStart_2661769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661857 : List Nat := [1, 2, 3, 1, 2, 5, 1, 2, 5]
def baseStart_2661857 : Nat := 118140960795 + 2661857 * 2 ^ 59
def prefixEnd_2661857 : Nat := 4983230072969 + 3 ^ 40 * 2661857 * 2
def baseEnd_2661857 : Nat := 303736016563354934654633

theorem tailTrace_2661857 : CollatzResearch.WordTrace tailWord_2661857 prefixEnd_2661857 303736016563354934654633 := by
  unfold tailWord_2661857
  simp only [CollatzResearch.WordTrace]
  refine ⟨97085900717554172827439825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64723933811702781884959883 97085900717554172827439825)
  ·
    refine ⟨72814425538165629620579869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97085900717554172827439825 72814425538165629620579869)
    ·
      refine ⟨27305409576812111107717451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72814425538165629620579869 27305409576812111107717451)
      ·
        refine ⟨40958114365218166661576177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27305409576812111107717451 40958114365218166661576177)
        ·
          refine ⟨30718585773913624996182133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40958114365218166661576177 30718585773913624996182133)
          ·
            refine ⟨2879867416304402343392075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30718585773913624996182133 2879867416304402343392075)
            ·
              refine ⟨4319801124456603515088113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879867416304402343392075 4319801124456603515088113)
              ·
                refine ⟨3239850843342452636316085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4319801124456603515088113 3239850843342452636316085)
                ·
                  refine ⟨303736016563354934654633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3239850843342452636316085 303736016563354934654633)
                  ·
                    rfl

theorem cell22_2661857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 5].length) (baseStart_2661857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661857 prefixEnd_2661857 := by exact prefixLift 2661857
  have htrace : WordTrace (prefixWord ++ tailWord_2661857) baseStart_2661857 baseEnd_2661857 := by
    simpa [prefixWord, tailWord_2661857, baseEnd_2661857] using wordTrace_append hprefix tailTrace_2661857
  have hstable : (prefixWord ++ tailWord_2661857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661857).length < 2 ^ (prefixWord ++ tailWord_2661857).sum := by decide
  have hdescent : baseEnd_2661857 < baseStart_2661857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661874 : List Nat := [3, 2, 1, 4, 1, 2, 3, 1, 5]
def baseStart_2661874 : Nat := 118140960795 + 2661874 * 2 ^ 59
def prefixEnd_2661874 : Nat := 4983230072969 + 3 ^ 40 * 2661874 * 2
def baseEnd_2661874 : Nat := 303737956379160808762949

theorem tailTrace_2661874 : CollatzResearch.WordTrace tailWord_2661874 prefixEnd_2661874 303737956379160808762949 := by
  unfold tailWord_2661874
  simp only [CollatzResearch.WordTrace]
  refine ⟨24271630189623146182702169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64724347172328389820539117 24271630189623146182702169)
  ·
    refine ⟨18203722642217359637026627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24271630189623146182702169 18203722642217359637026627)
    ·
      refine ⟨27305583963326039455539941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18203722642217359637026627 27305583963326039455539941)
      ·
        refine ⟨5119796993123632397913739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27305583963326039455539941 5119796993123632397913739)
        ·
          refine ⟨7679695489685448596870609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5119796993123632397913739 7679695489685448596870609)
          ·
            refine ⟨5759771617264086447652957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7679695489685448596870609 5759771617264086447652957)
            ·
              refine ⟨2159914356474032417869859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5759771617264086447652957 2159914356474032417869859)
              ·
                refine ⟨3239871534711048626804789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159914356474032417869859 3239871534711048626804789)
                ·
                  refine ⟨303737956379160808762949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3239871534711048626804789 303737956379160808762949)
                  ·
                    rfl

theorem cell22_2661874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_2661874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661874 prefixEnd_2661874 := by exact prefixLift 2661874
  have htrace : WordTrace (prefixWord ++ tailWord_2661874) baseStart_2661874 baseEnd_2661874 := by
    simpa [prefixWord, tailWord_2661874, baseEnd_2661874] using wordTrace_append hprefix tailTrace_2661874
  have hstable : (prefixWord ++ tailWord_2661874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661874).length < 2 ^ (prefixWord ++ tailWord_2661874).sum := by decide
  have hdescent : baseEnd_2661874 < baseStart_2661874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661885 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 6]
def baseStart_2661885 : Nat := 118140960795 + 2661885 * 2 ^ 59
def prefixEnd_2661885 : Nat := 4983230072969 + 3 ^ 40 * 2661885 * 2
def baseEnd_2661885 : Nat := 303739211554094021421271

theorem tailTrace_2661885 : CollatzResearch.WordTrace tailWord_2661885 prefixEnd_2661885 303739211554094021421271 := by
  unfold tailWord_2661885
  simp only [CollatzResearch.WordTrace]
  refine ⟨97086921961452733609459109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64724614640968489072972739 97086921961452733609459109)
  ·
    refine ⟨18203797867772387551773583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97086921961452733609459109 18203797867772387551773583)
    ·
      refine ⟨27305696801658581327660375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18203797867772387551773583 27305696801658581327660375)
      ·
        refine ⟨40958545202487871991490563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27305696801658581327660375 40958545202487871991490563)
        ·
          refine ⟨61437817803731807987235845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40958545202487871991490563 61437817803731807987235845)
          ·
            refine ⟨11519590838199713997606721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61437817803731807987235845 11519590838199713997606721)
            ·
              refine ⟨8639693128649785498205041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11519590838199713997606721 8639693128649785498205041)
              ·
                refine ⟨6479769846487339123653781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8639693128649785498205041 6479769846487339123653781)
                ·
                  refine ⟨303739211554094021421271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6479769846487339123653781 303739211554094021421271)
                  ·
                    rfl

theorem cell22_2661885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_2661885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661885 prefixEnd_2661885 := by exact prefixLift 2661885
  have htrace : WordTrace (prefixWord ++ tailWord_2661885) baseStart_2661885 baseEnd_2661885 := by
    simpa [prefixWord, tailWord_2661885, baseEnd_2661885] using wordTrace_append hprefix tailTrace_2661885
  have hstable : (prefixWord ++ tailWord_2661885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661885).length < 2 ^ (prefixWord ++ tailWord_2661885).sum := by decide
  have hdescent : baseEnd_2661885 < baseStart_2661885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661917 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_2661917 : Nat := 118140960795 + 2661917 * 2 ^ 59
def prefixEnd_2661917 : Nat := 4983230072969 + 3 ^ 40 * 2661917 * 2
def baseEnd_2661917 : Nat := 911228588916244647463715

theorem tailTrace_2661917 : CollatzResearch.WordTrace tailWord_2661917 prefixEnd_2661917 911228588916244647463715 := by
  unfold tailWord_2661917
  simp only [CollatzResearch.WordTrace]
  refine ⟨97088089097336803074624005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64725392731557868716416003 97088089097336803074624005)
  ·
    refine ⟨18204016705750650576492001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97088089097336803074624005 18204016705750650576492001)
    ·
      refine ⟨13653012529312987932369001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18204016705750650576492001 13653012529312987932369001)
      ·
        refine ⟨10239759396984740949276751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13653012529312987932369001 10239759396984740949276751)
        ·
          refine ⟨15359639095477111423915127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10239759396984740949276751 15359639095477111423915127)
          ·
            refine ⟨23039458643215667135872691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15359639095477111423915127 23039458643215667135872691)
            ·
              refine ⟨34559187964823500703809037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23039458643215667135872691 34559187964823500703809037)
              ·
                refine ⟨12959695486808812763928389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34559187964823500703809037 12959695486808812763928389)
                ·
                  refine ⟨2429942903776652393236573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12959695486808812763928389 2429942903776652393236573)
                  ·
                    refine ⟨911228588916244647463715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2429942903776652393236573 911228588916244647463715)
                    ·
                      rfl

theorem cell22_2661917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_2661917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661917 prefixEnd_2661917 := by exact prefixLift 2661917
  have htrace : WordTrace (prefixWord ++ tailWord_2661917) baseStart_2661917 baseEnd_2661917 := by
    simpa [prefixWord, tailWord_2661917, baseEnd_2661917] using wordTrace_append hprefix tailTrace_2661917
  have hstable : (prefixWord ++ tailWord_2661917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661917).length < 2 ^ (prefixWord ++ tailWord_2661917).sum := by decide
  have hdescent : baseEnd_2661917 < baseStart_2661917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661949 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_2661949 : Nat := 118140960795 + 2661949 * 2 ^ 59
def prefixEnd_2661949 : Nat := 4983230072969 + 3 ^ 40 * 2661949 * 2
def baseEnd_2661949 : Nat := 911239543170207230663617

theorem tailTrace_2661949 : CollatzResearch.WordTrace tailWord_2661949 prefixEnd_2661949 911239543170207230663617 := by
  unfold tailWord_2661949
  simp only [CollatzResearch.WordTrace]
  refine ⟨97089256233220872539788901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64726170822147248359859267 97089256233220872539788901)
  ·
    refine ⟨18204235543728913601210419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97089256233220872539788901 18204235543728913601210419)
    ·
      refine ⟨27306353315593370401815629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18204235543728913601210419 27306353315593370401815629)
      ·
        refine ⟨10239882493347513900680861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27306353315593370401815629 10239882493347513900680861)
        ·
          refine ⟨3839955935005317712755323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10239882493347513900680861 3839955935005317712755323)
          ·
            refine ⟨5759933902507976569132985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3839955935005317712755323 5759933902507976569132985)
            ·
              refine ⟨4319950426880982426849739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5759933902507976569132985 4319950426880982426849739)
              ·
                refine ⟨6479925640321473640274609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4319950426880982426849739 6479925640321473640274609)
                ·
                  refine ⟨4859944230241105230205957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6479925640321473640274609 4859944230241105230205957)
                  ·
                    refine ⟨911239543170207230663617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4859944230241105230205957 911239543170207230663617)
                    ·
                      rfl

theorem cell22_2661949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_2661949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661949 prefixEnd_2661949 := by exact prefixLift 2661949
  have htrace : WordTrace (prefixWord ++ tailWord_2661949) baseStart_2661949 baseEnd_2661949 := by
    simpa [prefixWord, tailWord_2661949, baseEnd_2661949] using wordTrace_append hprefix tailTrace_2661949
  have hstable : (prefixWord ++ tailWord_2661949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661949).length < 2 ^ (prefixWord ++ tailWord_2661949).sum := by decide
  have hdescent : baseEnd_2661949 < baseStart_2661949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661981 : List Nat := [1, 4, 4, 2, 1, 2, 1, 7]
def baseStart_2661981 : Nat := 118140960795 + 2661981 * 2 ^ 59
def prefixEnd_2661981 : Nat := 4983230072969 + 3 ^ 40 * 2661981 * 2
def baseEnd_2661981 : Nat := 101250055269352201540391

theorem tailTrace_2661981 : CollatzResearch.WordTrace tailWord_2661981 prefixEnd_2661981 101250055269352201540391 := by
  unfold tailWord_2661981
  simp only [CollatzResearch.WordTrace]
  refine ⟨97090423369104942004953797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64726948912736628003302531 97090423369104942004953797)
  ·
    refine ⟨18204454381707176625928837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97090423369104942004953797 18204454381707176625928837)
    ·
      refine ⟨3413335196570095617361657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18204454381707176625928837 3413335196570095617361657)
      ·
        refine ⟨2560001397427571713021243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3413335196570095617361657 2560001397427571713021243)
        ·
          refine ⟨3840002096141357569531865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560001397427571713021243 3840002096141357569531865)
          ·
            refine ⟨2880001572106018177148899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3840002096141357569531865 2880001572106018177148899)
            ·
              refine ⟨4320002358159027265723349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2880001572106018177148899 4320002358159027265723349)
              ·
                refine ⟨101250055269352201540391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4320002358159027265723349 101250055269352201540391)
                ·
                  rfl

theorem cell22_2661981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 7].length) (baseStart_2661981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2661981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2661981 prefixEnd_2661981 := by exact prefixLift 2661981
  have htrace : WordTrace (prefixWord ++ tailWord_2661981) baseStart_2661981 baseEnd_2661981 := by
    simpa [prefixWord, tailWord_2661981, baseEnd_2661981] using wordTrace_append hprefix tailTrace_2661981
  have hstable : (prefixWord ++ tailWord_2661981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661981).length < 2 ^ (prefixWord ++ tailWord_2661981).sum := by decide
  have hdescent : baseEnd_2661981 < baseStart_2661981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662067 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 2, 4]
def baseStart_2662067 : Nat := 118140960795 + 2662067 * 2 ^ 59
def prefixEnd_2662067 : Nat := 4983230072969 + 3 ^ 40 * 2662067 * 2
def baseEnd_2662067 : Nat := 911279936981694256213255

theorem tailTrace_2662067 : CollatzResearch.WordTrace tailWord_2662067 prefixEnd_2662067 911279936981694256213255 := by
  unfold tailWord_2662067
  simp only [CollatzResearch.WordTrace]
  refine ⟨97093560046793378692584455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64729040031195585795056303 97093560046793378692584455)
  ·
    refine ⟨145640340070190068038876683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97093560046793378692584455 145640340070190068038876683)
    ·
      refine ⟨218460510105285102058315025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145640340070190068038876683 218460510105285102058315025)
      ·
        refine ⟨163845382578963826543736269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218460510105285102058315025 163845382578963826543736269)
        ·
          refine ⟨61442018467111434953901101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163845382578963826543736269 61442018467111434953901101)
          ·
            refine ⟨23040756925166788107712913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61442018467111434953901101 23040756925166788107712913)
            ·
              refine ⟨17280567693875091080784685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23040756925166788107712913 17280567693875091080784685)
              ·
                refine ⟨6480212885203159155294257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17280567693875091080784685 6480212885203159155294257)
                ·
                  refine ⟨4860159663902369366470693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6480212885203159155294257 4860159663902369366470693)
                  ·
                    refine ⟨911279936981694256213255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4860159663902369366470693 911279936981694256213255)
                    ·
                      rfl

theorem cell22_2662067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 4].length) (baseStart_2662067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662067 prefixEnd_2662067 := by exact prefixLift 2662067
  have htrace : WordTrace (prefixWord ++ tailWord_2662067) baseStart_2662067 baseEnd_2662067 := by
    simpa [prefixWord, tailWord_2662067, baseEnd_2662067] using wordTrace_append hprefix tailTrace_2662067
  have hstable : (prefixWord ++ tailWord_2662067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662067).length < 2 ^ (prefixWord ++ tailWord_2662067).sum := by decide
  have hdescent : baseEnd_2662067 < baseStart_2662067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662071 : List Nat := [1, 1, 3, 1, 5, 3, 1, 3, 4]
def baseStart_2662071 : Nat := 118140960795 + 2662071 * 2 ^ 59
def prefixEnd_2662071 : Nat := 4983230072969 + 3 ^ 40 * 2662071 * 2
def baseEnd_2662071 : Nat := 303760435421146526371081

theorem tailTrace_2662071 : CollatzResearch.WordTrace tailWord_2662071 prefixEnd_2662071 303760435421146526371081 := by
  unfold tailWord_2662071
  simp only [CollatzResearch.WordTrace]
  refine ⟨97093705938778887375730067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64729137292519258250486711 97093705938778887375730067)
  ·
    refine ⟨145640558908168331063595101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97093705938778887375730067 145640558908168331063595101)
    ·
      refine ⟨54615209590563124148848163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145640558908168331063595101 54615209590563124148848163)
      ·
        refine ⟨81922814385844686223272245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54615209590563124148848163 81922814385844686223272245)
        ·
          refine ⟨7680263848672939333431773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81922814385844686223272245 7680263848672939333431773)
          ·
            refine ⟨2880098943252352250036915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7680263848672939333431773 2880098943252352250036915)
            ·
              refine ⟨4320148414878528375055373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2880098943252352250036915 4320148414878528375055373)
              ·
                refine ⟨1620055655579448140645765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4320148414878528375055373 1620055655579448140645765)
                ·
                  refine ⟨303760435421146526371081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1620055655579448140645765 303760435421146526371081)
                  ·
                    rfl

theorem cell22_2662071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 4].length) (baseStart_2662071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662071 prefixEnd_2662071 := by exact prefixLift 2662071
  have htrace : WordTrace (prefixWord ++ tailWord_2662071) baseStart_2662071 baseEnd_2662071 := by
    simpa [prefixWord, tailWord_2662071, baseEnd_2662071] using wordTrace_append hprefix tailTrace_2662071
  have hstable : (prefixWord ++ tailWord_2662071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662071).length < 2 ^ (prefixWord ++ tailWord_2662071).sum := by decide
  have hdescent : baseEnd_2662071 < baseStart_2662071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662084 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_2662084 : Nat := 118140960795 + 2662084 * 2 ^ 59
def prefixEnd_2662084 : Nat := 4983230072969 + 3 ^ 40 * 2662084 * 2
def baseEnd_2662084 : Nat := 911285756429111878538203

theorem tailTrace_2662084 : CollatzResearch.WordTrace tailWord_2662084 prefixEnd_2662084 911285756429111878538203 := by
  unfold tailWord_2662084
  simp only [CollatzResearch.WordTrace]
  refine ⟨48547090043865895297976653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64729453391821193730635537 48547090043865895297976653)
  ·
    refine ⟨18205158766449710736741245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48547090043865895297976653 18205158766449710736741245)
    ·
      refine ⟨6826934537418641526277967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18205158766449710736741245 6826934537418641526277967)
      ·
        refine ⟨10240401806127962289416951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6826934537418641526277967 10240401806127962289416951)
        ·
          refine ⟨15360602709191943434125427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10240401806127962289416951 15360602709191943434125427)
          ·
            refine ⟨23040904063787915151188141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15360602709191943434125427 23040904063787915151188141)
            ·
              refine ⟨8640339023920468181695553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23040904063787915151188141 8640339023920468181695553)
              ·
                refine ⟨6480254267940351136271665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8640339023920468181695553 6480254267940351136271665)
                ·
                  refine ⟨4860190700955263352203749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6480254267940351136271665 4860190700955263352203749)
                  ·
                    refine ⟨911285756429111878538203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4860190700955263352203749 911285756429111878538203)
                    ·
                      rfl

theorem cell22_2662084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_2662084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662084 prefixEnd_2662084 := by exact prefixLift 2662084
  have htrace : WordTrace (prefixWord ++ tailWord_2662084) baseStart_2662084 baseEnd_2662084 := by
    simpa [prefixWord, tailWord_2662084, baseEnd_2662084] using wordTrace_append hprefix tailTrace_2662084
  have hstable : (prefixWord ++ tailWord_2662084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662084).length < 2 ^ (prefixWord ++ tailWord_2662084).sum := by decide
  have hdescent : baseEnd_2662084 < baseStart_2662084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662148 : List Nat := [2, 3, 2, 2, 1, 3, 1, 4, 1, 3]
def baseStart_2662148 : Nat := 118140960795 + 2662148 * 2 ^ 59
def prefixEnd_2662148 : Nat := 4983230072969 + 3 ^ 40 * 2662148 * 2
def baseEnd_2662148 : Nat := 911307664937037044938007

theorem tailTrace_2662148 : CollatzResearch.WordTrace tailWord_2662148 prefixEnd_2662148 911307664937037044938007 := by
  unfold tailWord_2662148
  simp only [CollatzResearch.WordTrace]
  refine ⟨48548257179749964763141549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64731009572999953017522065 48548257179749964763141549)
  ·
    refine ⟨18205596442406236786178081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48548257179749964763141549 18205596442406236786178081)
    ·
      refine ⟨13654197331804677589633561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18205596442406236786178081 13654197331804677589633561)
      ·
        refine ⟨10240647998853508192225171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13654197331804677589633561 10240647998853508192225171)
        ·
          refine ⟨15360971998280262288337757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10240647998853508192225171 15360971998280262288337757)
          ·
            refine ⟨5760364499355098358126659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15360971998280262288337757 5760364499355098358126659)
            ·
              refine ⟨8640546749032647537189989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5760364499355098358126659 8640546749032647537189989)
              ·
                refine ⟨1620102515443621413223123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8640546749032647537189989 1620102515443621413223123)
                ·
                  refine ⟨2430153773165432119834685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620102515443621413223123 2430153773165432119834685)
                  ·
                    refine ⟨911307664937037044938007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2430153773165432119834685 911307664937037044938007)
                    ·
                      rfl

theorem cell22_2662148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_2662148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662148 prefixEnd_2662148 := by exact prefixLift 2662148
  have htrace : WordTrace (prefixWord ++ tailWord_2662148) baseStart_2662148 baseEnd_2662148 := by
    simpa [prefixWord, tailWord_2662148, baseEnd_2662148] using wordTrace_append hprefix tailTrace_2662148
  have hstable : (prefixWord ++ tailWord_2662148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662148).length < 2 ^ (prefixWord ++ tailWord_2662148).sum := by decide
  have hdescent : baseEnd_2662148 < baseStart_2662148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662206 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_2662206 : Nat := 118140960795 + 2662206 * 2 ^ 59
def prefixEnd_2662206 : Nat := 4983230072969 + 3 ^ 40 * 2662206 * 2
def baseEnd_2662206 : Nat := 303775839840781408995943

theorem tailTrace_2662206 : CollatzResearch.WordTrace tailWord_2662206 prefixEnd_2662206 303775839840781408995943 := by
  unfold tailWord_2662206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12137328724161225678986809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64732419862193203621262981 12137328724161225678986809)
  ·
    refine ⟨9102996543120919259240107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12137328724161225678986809 9102996543120919259240107)
    ·
      refine ⟨13654494814681378888860161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9102996543120919259240107 13654494814681378888860161)
      ·
        refine ⟨10240871111011034166645121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13654494814681378888860161 10240871111011034166645121)
        ·
          refine ⟨7680653333258275624983841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10240871111011034166645121 7680653333258275624983841)
          ·
            refine ⟨5760489999943706718737881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7680653333258275624983841 5760489999943706718737881)
            ·
              refine ⟨4320367499957780039053411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5760489999943706718737881 4320367499957780039053411)
              ·
                refine ⟨6480551249936670058580117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4320367499957780039053411 6480551249936670058580117)
                ·
                  refine ⟨303775839840781408995943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6480551249936670058580117 303775839840781408995943)
                  ·
                    rfl

theorem cell22_2662206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_2662206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662206 prefixEnd_2662206 := by exact prefixLift 2662206
  have htrace : WordTrace (prefixWord ++ tailWord_2662206) baseStart_2662206 baseEnd_2662206 := by
    simpa [prefixWord, tailWord_2662206, baseEnd_2662206] using wordTrace_append hprefix tailTrace_2662206
  have hstable : (prefixWord ++ tailWord_2662206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662206).length < 2 ^ (prefixWord ++ tailWord_2662206).sum := by decide
  have hdescent : baseEnd_2662206 < baseStart_2662206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662217 : List Nat := [1, 2, 1, 1, 2, 4, 2, 9]
def baseStart_2662217 : Nat := 118140960795 + 2662217 * 2 ^ 59
def prefixEnd_2662217 : Nat := 4983230072969 + 3 ^ 40 * 2662217 * 2
def baseEnd_2662217 : Nat := 101259031671904873884755

theorem tailTrace_2662217 : CollatzResearch.WordTrace tailWord_2662217 prefixEnd_2662217 101259031671904873884755 := by
  unfold tailWord_2662217
  simp only [CollatzResearch.WordTrace]
  refine ⟨97099030996249954310544905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64732687330833302873696603 97099030996249954310544905)
  ·
    refine ⟨72824273247187465732908679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97099030996249954310544905 72824273247187465732908679)
    ·
      refine ⟨109236409870781198599363019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72824273247187465732908679 109236409870781198599363019)
      ·
        refine ⟨163854614806171797899044529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109236409870781198599363019 163854614806171797899044529)
        ·
          refine ⟨122890961104628848424283397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163854614806171797899044529 122890961104628848424283397)
          ·
            refine ⟨23042055207117909079553137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122890961104628848424283397 23042055207117909079553137)
            ·
              refine ⟨17281541405338431809664853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23042055207117909079553137 17281541405338431809664853)
              ·
                refine ⟨101259031671904873884755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17281541405338431809664853 101259031671904873884755)
                ·
                  rfl

theorem cell22_2662217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 9].length) (baseStart_2662217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662217 prefixEnd_2662217 := by exact prefixLift 2662217
  have htrace : WordTrace (prefixWord ++ tailWord_2662217) baseStart_2662217 baseEnd_2662217 := by
    simpa [prefixWord, tailWord_2662217, baseEnd_2662217] using wordTrace_append hprefix tailTrace_2662217
  have hstable : (prefixWord ++ tailWord_2662217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662217).length < 2 ^ (prefixWord ++ tailWord_2662217).sum := by decide
  have hdescent : baseEnd_2662217 < baseStart_2662217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662249 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 5, 3]
def baseStart_2662249 : Nat := 118140960795 + 2662249 * 2 ^ 59
def prefixEnd_2662249 : Nat := 4983230072969 + 3 ^ 40 * 2662249 * 2
def baseEnd_2662249 : Nat := 911342239301106448162697

theorem tailTrace_2662249 : CollatzResearch.WordTrace tailWord_2662249 prefixEnd_2662249 911342239301106448162697 := by
  unfold tailWord_2662249
  simp only [CollatzResearch.WordTrace]
  refine ⟨97100198132134023775709801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64733465421422682517139867 97100198132134023775709801)
  ·
    refine ⟨72825148599100517831782351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97100198132134023775709801 72825148599100517831782351)
    ·
      refine ⟨109237722898650776747673527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72825148599100517831782351 109237722898650776747673527)
      ·
        refine ⟨163856584347976165121510291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109237722898650776747673527 163856584347976165121510291)
        ·
          refine ⟨245784876521964247682265437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163856584347976165121510291 245784876521964247682265437)
          ·
            refine ⟨92169328695736592880849539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245784876521964247682265437 92169328695736592880849539)
            ·
              refine ⟨138253993043604889321274309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92169328695736592880849539 138253993043604889321274309)
              ·
                refine ⟨25922623695675916747738933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138253993043604889321274309 25922623695675916747738933)
                ·
                  refine ⟨2430245971469617195100525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25922623695675916747738933 2430245971469617195100525)
                  ·
                    refine ⟨911342239301106448162697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2430245971469617195100525 911342239301106448162697)
                    ·
                      rfl

theorem cell22_2662249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 3].length) (baseStart_2662249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662249 prefixEnd_2662249 := by exact prefixLift 2662249
  have htrace : WordTrace (prefixWord ++ tailWord_2662249) baseStart_2662249 baseEnd_2662249 := by
    simpa [prefixWord, tailWord_2662249, baseEnd_2662249] using wordTrace_append hprefix tailTrace_2662249
  have hstable : (prefixWord ++ tailWord_2662249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662249).length < 2 ^ (prefixWord ++ tailWord_2662249).sum := by decide
  have hdescent : baseEnd_2662249 < baseStart_2662249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662266 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 3, 3]
def baseStart_2662266 : Nat := 118140960795 + 2662266 * 2 ^ 59
def prefixEnd_2662266 : Nat := 4983230072969 + 3 ^ 40 * 2662266 * 2
def baseEnd_2662266 : Nat := 911348058748524070487645

theorem tailTrace_2662266 : CollatzResearch.WordTrace tailWord_2662266 prefixEnd_2662266 911348058748524070487645 := by
  unfold tailWord_2662266
  simp only [CollatzResearch.WordTrace]
  refine ⟨24275204543268108919769663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64733878782048290452719101 24275204543268108919769663)
  ·
    refine ⟨36412806814902163379654495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24275204543268108919769663 36412806814902163379654495)
    ·
      refine ⟨54619210222353245069481743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36412806814902163379654495 54619210222353245069481743)
      ·
        refine ⟨81928815333529867604222615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54619210222353245069481743 81928815333529867604222615)
        ·
          refine ⟨122893223000294801406333923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81928815333529867604222615 122893223000294801406333923)
          ·
            refine ⟨184339834500442202109500885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122893223000294801406333923 184339834500442202109500885)
            ·
              refine ⟨4320464871104114111941427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 184339834500442202109500885 4320464871104114111941427)
              ·
                refine ⟨6480697306656171167912141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4320464871104114111941427 6480697306656171167912141)
                ·
                  refine ⟨2430261489996064187967053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6480697306656171167912141 2430261489996064187967053)
                  ·
                    refine ⟨911348058748524070487645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2430261489996064187967053 911348058748524070487645)
                    ·
                      rfl

theorem cell22_2662266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_2662266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662266 prefixEnd_2662266 := by exact prefixLift 2662266
  have htrace : WordTrace (prefixWord ++ tailWord_2662266) baseStart_2662266 baseEnd_2662266 := by
    simpa [prefixWord, tailWord_2662266, baseEnd_2662266] using wordTrace_append hprefix tailTrace_2662266
  have hstable : (prefixWord ++ tailWord_2662266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662266).length < 2 ^ (prefixWord ++ tailWord_2662266).sum := by decide
  have hdescent : baseEnd_2662266 < baseStart_2662266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662356 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_2662356 : Nat := 118140960795 + 2662356 * 2 ^ 59
def prefixEnd_2662356 : Nat := 4983230072969 + 3 ^ 40 * 2662356 * 2
def baseEnd_2662356 : Nat := 911378867587793835737369

theorem tailTrace_2662356 : CollatzResearch.WordTrace tailWord_2662356 prefixEnd_2662356 911378867587793835737369 := by
  unfold tailWord_2662356
  simp only [CollatzResearch.WordTrace]
  refine ⟨48552050371373190524927461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64736067161830920699903281 48552050371373190524927461)
  ·
    refine ⟨9103509444632473223423899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48552050371373190524927461 9103509444632473223423899)
    ·
      refine ⟨13655264166948709835135849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9103509444632473223423899 13655264166948709835135849)
      ·
        refine ⟨10241448125211532376351887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13655264166948709835135849 10241448125211532376351887)
        ·
          refine ⟨15362172187817298564527831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10241448125211532376351887 15362172187817298564527831)
          ·
            refine ⟨23043258281725947846791747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15362172187817298564527831 23043258281725947846791747)
            ·
              refine ⟨34564887422588921770187621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23043258281725947846791747 34564887422588921770187621)
              ·
                refine ⟨6480916391735422831910179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34564887422588921770187621 6480916391735422831910179)
                ·
                  refine ⟨9721374587603134247865269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6480916391735422831910179 9721374587603134247865269)
                  ·
                    refine ⟨911378867587793835737369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9721374587603134247865269 911378867587793835737369)
                    ·
                      rfl

theorem cell22_2662356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_2662356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662356 prefixEnd_2662356 := by exact prefixLift 2662356
  have htrace : WordTrace (prefixWord ++ tailWord_2662356) baseStart_2662356 baseEnd_2662356 := by
    simpa [prefixWord, tailWord_2662356, baseEnd_2662356] using wordTrace_append hprefix tailTrace_2662356
  have hstable : (prefixWord ++ tailWord_2662356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662356).length < 2 ^ (prefixWord ++ tailWord_2662356).sum := by decide
  have hdescent : baseEnd_2662356 < baseStart_2662356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662364 : List Nat := [2, 2, 6, 1, 2, 1, 1, 2, 5]
def baseStart_2662364 : Nat := 118140960795 + 2662364 * 2 ^ 59
def prefixEnd_2662364 : Nat := 4983230072969 + 3 ^ 40 * 2662364 * 2
def baseEnd_2662364 : Nat := 303793868717094827179115

theorem tailTrace_2662364 : CollatzResearch.WordTrace tailWord_2662364 prefixEnd_2662364 303793868717094827179115 := by
  unfold tailWord_2662364
  simp only [CollatzResearch.WordTrace]
  refine ⟨48552196263358699208073073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64736261684478265610764097 48552196263358699208073073)
  ·
    refine ⟨36414147197519024406054805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48552196263358699208073073 36414147197519024406054805)
    ·
      refine ⟨1706913149883704269033819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36414147197519024406054805 1706913149883704269033819)
      ·
        refine ⟨2560369724825556403550729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1706913149883704269033819 2560369724825556403550729)
        ·
          refine ⟨1920277293619167302663047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2560369724825556403550729 1920277293619167302663047)
          ·
            refine ⟨2880415940428750953994571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920277293619167302663047 2880415940428750953994571)
            ·
              refine ⟨4320623910643126430991857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2880415940428750953994571 4320623910643126430991857)
              ·
                refine ⟨3240467932982344823243893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4320623910643126430991857 3240467932982344823243893)
                ·
                  refine ⟨303793868717094827179115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3240467932982344823243893 303793868717094827179115)
                  ·
                    rfl

theorem cell22_2662364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_2662364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662364 prefixEnd_2662364 := by exact prefixLift 2662364
  have htrace : WordTrace (prefixWord ++ tailWord_2662364) baseStart_2662364 baseEnd_2662364 := by
    simpa [prefixWord, tailWord_2662364, baseEnd_2662364] using wordTrace_append hprefix tailTrace_2662364
  have hstable : (prefixWord ++ tailWord_2662364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662364).length < 2 ^ (prefixWord ++ tailWord_2662364).sum := by decide
  have hdescent : baseEnd_2662364 < baseStart_2662364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662390 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_2662390 : Nat := 118140960795 + 2662390 * 2 ^ 59
def prefixEnd_2662390 : Nat := 4983230072969 + 3 ^ 40 * 2662390 * 2
def baseEnd_2662390 : Nat := 911390506482629080387265

theorem tailTrace_2662390 : CollatzResearch.WordTrace tailWord_2662390 prefixEnd_2662390 911390506482629080387265 := by
  unfold tailWord_2662390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6069083801538950303537039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64736893883082136571061749 6069083801538950303537039)
  ·
    refine ⟨9103625702308425455305559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6069083801538950303537039 9103625702308425455305559)
    ·
      refine ⟨13655438553462638182958339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9103625702308425455305559 13655438553462638182958339)
      ·
        refine ⟨20483157830193957274437509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13655438553462638182958339 20483157830193957274437509)
        ·
          refine ⟨3840592093161366988957033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20483157830193957274437509 3840592093161366988957033)
          ·
            refine ⟨2880444069871025241717775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3840592093161366988957033 2880444069871025241717775)
            ·
              refine ⟨4320666104806537862576663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2880444069871025241717775 4320666104806537862576663)
              ·
                refine ⟨6480999157209806793864995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4320666104806537862576663 6480999157209806793864995)
                ·
                  refine ⟨9721498735814710190797493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6480999157209806793864995 9721498735814710190797493)
                  ·
                    refine ⟨911390506482629080387265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9721498735814710190797493 911390506482629080387265)
                    ·
                      rfl

theorem cell22_2662390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_2662390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662390 prefixEnd_2662390 := by exact prefixLift 2662390
  have htrace : WordTrace (prefixWord ++ tailWord_2662390) baseStart_2662390 baseEnd_2662390 := by
    simpa [prefixWord, tailWord_2662390, baseEnd_2662390] using wordTrace_append hprefix tailTrace_2662390
  have hstable : (prefixWord ++ tailWord_2662390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662390).length < 2 ^ (prefixWord ++ tailWord_2662390).sum := by decide
  have hdescent : baseEnd_2662390 < baseStart_2662390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662399 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 2, 6]
def baseStart_2662399 : Nat := 118140960795 + 2662399 * 2 ^ 59
def prefixEnd_2662399 : Nat := 4983230072969 + 3 ^ 40 * 2662399 * 2
def baseEnd_2662399 : Nat := 911393587366556056912237

theorem tailTrace_2662399 : CollatzResearch.WordTrace tailWord_2662399 prefixEnd_2662399 911393587366556056912237 := by
  unfold tailWord_2662399
  simp only [CollatzResearch.WordTrace]
  refine ⟨97105669081590599393670251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64737112721060399595780167 97105669081590599393670251)
  ·
    refine ⟨145658503622385899090505377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97105669081590599393670251 145658503622385899090505377)
    ·
      refine ⟨109243877716789424317879033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145658503622385899090505377 109243877716789424317879033)
      ·
        refine ⟨81932908287592068238409275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109243877716789424317879033 81932908287592068238409275)
        ·
          refine ⟨122899362431388102357613913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81932908287592068238409275 122899362431388102357613913)
          ·
            refine ⟨92174521823541076768210435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122899362431388102357613913 92174521823541076768210435)
            ·
              refine ⟨138261782735311615152315653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92174521823541076768210435 138261782735311615152315653)
              ·
                refine ⟨25924084262870927841059185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138261782735311615152315653 25924084262870927841059185)
                ·
                  refine ⟨19443063197153195880794389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25924084262870927841059185 19443063197153195880794389)
                  ·
                    refine ⟨911393587366556056912237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19443063197153195880794389 911393587366556056912237)
                    ·
                      rfl

theorem cell22_2662399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_2662399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662399 prefixEnd_2662399 := by exact prefixLift 2662399
  have htrace : WordTrace (prefixWord ++ tailWord_2662399) baseStart_2662399 baseEnd_2662399 := by
    simpa [prefixWord, tailWord_2662399, baseEnd_2662399] using wordTrace_append hprefix tailTrace_2662399
  have hstable : (prefixWord ++ tailWord_2662399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662399).length < 2 ^ (prefixWord ++ tailWord_2662399).sum := by decide
  have hdescent : baseEnd_2662399 < baseStart_2662399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662420 : List Nat := [2, 4, 3, 2, 1, 2, 8]
def baseStart_2662420 : Nat := 118140960795 + 2662420 * 2 ^ 59
def prefixEnd_2662420 : Nat := 4983230072969 + 3 ^ 40 * 2662420 * 2
def baseEnd_2662420 : Nat := 33755584299841444523599

theorem tailTrace_2662420 : CollatzResearch.WordTrace tailWord_2662420 prefixEnd_2662420 33755584299841444523599 := by
  unfold tailWord_2662420
  simp only [CollatzResearch.WordTrace]
  refine ⟨48553217507257259990092357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64737623343009679986789809 48553217507257259990092357)
  ·
    refine ⟨9103728282610736248142317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48553217507257259990092357 9103728282610736248142317)
    ·
      refine ⟨3413898105979026093053369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9103728282610736248142317 3413898105979026093053369)
      ·
        refine ⟨2560423579484269569790027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3413898105979026093053369 2560423579484269569790027)
        ·
          refine ⟨3840635369226404354685041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560423579484269569790027 3840635369226404354685041)
          ·
            refine ⟨2880476526919803266013781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3840635369226404354685041 2880476526919803266013781)
            ·
              refine ⟨33755584299841444523599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2880476526919803266013781 33755584299841444523599)
              ·
                rfl

theorem cell22_2662420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 8].length) (baseStart_2662420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662420 prefixEnd_2662420 := by exact prefixLift 2662420
  have htrace : WordTrace (prefixWord ++ tailWord_2662420) baseStart_2662420 baseEnd_2662420 := by
    simpa [prefixWord, tailWord_2662420, baseEnd_2662420] using wordTrace_append hprefix tailTrace_2662420
  have hstable : (prefixWord ++ tailWord_2662420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662420).length < 2 ^ (prefixWord ++ tailWord_2662420).sum := by decide
  have hdescent : baseEnd_2662420 < baseStart_2662420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662431 : List Nat := [1, 1, 2, 4, 1, 2, 2, 4, 5]
def baseStart_2662431 : Nat := 118140960795 + 2662431 * 2 ^ 59
def prefixEnd_2662431 : Nat := 4983230072969 + 3 ^ 40 * 2662431 * 2
def baseEnd_2662431 : Nat := 303801513873506213370713

theorem tailTrace_2662431 : CollatzResearch.WordTrace tailWord_2662431 prefixEnd_2662431 303801513873506213370713 := by
  unfold tailWord_2662431
  simp only [CollatzResearch.WordTrace]
  refine ⟨97106836217474668858835147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64737890811649779239223431 97106836217474668858835147)
  ·
    refine ⟨145660254326212003288252721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97106836217474668858835147 145660254326212003288252721)
    ·
      refine ⟨109245190744659002466189541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145660254326212003288252721 109245190744659002466189541)
      ·
        refine ⟨20483473264623562962410539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109245190744659002466189541 20483473264623562962410539)
        ·
          refine ⟨30725209896935344443615809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20483473264623562962410539 30725209896935344443615809)
          ·
            refine ⟨23043907422701508332711857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30725209896935344443615809 23043907422701508332711857)
            ·
              refine ⟨17282930567026131249533893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23043907422701508332711857 17282930567026131249533893)
              ·
                refine ⟨3240549481317399609287605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17282930567026131249533893 3240549481317399609287605)
                ·
                  refine ⟨303801513873506213370713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3240549481317399609287605 303801513873506213370713)
                  ·
                    rfl

theorem cell22_2662431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 5].length) (baseStart_2662431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662431 prefixEnd_2662431 := by exact prefixLift 2662431
  have htrace : WordTrace (prefixWord ++ tailWord_2662431) baseStart_2662431 baseEnd_2662431 := by
    simpa [prefixWord, tailWord_2662431, baseEnd_2662431] using wordTrace_append hprefix tailTrace_2662431
  have hstable : (prefixWord ++ tailWord_2662431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662431).length < 2 ^ (prefixWord ++ tailWord_2662431).sum := by decide
  have hdescent : baseEnd_2662431 < baseStart_2662431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662448 : List Nat := [2, 1, 1, 1, 2, 5, 4, 1, 5]
def baseStart_2662448 : Nat := 118140960795 + 2662448 * 2 ^ 59
def prefixEnd_2662448 : Nat := 4983230072969 + 3 ^ 40 * 2662448 * 2
def baseEnd_2662448 : Nat := 303803453689312087479029

theorem tailTrace_2662448 : CollatzResearch.WordTrace tailWord_2662448 prefixEnd_2662448 303803453689312087479029 := by
  unfold tailWord_2662448
  simp only [CollatzResearch.WordTrace]
  refine ⟨48553728129206540381101999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64738304172275387174802665 48553728129206540381101999)
  ·
    refine ⟨72830592193809810571652999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48553728129206540381101999 72830592193809810571652999)
    ·
      refine ⟨109245888290714715857479499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72830592193809810571652999 109245888290714715857479499)
      ·
        refine ⟨163868832436072073786219249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109245888290714715857479499 163868832436072073786219249)
        ·
          refine ⟨122901624327054055339664437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163868832436072073786219249 122901624327054055339664437)
          ·
            refine ⟨11522027280661317688093541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122901624327054055339664437 11522027280661317688093541)
            ·
              refine ⟨2160380115123997066517539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11522027280661317688093541 2160380115123997066517539)
              ·
                refine ⟨3240570172685995599776309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2160380115123997066517539 3240570172685995599776309)
                ·
                  refine ⟨303803453689312087479029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3240570172685995599776309 303803453689312087479029)
                  ·
                    rfl

theorem cell22_2662448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 5].length) (baseStart_2662448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662448 prefixEnd_2662448 := by exact prefixLift 2662448
  have htrace : WordTrace (prefixWord ++ tailWord_2662448) baseStart_2662448 baseEnd_2662448 := by
    simpa [prefixWord, tailWord_2662448, baseEnd_2662448] using wordTrace_append hprefix tailTrace_2662448
  have hstable : (prefixWord ++ tailWord_2662448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662448).length < 2 ^ (prefixWord ++ tailWord_2662448).sum := by decide
  have hdescent : baseEnd_2662448 < baseStart_2662448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662486 : List Nat := [5, 2, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2662486 : Nat := 118140960795 + 2662486 * 2 ^ 59
def prefixEnd_2662486 : Nat := 4983230072969 + 3 ^ 40 * 2662486 * 2
def baseEnd_2662486 : Nat := 911423369244516829986971

theorem tailTrace_2662486 : CollatzResearch.WordTrace tailWord_2662486 prefixEnd_2662486 911423369244516829986971 := by
  unfold tailWord_2662486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6069302639517213328255457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64739228154850275501391541 6069302639517213328255457)
  ·
    refine ⟨4551976979637909996191593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6069302639517213328255457 4551976979637909996191593)
    ·
      refine ⟨3413982734728432497143695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4551976979637909996191593 3413982734728432497143695)
      ·
        refine ⟨5120974102092648745715543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3413982734728432497143695 5120974102092648745715543)
        ·
          refine ⟨7681461153138973118573315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5120974102092648745715543 7681461153138973118573315)
          ·
            refine ⟨11522191729708459677859973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7681461153138973118573315 11522191729708459677859973)
            ·
              refine ⟨2160410949320336189598745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11522191729708459677859973 2160410949320336189598745)
              ·
                refine ⟨1620308211990252142199059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2160410949320336189598745 1620308211990252142199059)
                ·
                  refine ⟨2430462317985378213298589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620308211990252142199059 2430462317985378213298589)
                  ·
                    refine ⟨911423369244516829986971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2430462317985378213298589 911423369244516829986971)
                    ·
                      rfl

theorem cell22_2662486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2662486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662486 prefixEnd_2662486 := by exact prefixLift 2662486
  have htrace : WordTrace (prefixWord ++ tailWord_2662486) baseStart_2662486 baseEnd_2662486 := by
    simpa [prefixWord, tailWord_2662486, baseEnd_2662486] using wordTrace_append hprefix tailTrace_2662486
  have hstable : (prefixWord ++ tailWord_2662486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662486).length < 2 ^ (prefixWord ++ tailWord_2662486).sum := by decide
  have hdescent : baseEnd_2662486 < baseStart_2662486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662508 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 1, 5]
def baseStart_2662508 : Nat := 118140960795 + 2662508 * 2 ^ 59
def prefixEnd_2662508 : Nat := 4983230072969 + 3 ^ 40 * 2662508 * 2
def baseEnd_2662508 : Nat := 911430900294116105936903

theorem tailTrace_2662508 : CollatzResearch.WordTrace tailWord_2662508 prefixEnd_2662508 911430900294116105936903 := by
  unfold tailWord_2662508
  simp only [CollatzResearch.WordTrace]
  refine ⟨48554822319097855504694089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64739763092130474006258785 48554822319097855504694089)
  ·
    refine ⟨36416116739323391628520567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48554822319097855504694089 36416116739323391628520567)
    ·
      refine ⟨54624175108985087442780851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36416116739323391628520567 54624175108985087442780851)
      ·
        refine ⟨81936262663477631164171277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54624175108985087442780851 81936262663477631164171277)
        ·
          refine ⟨30726098498804111686564229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81936262663477631164171277 30726098498804111686564229)
          ·
            refine ⟨5761143468525770941230793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30726098498804111686564229 5761143468525770941230793)
            ·
              refine ⟨4320857601394328205923095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5761143468525770941230793 4320857601394328205923095)
              ·
                refine ⟨6481286402091492308884643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4320857601394328205923095 6481286402091492308884643)
                ·
                  refine ⟨9721929603137238463326965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6481286402091492308884643 9721929603137238463326965)
                  ·
                    refine ⟨911430900294116105936903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9721929603137238463326965 911430900294116105936903)
                    ·
                      rfl

theorem cell22_2662508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_2662508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662508 prefixEnd_2662508 := by exact prefixLift 2662508
  have htrace : WordTrace (prefixWord ++ tailWord_2662508) baseStart_2662508 baseEnd_2662508 := by
    simpa [prefixWord, tailWord_2662508, baseEnd_2662508] using wordTrace_append hprefix tailTrace_2662508
  have hstable : (prefixWord ++ tailWord_2662508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662508).length < 2 ^ (prefixWord ++ tailWord_2662508).sum := by decide
  have hdescent : baseEnd_2662508 < baseStart_2662508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662529 : List Nat := [1, 2, 4, 2, 4, 1, 2, 1, 1, 4]
def baseStart_2662529 : Nat := 118140960795 + 2662529 * 2 ^ 59
def prefixEnd_2662529 : Nat := 4983230072969 + 3 ^ 40 * 2662529 * 2
def baseEnd_2662529 : Nat := 911438089023279051161839

theorem tailTrace_2662529 : CollatzResearch.WordTrace tailWord_2662529 prefixEnd_2662529 911438089023279051161839 := by
  unfold tailWord_2662529
  simp only [CollatzResearch.WordTrace]
  refine ⟨97110410571119631595902641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64740273714079754397268427 97110410571119631595902641)
  ·
    refine ⟨72832807928339723696926981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97110410571119631595902641 72832807928339723696926981)
    ·
      refine ⟨13656151486563698193173809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72832807928339723696926981 13656151486563698193173809)
      ·
        refine ⟨10242113614922773644880357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13656151486563698193173809 10242113614922773644880357)
        ·
          refine ⟨1920396302798020058415067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10242113614922773644880357 1920396302798020058415067)
          ·
            refine ⟨2880594454197030087622601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920396302798020058415067 2880594454197030087622601)
            ·
              refine ⟨2160445840647772565716951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2880594454197030087622601 2160445840647772565716951)
              ·
                refine ⟨3240668760971658848575427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2160445840647772565716951 3240668760971658848575427)
                ·
                  refine ⟨4861003141457488272863141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3240668760971658848575427 4861003141457488272863141)
                  ·
                    refine ⟨911438089023279051161839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4861003141457488272863141 911438089023279051161839)
                    ·
                      rfl

theorem cell22_2662529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_2662529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662529 prefixEnd_2662529 := by exact prefixLift 2662529
  have htrace : WordTrace (prefixWord ++ tailWord_2662529) baseStart_2662529 baseEnd_2662529 := by
    simpa [prefixWord, tailWord_2662529, baseEnd_2662529] using wordTrace_append hprefix tailTrace_2662529
  have hstable : (prefixWord ++ tailWord_2662529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662529).length < 2 ^ (prefixWord ++ tailWord_2662529).sum := by decide
  have hdescent : baseEnd_2662529 < baseStart_2662529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662604 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 3, 3]
def baseStart_2662604 : Nat := 118140960795 + 2662604 * 2 ^ 59
def prefixEnd_2662604 : Nat := 4983230072969 + 3 ^ 40 * 2662604 * 2
def baseEnd_2662604 : Nat := 911463763056003855536609

theorem tailTrace_2662604 : CollatzResearch.WordTrace tailWord_2662604 prefixEnd_2662604 911463763056003855536609 := by
  unfold tailWord_2662604
  simp only [CollatzResearch.WordTrace]
  refine ⟨48556573022923959702441433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64742097363898612936588577 48556573022923959702441433)
  ·
    refine ⟨36417429767192969776831075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48556573022923959702441433 36417429767192969776831075)
    ·
      refine ⟨54626144650789454665246613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36417429767192969776831075 54626144650789454665246613)
      ·
        refine ⟨2560600530505755687433435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54626144650789454665246613 2560600530505755687433435)
        ·
          refine ⟨3840900795758633531150153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560600530505755687433435 3840900795758633531150153)
          ·
            refine ⟨2880675596818975148362615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3840900795758633531150153 2880675596818975148362615)
            ·
              refine ⟨4321013395228462722543923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2880675596818975148362615 4321013395228462722543923)
              ·
                refine ⟨6481520092842694083815885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4321013395228462722543923 6481520092842694083815885)
                ·
                  refine ⟨2430570034816010281430957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6481520092842694083815885 2430570034816010281430957)
                  ·
                    refine ⟨911463763056003855536609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2430570034816010281430957 911463763056003855536609)
                    ·
                      rfl

theorem cell22_2662604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_2662604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662604 prefixEnd_2662604 := by exact prefixLift 2662604
  have htrace : WordTrace (prefixWord ++ tailWord_2662604) baseStart_2662604 baseEnd_2662604 := by
    simpa [prefixWord, tailWord_2662604, baseEnd_2662604] using wordTrace_append hprefix tailTrace_2662604
  have hstable : (prefixWord ++ tailWord_2662604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662604).length < 2 ^ (prefixWord ++ tailWord_2662604).sum := by decide
  have hdescent : baseEnd_2662604 < baseStart_2662604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662643 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 1, 5]
def baseStart_2662643 : Nat := 118140960795 + 2662643 * 2 ^ 59
def prefixEnd_2662643 : Nat := 4983230072969 + 3 ^ 40 * 2662643 * 2
def baseEnd_2662643 : Nat := 911477113553020753811489

theorem tailTrace_2662643 : CollatzResearch.WordTrace tailWord_2662643 prefixEnd_2662643 911477113553020753811489 := by
  unfold tailWord_2662643
  simp only [CollatzResearch.WordTrace]
  refine ⟨97114568492706629065552583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64743045661804419377035055 97114568492706629065552583)
  ·
    refine ⟨145671852739059943598328875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97114568492706629065552583 145671852739059943598328875)
    ·
      refine ⟨218507779108589915397493313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145671852739059943598328875 218507779108589915397493313)
      ·
        refine ⟨163880834331442436548119985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218507779108589915397493313 163880834331442436548119985)
        ·
          refine ⟨122910625748581827411089989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163880834331442436548119985 122910625748581827411089989)
          ·
            refine ⟨23045742327859092639579373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122910625748581827411089989 23045742327859092639579373)
            ·
              refine ⟨8642153372947159739842265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23045742327859092639579373 8642153372947159739842265)
              ·
                refine ⟨6481615029710369804881699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8642153372947159739842265 6481615029710369804881699)
                ·
                  refine ⟨9722422544565554707322549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6481615029710369804881699 9722422544565554707322549)
                  ·
                    refine ⟨911477113553020753811489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9722422544565554707322549 911477113553020753811489)
                    ·
                      rfl

theorem cell22_2662643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 5].length) (baseStart_2662643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662643 prefixEnd_2662643 := by exact prefixLift 2662643
  have htrace : WordTrace (prefixWord ++ tailWord_2662643) baseStart_2662643 baseEnd_2662643 := by
    simpa [prefixWord, tailWord_2662643, baseEnd_2662643] using wordTrace_append hprefix tailTrace_2662643
  have hstable : (prefixWord ++ tailWord_2662643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662643).length < 2 ^ (prefixWord ++ tailWord_2662643).sum := by decide
  have hdescent : baseEnd_2662643 < baseStart_2662643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662673 : List Nat := [1, 2, 2, 1, 1, 5, 3, 7]
def baseStart_2662673 : Nat := 118140960795 + 2662673 * 2 ^ 59
def prefixEnd_2662673 : Nat := 4983230072969 + 3 ^ 40 * 2662673 * 2
def baseEnd_2662673 : Nat := 101276375907345630617933

theorem tailTrace_2662673 : CollatzResearch.WordTrace tailWord_2662673 prefixEnd_2662673 101276375907345630617933 := by
  unfold tailWord_2662673
  simp only [CollatzResearch.WordTrace]
  refine ⟨97115662682597944189144673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64743775121731962792763115 97115662682597944189144673)
  ·
    refine ⟨72836747011948458141858505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97115662682597944189144673 72836747011948458141858505)
    ·
      refine ⟨54627560258961343606393879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72836747011948458141858505 54627560258961343606393879)
      ·
        refine ⟨81941340388442015409590819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54627560258961343606393879 81941340388442015409590819)
        ·
          refine ⟨122912010582663023114386229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81941340388442015409590819 122912010582663023114386229)
          ·
            refine ⟨11523000992124658416973709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122912010582663023114386229 11523000992124658416973709)
            ·
              refine ⟨4321125372046746906365141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11523000992124658416973709 4321125372046746906365141)
              ·
                refine ⟨101276375907345630617933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4321125372046746906365141 101276375907345630617933)
                ·
                  rfl

theorem cell22_2662673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 7].length) (baseStart_2662673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662673 prefixEnd_2662673 := by exact prefixLift 2662673
  have htrace : WordTrace (prefixWord ++ tailWord_2662673) baseStart_2662673 baseEnd_2662673 := by
    simpa [prefixWord, tailWord_2662673, baseEnd_2662673] using wordTrace_append hprefix tailTrace_2662673
  have hstable : (prefixWord ++ tailWord_2662673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662673).length < 2 ^ (prefixWord ++ tailWord_2662673).sum := by decide
  have hdescent : baseEnd_2662673 < baseStart_2662673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662692 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_2662692 : Nat := 118140960795 + 2662692 * 2 ^ 59
def prefixEnd_2662692 : Nat := 4983230072969 + 3 ^ 40 * 2662692 * 2
def baseEnd_2662692 : Nat := 911493887254400959336339

theorem tailTrace_2662692 : CollatzResearch.WordTrace tailWord_2662692 prefixEnd_2662692 911493887254400959336339 := by
  unfold tailWord_2662692
  simp only [CollatzResearch.WordTrace]
  refine ⟨48558177834764555217043165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64744237113019406956057553 48558177834764555217043165)
  ·
    refine ⟨18209316688036708206391187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48558177834764555217043165 18209316688036708206391187)
    ·
      refine ⟨27313975032055062309586781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18209316688036708206391187 27313975032055062309586781)
      ·
        refine ⟨10242740637020648366095043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27313975032055062309586781 10242740637020648366095043)
        ·
          refine ⟨15364110955530972549142565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10242740637020648366095043 15364110955530972549142565)
          ·
            refine ⟨2880770804162057352964231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15364110955530972549142565 2880770804162057352964231)
            ·
              refine ⟨4321156206243086029446347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2880770804162057352964231 4321156206243086029446347)
              ·
                refine ⟨6481734309364629044169521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4321156206243086029446347 6481734309364629044169521)
                ·
                  refine ⟨4861300732023471783127141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6481734309364629044169521 4861300732023471783127141)
                  ·
                    refine ⟨911493887254400959336339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4861300732023471783127141 911493887254400959336339)
                    ·
                      rfl

theorem cell22_2662692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_2662692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662692 prefixEnd_2662692 := by exact prefixLift 2662692
  have htrace : WordTrace (prefixWord ++ tailWord_2662692) baseStart_2662692 baseEnd_2662692 := by
    simpa [prefixWord, tailWord_2662692, baseEnd_2662692] using wordTrace_append hprefix tailTrace_2662692
  have hstable : (prefixWord ++ tailWord_2662692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662692).length < 2 ^ (prefixWord ++ tailWord_2662692).sum := by decide
  have hdescent : baseEnd_2662692 < baseStart_2662692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662778 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_2662778 : Nat := 118140960795 + 2662778 * 2 ^ 59
def prefixEnd_2662778 : Nat := 4983230072969 + 3 ^ 40 * 2662778 * 2
def baseEnd_2662778 : Nat := 911523326811925401686075

theorem tailTrace_2662778 : CollatzResearch.WordTrace tailWord_2662778 prefixEnd_2662778 911523326811925401686075 := by
  unfold tailWord_2662778
  simp only [CollatzResearch.WordTrace]
  refine ⟨24279873086804386780429247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64746328231478364747811325 24279873086804386780429247)
  ·
    refine ⟨36419809630206580170643871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24279873086804386780429247 36419809630206580170643871)
    ·
      refine ⟨54629714445309870255965807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36419809630206580170643871 54629714445309870255965807)
      ·
        refine ⟨81944571667964805383948711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54629714445309870255965807 81944571667964805383948711)
        ·
          refine ⟨122916857501947208075923067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81944571667964805383948711 122916857501947208075923067)
          ·
            refine ⟨184375286252920812113884601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122916857501947208075923067 184375286252920812113884601)
            ·
              refine ⟨138281464689690609085413451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184375286252920812113884601 138281464689690609085413451)
              ·
                refine ⟨207422197034535913628120177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138281464689690609085413451 207422197034535913628120177)
                ·
                  refine ⟨155566647775901935221090133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207422197034535913628120177 155566647775901935221090133)
                  ·
                    refine ⟨911523326811925401686075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 155566647775901935221090133 911523326811925401686075)
                    ·
                      rfl

theorem cell22_2662778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_2662778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662778 prefixEnd_2662778 := by exact prefixLift 2662778
  have htrace : WordTrace (prefixWord ++ tailWord_2662778) baseStart_2662778 baseEnd_2662778 := by
    simpa [prefixWord, tailWord_2662778, baseEnd_2662778] using wordTrace_append hprefix tailTrace_2662778
  have hstable : (prefixWord ++ tailWord_2662778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662778).length < 2 ^ (prefixWord ++ tailWord_2662778).sum := by decide
  have hdescent : baseEnd_2662778 < baseStart_2662778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662902 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_2662902 : Nat := 118140960795 + 2662902 * 2 ^ 59
def prefixEnd_2662902 : Nat := 4983230072969 + 3 ^ 40 * 2662902 * 2
def baseEnd_2662902 : Nat := 911565774546030411585695

theorem tailTrace_2662902 : CollatzResearch.WordTrace tailWord_2662902 prefixEnd_2662902 911565774546030411585695 := by
  unfold tailWord_2662902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6070250937423019768701935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64749343332512210866153973 6070250937423019768701935)
  ·
    refine ⟨9105376406134529653052903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6070250937423019768701935 9105376406134529653052903)
    ·
      refine ⟨13658064609201794479579355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9105376406134529653052903 13658064609201794479579355)
      ·
        refine ⟨20487096913802691719369033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13658064609201794479579355 20487096913802691719369033)
        ·
          refine ⟨15365322685352018789526775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20487096913802691719369033 15365322685352018789526775)
          ·
            refine ⟨23047984028028028184290163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15365322685352018789526775 23047984028028028184290163)
            ·
              refine ⟨34571976042042042276435245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23047984028028028184290163 34571976042042042276435245)
              ·
                refine ⟨12964491015765765853663217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34571976042042042276435245 12964491015765765853663217)
                ·
                  refine ⟨9723368261824324390247413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12964491015765765853663217 9723368261824324390247413)
                  ·
                    refine ⟨911565774546030411585695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9723368261824324390247413 911565774546030411585695)
                    ·
                      rfl

theorem cell22_2662902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_2662902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662902 prefixEnd_2662902 := by exact prefixLift 2662902
  have htrace : WordTrace (prefixWord ++ tailWord_2662902) baseStart_2662902 baseEnd_2662902 := by
    simpa [prefixWord, tailWord_2662902, baseEnd_2662902] using wordTrace_append hprefix tailTrace_2662902
  have hstable : (prefixWord ++ tailWord_2662902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662902).length < 2 ^ (prefixWord ++ tailWord_2662902).sum := by decide
  have hdescent : baseEnd_2662902 < baseStart_2662902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662915 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 6]
def baseStart_2662915 : Nat := 118140960795 + 2662915 * 2 ^ 59
def prefixEnd_2662915 : Nat := 4983230072969 + 3 ^ 40 * 2662915 * 2
def baseEnd_2662915 : Nat := 303856741570567570336885

theorem tailTrace_2662915 : CollatzResearch.WordTrace tailWord_2662915 prefixEnd_2662915 303856741570567570336885 := by
  unfold tailWord_2662915
  simp only [CollatzResearch.WordTrace]
  refine ⟨97124489147721219519454199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64749659431814146346302799 97124489147721219519454199)
  ·
    refine ⟨145686733721581829279181299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97124489147721219519454199 145686733721581829279181299)
    ·
      refine ⟨218530100582372743918771949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145686733721581829279181299 218530100582372743918771949)
      ·
        refine ⟨81948787718389778969539481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218530100582372743918771949 81948787718389778969539481)
        ·
          refine ⟨61461590788792334227154611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81948787718389778969539481 61461590788792334227154611)
          ·
            refine ⟨92192386183188501340731917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61461590788792334227154611 92192386183188501340731917)
            ·
              refine ⟨34572144818695688002774469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92192386183188501340731917 34572144818695688002774469)
              ·
                refine ⟨6482277153505441500520213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34572144818695688002774469 6482277153505441500520213)
                ·
                  refine ⟨303856741570567570336885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6482277153505441500520213 303856741570567570336885)
                  ·
                    rfl

theorem cell22_2662915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 6].length) (baseStart_2662915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662915 prefixEnd_2662915 := by exact prefixLift 2662915
  have htrace : WordTrace (prefixWord ++ tailWord_2662915) baseStart_2662915 baseEnd_2662915 := by
    simpa [prefixWord, tailWord_2662915, baseEnd_2662915] using wordTrace_append hprefix tailTrace_2662915
  have hstable : (prefixWord ++ tailWord_2662915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662915).length < 2 ^ (prefixWord ++ tailWord_2662915).sum := by decide
  have hdescent : baseEnd_2662915 < baseStart_2662915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662917 : List Nat := [1, 3, 1, 1, 2, 2, 3, 4, 1, 4]
def baseStart_2662917 : Nat := 118140960795 + 2662917 * 2 ^ 59
def prefixEnd_2662917 : Nat := 4983230072969 + 3 ^ 40 * 2662917 * 2
def baseEnd_2662917 : Nat := 911570909352575372460649

theorem tailTrace_2662917 : CollatzResearch.WordTrace tailWord_2662917 prefixEnd_2662917 911570909352575372460649 := by
  unfold tailWord_2662917
  simp only [CollatzResearch.WordTrace]
  refine ⟨97124562093713973861027005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64749708062475982574018003 97124562093713973861027005)
  ·
    refine ⟨36421710785142740197885127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97124562093713973861027005 36421710785142740197885127)
    ·
      refine ⟨54632566177714110296827691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36421710785142740197885127 54632566177714110296827691)
      ·
        refine ⟨81948849266571165445241537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54632566177714110296827691 81948849266571165445241537)
        ·
          refine ⟨61461636949928374083931153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81948849266571165445241537 61461636949928374083931153)
          ·
            refine ⟨46096227712446280562948365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61461636949928374083931153 46096227712446280562948365)
            ·
              refine ⟨17286085392167355211105637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46096227712446280562948365 17286085392167355211105637)
              ·
                refine ⟨3241141011031379102082307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17286085392167355211105637 3241141011031379102082307)
                ·
                  refine ⟨4861711516547068653123461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241141011031379102082307 4861711516547068653123461)
                  ·
                    refine ⟨911570909352575372460649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4861711516547068653123461 911570909352575372460649)
                    ·
                      rfl

theorem cell22_2662917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_2662917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662917 prefixEnd_2662917 := by exact prefixLift 2662917
  have htrace : WordTrace (prefixWord ++ tailWord_2662917) baseStart_2662917 baseEnd_2662917 := by
    simpa [prefixWord, tailWord_2662917, baseEnd_2662917] using wordTrace_append hprefix tailTrace_2662917
  have hstable : (prefixWord ++ tailWord_2662917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662917).length < 2 ^ (prefixWord ++ tailWord_2662917).sum := by decide
  have hdescent : baseEnd_2662917 < baseStart_2662917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662925 : List Nat := [1, 7, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_2662925 : Nat := 118140960795 + 2662925 * 2 ^ 59
def prefixEnd_2662925 : Nat := 4983230072969 + 3 ^ 40 * 2662925 * 2
def baseEnd_2662925 : Nat := 911573647916066018260625

theorem tailTrace_2662925 : CollatzResearch.WordTrace tailWord_2662925 prefixEnd_2662925 911573647916066018260625 := by
  unfold tailWord_2662925
  simp only [CollatzResearch.WordTrace]
  refine ⟨97124853877684991227318229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64749902585123327484878819 97124853877684991227318229)
  ·
    refine ⟨2276363762758241981890271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 97124853877684991227318229 2276363762758241981890271)
    ·
      refine ⟨3414545644137362972835407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2276363762758241981890271 3414545644137362972835407)
      ·
        refine ⟨5121818466206044459253111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3414545644137362972835407 5121818466206044459253111)
        ·
          refine ⟨7682727699309066688879667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5121818466206044459253111 7682727699309066688879667)
          ·
            refine ⟨11524091548963600033319501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7682727699309066688879667 11524091548963600033319501)
            ·
              refine ⟨4321534330861350012494813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11524091548963600033319501 4321534330861350012494813)
              ·
                refine ⟨1620575374073006254685555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4321534330861350012494813 1620575374073006254685555)
                ·
                  refine ⟨2430863061109509382028333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620575374073006254685555 2430863061109509382028333)
                  ·
                    refine ⟨911573647916066018260625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2430863061109509382028333 911573647916066018260625)
                    ·
                      rfl

theorem cell22_2662925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_2662925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662925 prefixEnd_2662925 := by exact prefixLift 2662925
  have htrace : WordTrace (prefixWord ++ tailWord_2662925) baseStart_2662925 baseEnd_2662925 := by
    simpa [prefixWord, tailWord_2662925, baseEnd_2662925] using wordTrace_append hprefix tailTrace_2662925
  have hstable : (prefixWord ++ tailWord_2662925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662925).length < 2 ^ (prefixWord ++ tailWord_2662925).sum := by decide
  have hdescent : baseEnd_2662925 < baseStart_2662925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662960 : List Nat := [2, 1, 1, 1, 2, 3, 3, 9]
def baseStart_2662960 : Nat := 118140960795 + 2662960 * 2 ^ 59
def prefixEnd_2662960 : Nat := 4983230072969 + 3 ^ 40 * 2662960 * 2
def baseEnd_2662960 : Nat := 101287292125704177070613

theorem tailTrace_2662960 : CollatzResearch.WordTrace tailWord_2662960 prefixEnd_2662960 101287292125704177070613 := by
  unfold tailWord_2662960
  simp only [CollatzResearch.WordTrace]
  refine ⟨48563065216279096102421167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64750753621705461469894889 48563065216279096102421167)
  ·
    refine ⟨72844597824418644153631751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48563065216279096102421167 72844597824418644153631751)
    ·
      refine ⟨109266896736627966230447627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72844597824418644153631751 109266896736627966230447627)
      ·
        refine ⟨163900345104941949345671441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109266896736627966230447627 163900345104941949345671441)
        ·
          refine ⟨122925258828706462009253581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163900345104941949345671441 122925258828706462009253581)
          ·
            refine ⟨46096972060764923253470093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122925258828706462009253581 46096972060764923253470093)
            ·
              refine ⟨17286364522786846220051285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46096972060764923253470093 17286364522786846220051285)
              ·
                refine ⟨101287292125704177070613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17286364522786846220051285 101287292125704177070613)
                ·
                  rfl

theorem cell22_2662960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 9].length) (baseStart_2662960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662960 prefixEnd_2662960 := by exact prefixLift 2662960
  have htrace : WordTrace (prefixWord ++ tailWord_2662960) baseStart_2662960 baseEnd_2662960 := by
    simpa [prefixWord, tailWord_2662960, baseEnd_2662960] using wordTrace_append hprefix tailTrace_2662960
  have hstable : (prefixWord ++ tailWord_2662960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662960).length < 2 ^ (prefixWord ++ tailWord_2662960).sum := by decide
  have hdescent : baseEnd_2662960 < baseStart_2662960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662977 : List Nat := [1, 2, 5, 1, 1, 2, 2, 8]
def baseStart_2662977 : Nat := 118140960795 + 2662977 * 2 ^ 59
def prefixEnd_2662977 : Nat := 4983230072969 + 3 ^ 40 * 2662977 * 2
def baseEnd_2662977 : Nat := 101287938730972801773385

theorem tailTrace_2662977 : CollatzResearch.WordTrace tailWord_2662977 prefixEnd_2662977 101287938730972801773385 := by
  unfold tailWord_2662977
  simp only [CollatzResearch.WordTrace]
  refine ⟨97126750473496604108211185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64751166982331069405474123 97126750473496604108211185)
  ·
    refine ⟨72845062855122453081158389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97126750473496604108211185 72845062855122453081158389)
    ·
      refine ⟨6829224642667729976358599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72845062855122453081158389 6829224642667729976358599)
      ·
        refine ⟨10243836964001594964537899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6829224642667729976358599 10243836964001594964537899)
        ·
          refine ⟨15365755446002392446806849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10243836964001594964537899 15365755446002392446806849)
          ·
            refine ⟨11524316584501794335105137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15365755446002392446806849 11524316584501794335105137)
            ·
              refine ⟨8643237438376345751328853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11524316584501794335105137 8643237438376345751328853)
              ·
                refine ⟨101287938730972801773385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8643237438376345751328853 101287938730972801773385)
                ·
                  rfl

theorem cell22_2662977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 8].length) (baseStart_2662977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662977 prefixEnd_2662977 := by exact prefixLift 2662977
  have htrace : WordTrace (prefixWord ++ tailWord_2662977) baseStart_2662977 baseEnd_2662977 := by
    simpa [prefixWord, tailWord_2662977, baseEnd_2662977] using wordTrace_append hprefix tailTrace_2662977
  have hstable : (prefixWord ++ tailWord_2662977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662977).length < 2 ^ (prefixWord ++ tailWord_2662977).sum := by decide
  have hdescent : baseEnd_2662977 < baseStart_2662977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662992 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 7, 3]
def baseStart_2662992 : Nat := 118140960795 + 2662992 * 2 ^ 59
def prefixEnd_2662992 : Nat := 4983230072969 + 3 ^ 40 * 2662992 * 2
def baseEnd_2662992 : Nat := 911596583385300176835419

theorem tailTrace_2662992 : CollatzResearch.WordTrace tailWord_2662992 prefixEnd_2662992 911596583385300176835419 := by
  unfold tailWord_2662992
  simp only [CollatzResearch.WordTrace]
  refine ⟨48563648784221130835003615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64751531712294841113338153 48563648784221130835003615)
  ·
    refine ⟨72845473176331696252505423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48563648784221130835003615 72845473176331696252505423)
    ·
      refine ⟨109268209764497544378758135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72845473176331696252505423 109268209764497544378758135)
      ·
        refine ⟨163902314646746316568137203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109268209764497544378758135 163902314646746316568137203)
        ·
          refine ⟨245853471970119474852205805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163902314646746316568137203 245853471970119474852205805)
          ·
            refine ⟨92195051988794803069577177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245853471970119474852205805 92195051988794803069577177)
            ·
              refine ⟨69146288991596102302182883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92195051988794803069577177 69146288991596102302182883)
              ·
                refine ⟨103719433487394153453274325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69146288991596102302182883 103719433487394153453274325)
                ·
                  refine ⟨2430924222360800471561117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 103719433487394153453274325 2430924222360800471561117)
                  ·
                    refine ⟨911596583385300176835419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2430924222360800471561117 911596583385300176835419)
                    ·
                      rfl

theorem cell22_2662992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 7, 3].length) (baseStart_2662992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2662992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2662992 prefixEnd_2662992 := by exact prefixLift 2662992
  have htrace : WordTrace (prefixWord ++ tailWord_2662992) baseStart_2662992 baseEnd_2662992 := by
    simpa [prefixWord, tailWord_2662992, baseEnd_2662992] using wordTrace_append hprefix tailTrace_2662992
  have hstable : (prefixWord ++ tailWord_2662992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662992).length < 2 ^ (prefixWord ++ tailWord_2662992).sum := by decide
  have hdescent : baseEnd_2662992 < baseStart_2662992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663026 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_2663026 : Nat := 118140960795 + 2663026 * 2 ^ 59
def prefixEnd_2663026 : Nat := 4983230072969 + 3 ^ 40 * 2663026 * 2
def baseEnd_2663026 : Nat := 911608222280135421485315

theorem tailTrace_2663026 : CollatzResearch.WordTrace tailWord_2663026 prefixEnd_2663026 911608222280135421485315 := by
  unfold tailWord_2663026
  simp only [CollatzResearch.WordTrace]
  refine ⟨24282134412579771369186233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64752358433546056984496621 24282134412579771369186233)
  ·
    refine ⟨18211600809434828526889675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24282134412579771369186233 18211600809434828526889675)
    ·
      refine ⟨27317401214152242790334513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18211600809434828526889675 27317401214152242790334513)
      ·
        refine ⟨20488050910614182092750885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27317401214152242790334513 20488050910614182092750885)
        ·
          refine ⟨3841509545740159142390791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20488050910614182092750885 3841509545740159142390791)
          ·
            refine ⟨5762264318610238713586187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3841509545740159142390791 5762264318610238713586187)
            ·
              refine ⟨8643396477915358070379281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5762264318610238713586187 8643396477915358070379281)
              ·
                refine ⟨6482547358436518552784461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8643396477915358070379281 6482547358436518552784461)
                ·
                  refine ⟨2430955259413694457294173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6482547358436518552784461 2430955259413694457294173)
                  ·
                    refine ⟨911608222280135421485315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2430955259413694457294173 911608222280135421485315)
                    ·
                      rfl

theorem cell22_2663026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_2663026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663026 prefixEnd_2663026 := by exact prefixLift 2663026
  have htrace : WordTrace (prefixWord ++ tailWord_2663026) baseStart_2663026 baseEnd_2663026 := by
    simpa [prefixWord, tailWord_2663026, baseEnd_2663026] using wordTrace_append hprefix tailTrace_2663026
  have hstable : (prefixWord ++ tailWord_2663026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663026).length < 2 ^ (prefixWord ++ tailWord_2663026).sum := by decide
  have hdescent : baseEnd_2663026 < baseStart_2663026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663052 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_2663052 : Nat := 118140960795 + 2663052 * 2 ^ 59
def prefixEnd_2663052 : Nat := 4983230072969 + 3 ^ 40 * 2663052 * 2
def baseEnd_2663052 : Nat := 911617122611480020335235

theorem tailTrace_2663052 : CollatzResearch.WordTrace tailWord_2663052 prefixEnd_2663052 911617122611480020335235 := by
  unfold tailWord_2663052
  simp only [CollatzResearch.WordTrace]
  refine ⟨48564742974112445958595705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64752990632149927944794273 48564742974112445958595705)
  ·
    refine ⟨36423557230584334468946779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48564742974112445958595705 36423557230584334468946779)
    ·
      refine ⟨54635335845876501703420169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36423557230584334468946779 54635335845876501703420169)
      ·
        refine ⟨40976501884407376277565127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54635335845876501703420169 40976501884407376277565127)
        ·
          refine ⟨61464752826611064416347691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40976501884407376277565127 61464752826611064416347691)
          ·
            refine ⟨92197129239916596624521537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61464752826611064416347691 92197129239916596624521537)
            ·
              refine ⟨69147846929937447468391153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92197129239916596624521537 69147846929937447468391153)
              ·
                refine ⟨51860885197453085601293365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69147846929937447468391153 51860885197453085601293365)
                ·
                  refine ⟨4861957987261226775121253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51860885197453085601293365 4861957987261226775121253)
                  ·
                    refine ⟨911617122611480020335235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4861957987261226775121253 911617122611480020335235)
                    ·
                      rfl

theorem cell22_2663052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_2663052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663052 prefixEnd_2663052 := by exact prefixLift 2663052
  have htrace : WordTrace (prefixWord ++ tailWord_2663052) baseStart_2663052 baseEnd_2663052 := by
    simpa [prefixWord, tailWord_2663052, baseEnd_2663052] using wordTrace_append hprefix tailTrace_2663052
  have hstable : (prefixWord ++ tailWord_2663052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663052).length < 2 ^ (prefixWord ++ tailWord_2663052).sum := by decide
  have hdescent : baseEnd_2663052 < baseStart_2663052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663094 : List Nat := [5, 1, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2663094 : Nat := 118140960795 + 2663094 * 2 ^ 59
def prefixEnd_2663094 : Nat := 4983230072969 + 3 ^ 40 * 2663094 * 2
def baseEnd_2663094 : Nat := 911631500069805910785107

theorem tailTrace_2663094 : CollatzResearch.WordTrace tailWord_2663094 prefixEnd_2663094 911631500069805910785107 := by
  unfold tailWord_2663094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6070688613379545818138771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64754011876048488726813557 6070688613379545818138771)
  ·
    refine ⟨9106032920069318727208157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6070688613379545818138771 9106032920069318727208157)
    ·
      refine ⟨3414762345025994522703059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9106032920069318727208157 3414762345025994522703059)
      ·
        refine ⟨5122143517538991784054589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3414762345025994522703059 5122143517538991784054589)
        ·
          refine ⟨1920803819077121919020471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5122143517538991784054589 1920803819077121919020471)
          ·
            refine ⟨2881205728615682878530707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920803819077121919020471 2881205728615682878530707)
            ·
              refine ⟨4321808592923524317796061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2881205728615682878530707 4321808592923524317796061)
              ·
                refine ⟨1620678222346321619173523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4321808592923524317796061 1620678222346321619173523)
                ·
                  refine ⟨2431017333519482428760285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620678222346321619173523 2431017333519482428760285)
                  ·
                    refine ⟨911631500069805910785107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2431017333519482428760285 911631500069805910785107)
                    ·
                      rfl

theorem cell22_2663094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2663094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663094 prefixEnd_2663094 := by exact prefixLift 2663094
  have htrace : WordTrace (prefixWord ++ tailWord_2663094) baseStart_2663094 baseEnd_2663094 := by
    simpa [prefixWord, tailWord_2663094, baseEnd_2663094] using wordTrace_append hprefix tailTrace_2663094
  have hstable : (prefixWord ++ tailWord_2663094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663094).length < 2 ^ (prefixWord ++ tailWord_2663094).sum := by decide
  have hdescent : baseEnd_2663094 < baseStart_2663094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663101 : List Nat := [1, 4, 1, 2, 1, 3, 3, 3, 4]
def baseStart_2663101 : Nat := 118140960795 + 2663101 * 2 ^ 59
def prefixEnd_2663101 : Nat := 4983230072969 + 3 ^ 40 * 2663101 * 2
def baseEnd_2663101 : Nat := 303877965437620075286695

theorem tailTrace_2663101 : CollatzResearch.WordTrace tailWord_2663101 prefixEnd_2663101 303877965437620075286695 := by
  unfold tailWord_2663101
  simp only [CollatzResearch.WordTrace]
  refine ⟨97131273125047373285725157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64754182083364915523816771 97131273125047373285725157)
  ·
    refine ⟨18212113710946382491073467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97131273125047373285725157 18212113710946382491073467)
    ·
      refine ⟨27318170566419573736610201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18212113710946382491073467 27318170566419573736610201)
      ·
        refine ⟨20488627924814680302457651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27318170566419573736610201 20488627924814680302457651)
        ·
          refine ⟨30732941887222020453686477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20488627924814680302457651 30732941887222020453686477)
          ·
            refine ⟨11524853207708257670132429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30732941887222020453686477 11524853207708257670132429)
            ·
              refine ⟨4321819952890596626299661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11524853207708257670132429 4321819952890596626299661)
              ·
                refine ⟨1620682482333973734862373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4321819952890596626299661 1620682482333973734862373)
                ·
                  refine ⟨303877965437620075286695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1620682482333973734862373 303877965437620075286695)
                  ·
                    rfl

theorem cell22_2663101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_2663101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663101 prefixEnd_2663101 := by exact prefixLift 2663101
  have htrace : WordTrace (prefixWord ++ tailWord_2663101) baseStart_2663101 baseEnd_2663101 := by
    simpa [prefixWord, tailWord_2663101, baseEnd_2663101] using wordTrace_append hprefix tailTrace_2663101
  have hstable : (prefixWord ++ tailWord_2663101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663101).length < 2 ^ (prefixWord ++ tailWord_2663101).sum := by decide
  have hdescent : baseEnd_2663101 < baseStart_2663101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663112 : List Nat := [2, 1, 3, 1, 2, 3, 10]
def baseStart_2663112 : Nat := 118140960795 + 2663112 * 2 ^ 59
def prefixEnd_2663112 : Nat := 4983230072969 + 3 ^ 40 * 2663112 * 2
def baseEnd_2663112 : Nat := 33764357845839254216113

theorem tailTrace_2663112 : CollatzResearch.WordTrace tailWord_2663112 prefixEnd_2663112 33764357845839254216113 := by
  unfold tailWord_2663112
  simp only [CollatzResearch.WordTrace]
  refine ⟨48565837164003761082187795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64754449552005014776250393 48565837164003761082187795)
  ·
    refine ⟨72848755746005641623281693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48565837164003761082187795 72848755746005641623281693)
    ·
      refine ⟨27318283404752115608730635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72848755746005641623281693 27318283404752115608730635)
      ·
        refine ⟨40977425107128173413095953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27318283404752115608730635 40977425107128173413095953)
        ·
          refine ⟨30733068830346130059821965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40977425107128173413095953 30733068830346130059821965)
          ·
            refine ⟨11524900811379798772433237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30733068830346130059821965 11524900811379798772433237)
            ·
              refine ⟨33764357845839254216113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11524900811379798772433237 33764357845839254216113)
              ·
                rfl

theorem cell22_2663112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 10].length) (baseStart_2663112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663112 prefixEnd_2663112 := by exact prefixLift 2663112
  have htrace : WordTrace (prefixWord ++ tailWord_2663112) baseStart_2663112 baseEnd_2663112 := by
    simpa [prefixWord, tailWord_2663112, baseEnd_2663112] using wordTrace_append hprefix tailTrace_2663112
  have hstable : (prefixWord ++ tailWord_2663112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663112).length < 2 ^ (prefixWord ++ tailWord_2663112).sum := by decide
  have hdescent : baseEnd_2663112 < baseStart_2663112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663114 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_2663114 : Nat := 118140960795 + 2663114 * 2 ^ 59
def prefixEnd_2663114 : Nat := 4983230072969 + 3 ^ 40 * 2663114 * 2
def baseEnd_2663114 : Nat := 911638346478532525285045

theorem tailTrace_2663114 : CollatzResearch.WordTrace tailWord_2663114 prefixEnd_2663114 911638346478532525285045 := by
  unfold tailWord_2663114
  simp only [CollatzResearch.WordTrace]
  refine ⟨24282936818500069126487099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64754498182666851003965597 24282936818500069126487099)
  ·
    refine ⟨36424405227750103689730649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24282936818500069126487099 36424405227750103689730649)
    ·
      refine ⟨27318303920812577767297987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36424405227750103689730649 27318303920812577767297987)
      ·
        refine ⟨40977455881218866650946981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27318303920812577767297987 40977455881218866650946981)
        ·
          refine ⟨7683272977728537497052559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40977455881218866650946981 7683272977728537497052559)
          ·
            refine ⟨11524909466592806245578839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7683272977728537497052559 11524909466592806245578839)
            ·
              refine ⟨17287364199889209368368259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11524909466592806245578839 17287364199889209368368259)
              ·
                refine ⟨25931046299833814052552389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17287364199889209368368259 25931046299833814052552389)
                ·
                  refine ⟨4862071181218840134853573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25931046299833814052552389 4862071181218840134853573)
                  ·
                    refine ⟨911638346478532525285045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4862071181218840134853573 911638346478532525285045)
                    ·
                      rfl

theorem cell22_2663114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_2663114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663114 prefixEnd_2663114 := by exact prefixLift 2663114
  have htrace : WordTrace (prefixWord ++ tailWord_2663114) baseStart_2663114 baseEnd_2663114 := by
    simpa [prefixWord, tailWord_2663114, baseEnd_2663114] using wordTrace_append hprefix tailTrace_2663114
  have hstable : (prefixWord ++ tailWord_2663114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663114).length < 2 ^ (prefixWord ++ tailWord_2663114).sum := by decide
  have hdescent : baseEnd_2663114 < baseStart_2663114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663116 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 4, 3]
def baseStart_2663116 : Nat := 118140960795 + 2663116 * 2 ^ 59
def prefixEnd_2663116 : Nat := 4983230072969 + 3 ^ 40 * 2663116 * 2
def baseEnd_2663116 : Nat := 911639031119405186735039

theorem tailTrace_2663116 : CollatzResearch.WordTrace tailWord_2663116 prefixEnd_2663116 911639031119405186735039 := by
  unfold tailWord_2663116
  simp only [CollatzResearch.WordTrace]
  refine ⟨48565910109996515423760601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64754546813328687231680801 48565910109996515423760601)
  ·
    refine ⟨36424432582497386567820451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48565910109996515423760601 36424432582497386567820451)
    ·
      refine ⟨54636648873746079851730677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36424432582497386567820451 54636648873746079851730677)
      ·
        refine ⟨5122185831913694986099751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54636648873746079851730677 5122185831913694986099751)
        ·
          refine ⟨7683278747870542479149627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5122185831913694986099751 7683278747870542479149627)
          ·
            refine ⟨11524918121805813718724441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7683278747870542479149627 11524918121805813718724441)
            ·
              refine ⟨8643688591354360289043331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11524918121805813718724441 8643688591354360289043331)
              ·
                refine ⟨12965532887031540433564997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8643688591354360289043331 12965532887031540433564997)
                ·
                  refine ⟨2431037416318413831293437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12965532887031540433564997 2431037416318413831293437)
                  ·
                    refine ⟨911639031119405186735039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2431037416318413831293437 911639031119405186735039)
                    ·
                      rfl

theorem cell22_2663116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_2663116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663116 prefixEnd_2663116 := by exact prefixLift 2663116
  have htrace : WordTrace (prefixWord ++ tailWord_2663116) baseStart_2663116 baseEnd_2663116 := by
    simpa [prefixWord, tailWord_2663116, baseEnd_2663116] using wordTrace_append hprefix tailTrace_2663116
  have hstable : (prefixWord ++ tailWord_2663116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663116).length < 2 ^ (prefixWord ++ tailWord_2663116).sum := by decide
  have hdescent : baseEnd_2663116 < baseStart_2663116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663118 : List Nat := [4, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_2663118 : Nat := 118140960795 + 2663118 * 2 ^ 59
def prefixEnd_2663118 : Nat := 4983230072969 + 3 ^ 40 * 2663118 * 2
def baseEnd_2663118 : Nat := 303879905253425949395011

theorem tailTrace_2663118 : CollatzResearch.WordTrace tailWord_2663118 prefixEnd_2663118 303879905253425949395011 := by
  unfold tailWord_2663118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12141486645748223148636751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64754595443990523459396005 12141486645748223148636751)
  ·
    refine ⟨18212229968622334722955127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12141486645748223148636751 18212229968622334722955127)
    ·
      refine ⟨27318344952933502084432691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18212229968622334722955127 27318344952933502084432691)
      ·
        refine ⟨40977517429400253126649037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27318344952933502084432691 40977517429400253126649037)
        ·
          refine ⟨15366569036025094922493389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40977517429400253126649037 15366569036025094922493389)
          ·
            refine ⟨5762463388509410595935021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15366569036025094922493389 5762463388509410595935021)
            ·
              refine ⟨2160923770691028973475633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5762463388509410595935021 2160923770691028973475633)
              ·
                refine ⟨1620692828018271730106725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2160923770691028973475633 1620692828018271730106725)
                ·
                  refine ⟨303879905253425949395011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1620692828018271730106725 303879905253425949395011)
                  ·
                    rfl

theorem cell22_2663118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_2663118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663118 prefixEnd_2663118 := by exact prefixLift 2663118
  have htrace : WordTrace (prefixWord ++ tailWord_2663118) baseStart_2663118 baseEnd_2663118 := by
    simpa [prefixWord, tailWord_2663118, baseEnd_2663118] using wordTrace_append hprefix tailTrace_2663118
  have hstable : (prefixWord ++ tailWord_2663118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663118).length < 2 ^ (prefixWord ++ tailWord_2663118).sum := by decide
  have hdescent : baseEnd_2663118 < baseStart_2663118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663178 : List Nat := [3, 1, 2, 2, 1, 2, 3, 4, 1, 3]
def baseStart_2663178 : Nat := 118140960795 + 2663178 * 2 ^ 59
def prefixEnd_2663178 : Nat := 4983230072969 + 3 ^ 40 * 2663178 * 2
def baseEnd_2663178 : Nat := 911660254986457691684849

theorem tailTrace_2663178 : CollatzResearch.WordTrace tailWord_2663178 prefixEnd_2663178 911660254986457691684849 := by
  unfold tailWord_2663178
  simp only [CollatzResearch.WordTrace]
  refine ⟨24283520386442103859069547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64756054363845610290852125 24283520386442103859069547)
  ·
    refine ⟨36425280579663155788604321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24283520386442103859069547 36425280579663155788604321)
    ·
      refine ⟨27318960434747366841453241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36425280579663155788604321 27318960434747366841453241)
      ·
        refine ⟨20489220326060525131089931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27318960434747366841453241 20489220326060525131089931)
        ·
          refine ⟨30733830489090787696634897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20489220326060525131089931 30733830489090787696634897)
          ·
            refine ⟨23050372866818090772476173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30733830489090787696634897 23050372866818090772476173)
            ·
              refine ⟨8643889825056784039678565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23050372866818090772476173 8643889825056784039678565)
              ·
                refine ⟨1620729342198147007439731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8643889825056784039678565 1620729342198147007439731)
                ·
                  refine ⟨2431094013297220511159597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620729342198147007439731 2431094013297220511159597)
                  ·
                    refine ⟨911660254986457691684849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2431094013297220511159597 911660254986457691684849)
                    ·
                      rfl

theorem cell22_2663178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_2663178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663178 prefixEnd_2663178 := by exact prefixLift 2663178
  have htrace : WordTrace (prefixWord ++ tailWord_2663178) baseStart_2663178 baseEnd_2663178 := by
    simpa [prefixWord, tailWord_2663178, baseEnd_2663178] using wordTrace_append hprefix tailTrace_2663178
  have hstable : (prefixWord ++ tailWord_2663178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663178).length < 2 ^ (prefixWord ++ tailWord_2663178).sum := by decide
  have hdescent : baseEnd_2663178 < baseStart_2663178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663189 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_2663189 : Nat := 118140960795 + 2663189 * 2 ^ 59
def prefixEnd_2663189 : Nat := 4983230072969 + 3 ^ 40 * 2663189 * 2
def baseEnd_2663189 : Nat := 911664020511257329659815

theorem tailTrace_2663189 : CollatzResearch.WordTrace tailWord_2663189 prefixEnd_2663189 911664020511257329659815 := by
  unfold tailWord_2663189
  simp only [CollatzResearch.WordTrace]
  refine ⟨97134482748728564314928621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64756321832485709543285747 97134482748728564314928621)
  ·
    refine ⟨36425431030773211618098233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97134482748728564314928621 36425431030773211618098233)
    ·
      refine ⟨27319073273079908713573675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36425431030773211618098233 27319073273079908713573675)
      ·
        refine ⟨40978609909619863070360513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27319073273079908713573675 40978609909619863070360513)
        ·
          refine ⟨30733957432214897302770385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40978609909619863070360513 30733957432214897302770385)
          ·
            refine ⟨23050468074161172977077789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30733957432214897302770385 23050468074161172977077789)
            ·
              refine ⟨8643925527810439866404171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23050468074161172977077789 8643925527810439866404171)
              ·
                refine ⟨12965888291715659799606257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8643925527810439866404171 12965888291715659799606257)
                ·
                  refine ⟨9724416218786744849704693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12965888291715659799606257 9724416218786744849704693)
                  ·
                    refine ⟨911664020511257329659815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9724416218786744849704693 911664020511257329659815)
                    ·
                      rfl

theorem cell22_2663189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_2663189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663189 prefixEnd_2663189 := by exact prefixLift 2663189
  have htrace : WordTrace (prefixWord ++ tailWord_2663189) baseStart_2663189 baseEnd_2663189 := by
    simpa [prefixWord, tailWord_2663189, baseEnd_2663189] using wordTrace_append hprefix tailTrace_2663189
  have hstable : (prefixWord ++ tailWord_2663189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663189).length < 2 ^ (prefixWord ++ tailWord_2663189).sum := by decide
  have hdescent : baseEnd_2663189 < baseStart_2663189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663251 : List Nat := [1, 1, 1, 2, 1, 1, 3, 7, 2, 3]
def baseStart_2663251 : Nat := 118140960795 + 2663251 * 2 ^ 59
def prefixEnd_2663251 : Nat := 4983230072969 + 3 ^ 40 * 2663251 * 2
def baseEnd_2663251 : Nat := 911685244378309834609625

theorem tailTrace_2663251 : CollatzResearch.WordTrace tailWord_2663251 prefixEnd_2663251 911685244378309834609625 := by
  unfold tailWord_2663251
  simp only [CollatzResearch.WordTrace]
  refine ⟨97136744074503948903685607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64757829383002632602457071 97136744074503948903685607)
  ·
    refine ⟨145705116111755923355528411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97136744074503948903685607 145705116111755923355528411)
    ·
      refine ⟨218557674167633885033292617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145705116111755923355528411 218557674167633885033292617)
      ·
        refine ⟨163918255625725413774969463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218557674167633885033292617 163918255625725413774969463)
        ·
          refine ⟨245877383438588120662454195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163918255625725413774969463 245877383438588120662454195)
          ·
            refine ⟨368816075157882180993681293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245877383438588120662454195 368816075157882180993681293)
            ·
              refine ⟨138306028184205817872630485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 368816075157882180993681293 138306028184205817872630485)
              ·
                refine ⟨3241547535567323856389777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 138306028184205817872630485 3241547535567323856389777)
                ·
                  refine ⟨2431160651675492892292333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3241547535567323856389777 2431160651675492892292333)
                  ·
                    refine ⟨911685244378309834609625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2431160651675492892292333 911685244378309834609625)
                    ·
                      rfl

theorem cell22_2663251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 3].length) (baseStart_2663251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663251 prefixEnd_2663251 := by exact prefixLift 2663251
  have htrace : WordTrace (prefixWord ++ tailWord_2663251) baseStart_2663251 baseEnd_2663251 := by
    simpa [prefixWord, tailWord_2663251, baseEnd_2663251] using wordTrace_append hprefix tailTrace_2663251
  have hstable : (prefixWord ++ tailWord_2663251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663251).length < 2 ^ (prefixWord ++ tailWord_2663251).sum := by decide
  have hdescent : baseEnd_2663251 < baseStart_2663251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663264 : List Nat := [2, 1, 1, 3, 3, 1, 3, 8]
def baseStart_2663264 : Nat := 118140960795 + 2663264 * 2 ^ 59
def prefixEnd_2663264 : Nat := 4983230072969 + 3 ^ 40 * 2663264 * 2
def baseEnd_2663264 : Nat := 101298854949331348226065

theorem tailTrace_2663264 : CollatzResearch.WordTrace tailWord_2663264 prefixEnd_2663264 101298854949331348226065 := by
  unfold tailWord_2663264
  simp only [CollatzResearch.WordTrace]
  refine ⟨48568609111728426061954423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64758145482304568082605897 48568609111728426061954423)
  ·
    refine ⟨72852913667592639092931635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48568609111728426061954423 72852913667592639092931635)
    ·
      refine ⟨109279370501388958639397453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72852913667592639092931635 109279370501388958639397453)
      ·
        refine ⟨40979763938020859489774045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109279370501388958639397453 40979763938020859489774045)
        ·
          refine ⟨15367411476757822308665267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40979763938020859489774045 15367411476757822308665267)
          ·
            refine ⟨23051117215136733462997901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15367411476757822308665267 23051117215136733462997901)
            ·
              refine ⟨8644168955676275048624213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23051117215136733462997901 8644168955676275048624213)
              ·
                refine ⟨101298854949331348226065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8644168955676275048624213 101298854949331348226065)
                ·
                  rfl

theorem cell22_2663264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 8].length) (baseStart_2663264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663264 prefixEnd_2663264 := by exact prefixLift 2663264
  have htrace : WordTrace (prefixWord ++ tailWord_2663264) baseStart_2663264 baseEnd_2663264 := by
    simpa [prefixWord, tailWord_2663264, baseEnd_2663264] using wordTrace_append hprefix tailTrace_2663264
  have hstable : (prefixWord ++ tailWord_2663264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663264).length < 2 ^ (prefixWord ++ tailWord_2663264).sum := by decide
  have hdescent : baseEnd_2663264 < baseStart_2663264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663296 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 3, 3]
def baseStart_2663296 : Nat := 118140960795 + 2663296 * 2 ^ 59
def prefixEnd_2663296 : Nat := 4983230072969 + 3 ^ 40 * 2663296 * 2
def baseEnd_2663296 : Nat := 911700648797944717234487

theorem tailTrace_2663296 : CollatzResearch.WordTrace tailWord_2663296 prefixEnd_2663296 911700648797944717234487 := by
  unfold tailWord_2663296
  simp only [CollatzResearch.WordTrace]
  refine ⟨48569192679670460794536871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64758923572893947726049161 48569192679670460794536871)
  ·
    refine ⟨72853789019505691191805307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48569192679670460794536871 72853789019505691191805307)
    ·
      refine ⟨109280683529258536787707961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72853789019505691191805307 109280683529258536787707961)
      ·
        refine ⟨81960512646943902590780971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109280683529258536787707961 81960512646943902590780971)
        ·
          refine ⟨122940768970415853886171457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81960512646943902590780971 122940768970415853886171457)
          ·
            refine ⟨92205576727811890414628593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122940768970415853886171457 92205576727811890414628593)
            ·
              refine ⟨69154182545858917810971445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92205576727811890414628593 69154182545858917810971445)
              ·
                refine ⟨6483204613674273544778573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69154182545858917810971445 6483204613674273544778573)
                ·
                  refine ⟨2431201730127852579291965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6483204613674273544778573 2431201730127852579291965)
                  ·
                    refine ⟨911700648797944717234487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2431201730127852579291965 911700648797944717234487)
                    ·
                      rfl

theorem cell22_2663296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 3, 3].length) (baseStart_2663296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663296 prefixEnd_2663296 := by exact prefixLift 2663296
  have htrace : WordTrace (prefixWord ++ tailWord_2663296) baseStart_2663296 baseEnd_2663296 := by
    simpa [prefixWord, tailWord_2663296, baseEnd_2663296] using wordTrace_append hprefix tailTrace_2663296
  have hstable : (prefixWord ++ tailWord_2663296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663296).length < 2 ^ (prefixWord ++ tailWord_2663296).sum := by decide
  have hdescent : baseEnd_2663296 < baseStart_2663296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663371 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 6]
def baseStart_2663371 : Nat := 118140960795 + 2663371 * 2 ^ 59
def prefixEnd_2663371 : Nat := 4983230072969 + 3 ^ 40 * 2663371 * 2
def baseEnd_2663371 : Nat := 303908774276889840536419

theorem tailTrace_2663371 : CollatzResearch.WordTrace tailWord_2663371 prefixEnd_2663371 303908774276889840536419 := by
  unfold tailWord_2663371
  simp only [CollatzResearch.WordTrace]
  refine ⟨97141120834069209398053967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64760747222712806265369311 97141120834069209398053967)
  ·
    refine ⟨145711681251103814097080951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97141120834069209398053967 145711681251103814097080951)
    ·
      refine ⟨218567521876655721145621427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145711681251103814097080951 218567521876655721145621427)
      ·
        refine ⟨327851282814983581718432141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218567521876655721145621427 327851282814983581718432141)
        ·
          refine ⟨122944231055618843144412053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327851282814983581718432141 122944231055618843144412053)
          ·
            refine ⟨5763010830732133272394315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122944231055618843144412053 5763010830732133272394315)
            ·
              refine ⟨8644516246098199908591473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5763010830732133272394315 8644516246098199908591473)
              ·
                refine ⟨6483387184573649931443605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8644516246098199908591473 6483387184573649931443605)
                ·
                  refine ⟨303908774276889840536419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6483387184573649931443605 303908774276889840536419)
                  ·
                    rfl

theorem cell22_2663371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 6].length) (baseStart_2663371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663371 prefixEnd_2663371 := by exact prefixLift 2663371
  have htrace : WordTrace (prefixWord ++ tailWord_2663371) baseStart_2663371 baseEnd_2663371 := by
    simpa [prefixWord, tailWord_2663371, baseEnd_2663371] using wordTrace_append hprefix tailTrace_2663371
  have hstable : (prefixWord ++ tailWord_2663371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663371).length < 2 ^ (prefixWord ++ tailWord_2663371).sum := by decide
  have hdescent : baseEnd_2663371 < baseStart_2663371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663431 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2663431 : Nat := 118140960795 + 2663431 * 2 ^ 59
def prefixEnd_2663431 : Nat := 4983230072969 + 3 ^ 40 * 2663431 * 2
def baseEnd_2663431 : Nat := 911746862056849365109073

theorem tailTrace_2663431 : CollatzResearch.WordTrace tailWord_2663431 prefixEnd_2663431 911746862056849365109073 := by
  unfold tailWord_2663431
  simp only [CollatzResearch.WordTrace]
  refine ⟨97143309213851839645238147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64762206142567893096825431 97143309213851839645238147)
  ·
    refine ⟨145714963820777759467857221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97143309213851839645238147 145714963820777759467857221)
    ·
      refine ⟨27321555716395829900223229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145714963820777759467857221 27321555716395829900223229)
      ·
        refine ⟨10245583393648436212583711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27321555716395829900223229 10245583393648436212583711)
        ·
          refine ⟨15368375090472654318875567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10245583393648436212583711 15368375090472654318875567)
          ·
            refine ⟨23052562635708981478313351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15368375090472654318875567 23052562635708981478313351)
            ·
              refine ⟨34578843953563472217470027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23052562635708981478313351 34578843953563472217470027)
              ·
                refine ⟨51868265930345208326205041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34578843953563472217470027 51868265930345208326205041)
                ·
                  refine ⟨38901199447758906244653781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51868265930345208326205041 38901199447758906244653781)
                  ·
                    refine ⟨911746862056849365109073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38901199447758906244653781 911746862056849365109073)
                    ·
                      rfl

theorem cell22_2663431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2663431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663431 prefixEnd_2663431 := by exact prefixLift 2663431
  have htrace : WordTrace (prefixWord ++ tailWord_2663431) baseStart_2663431 baseEnd_2663431 := by
    simpa [prefixWord, tailWord_2663431, baseEnd_2663431] using wordTrace_append hprefix tailTrace_2663431
  have hstable : (prefixWord ++ tailWord_2663431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663431).length < 2 ^ (prefixWord ++ tailWord_2663431).sum := by decide
  have hdescent : baseEnd_2663431 < baseStart_2663431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663461 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 7]
def baseStart_2663461 : Nat := 118140960795 + 2663461 * 2 ^ 59
def prefixEnd_2663461 : Nat := 4983230072969 + 3 ^ 40 * 2663461 * 2
def baseEnd_2663461 : Nat := 303919043889979762286327

theorem tailTrace_2663461 : CollatzResearch.WordTrace tailWord_2663461 prefixEnd_2663461 303919043889979762286327 := by
  unfold tailWord_2663461
  simp only [CollatzResearch.WordTrace]
  refine ⟨97144403403743154768830237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64762935602495436512553491 97144403403743154768830237)
  ·
    refine ⟨36429151276403683038311339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97144403403743154768830237 36429151276403683038311339)
    ·
      refine ⟨54643726914605524557467009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36429151276403683038311339 54643726914605524557467009)
      ·
        refine ⟨40982795185954143418100257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54643726914605524557467009 40982795185954143418100257)
        ·
          refine ⟨30737096389465607563575193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40982795185954143418100257 30737096389465607563575193)
          ·
            refine ⟨23052822292099205672681395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30737096389465607563575193 23052822292099205672681395)
            ·
              refine ⟨34579233438148808509022093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23052822292099205672681395 34579233438148808509022093)
              ·
                refine ⟨12967212539305803190883285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34579233438148808509022093 12967212539305803190883285)
                ·
                  refine ⟨303919043889979762286327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12967212539305803190883285 303919043889979762286327)
                  ·
                    rfl

theorem cell22_2663461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_2663461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663461 prefixEnd_2663461 := by exact prefixLift 2663461
  have htrace : WordTrace (prefixWord ++ tailWord_2663461) baseStart_2663461 baseEnd_2663461 := by
    simpa [prefixWord, tailWord_2663461, baseEnd_2663461] using wordTrace_append hprefix tailTrace_2663461
  have hstable : (prefixWord ++ tailWord_2663461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663461).length < 2 ^ (prefixWord ++ tailWord_2663461).sum := by decide
  have hdescent : baseEnd_2663461 < baseStart_2663461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663557 : List Nat := [1, 3, 1, 1, 6, 1, 2, 3, 4]
def baseStart_2663557 : Nat := 118140960795 + 2663557 * 2 ^ 59
def prefixEnd_2663557 : Nat := 4983230072969 + 3 ^ 40 * 2663557 * 2
def baseEnd_2663557 : Nat := 303929998143942345486229

theorem tailTrace_2663557 : CollatzResearch.WordTrace tailWord_2663557 prefixEnd_2663557 303929998143942345486229 := by
  unfold tailWord_2663557
  simp only [CollatzResearch.WordTrace]
  refine ⟨97147904811395363164324925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64765269874263575442883283 97147904811395363164324925)
  ·
    refine ⟨36430464304273261186621847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97147904811395363164324925 36430464304273261186621847)
    ·
      refine ⟨54645696456409891779932771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36430464304273261186621847 54645696456409891779932771)
      ·
        refine ⟨81968544684614837669899157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54645696456409891779932771 81968544684614837669899157)
        ·
          refine ⟨3842275532091320515776523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81968544684614837669899157 3842275532091320515776523)
          ·
            refine ⟨5763413298136980773664785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3842275532091320515776523 5763413298136980773664785)
            ·
              refine ⟨4322559973602735580248589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5763413298136980773664785 4322559973602735580248589)
              ·
                refine ⟨1620959990101025842593221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4322559973602735580248589 1620959990101025842593221)
                ·
                  refine ⟨303929998143942345486229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1620959990101025842593221 303929998143942345486229)
                  ·
                    rfl

theorem cell22_2663557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_2663557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663557 prefixEnd_2663557 := by exact prefixLift 2663557
  have htrace : WordTrace (prefixWord ++ tailWord_2663557) baseStart_2663557 baseEnd_2663557 := by
    simpa [prefixWord, tailWord_2663557, baseEnd_2663557] using wordTrace_append hprefix tailTrace_2663557
  have hstable : (prefixWord ++ tailWord_2663557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663557).length < 2 ^ (prefixWord ++ tailWord_2663557).sum := by decide
  have hdescent : baseEnd_2663557 < baseStart_2663557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663613 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 7]
def baseStart_2663613 : Nat := 118140960795 + 2663613 * 2 ^ 59
def prefixEnd_2663613 : Nat := 4983230072969 + 3 ^ 40 * 2663613 * 2
def baseEnd_2663613 : Nat := 303936388125420519019505

theorem tailTrace_2663613 : CollatzResearch.WordTrace tailWord_2663613 prefixEnd_2663613 303936388125420519019505 := by
  unfold tailWord_2663613
  simp only [CollatzResearch.WordTrace]
  refine ⟨97149947299192484728363493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64766631532794989818908995 97149947299192484728363493)
  ·
    refine ⟨18215615118598590886568155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97149947299192484728363493 18215615118598590886568155)
    ·
      refine ⟨27323422677897886329852233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18215615118598590886568155 27323422677897886329852233)
      ·
        refine ⟨20492567008423414747389175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27323422677897886329852233 20492567008423414747389175)
        ·
          refine ⟨30738850512635122121083763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20492567008423414747389175 30738850512635122121083763)
          ·
            refine ⟨46108275768952683181625645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30738850512635122121083763 46108275768952683181625645)
            ·
              refine ⟨17290603413357256193109617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46108275768952683181625645 17290603413357256193109617)
              ·
                refine ⟨12967952560017942144832213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17290603413357256193109617 12967952560017942144832213)
                ·
                  refine ⟨303936388125420519019505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12967952560017942144832213 303936388125420519019505)
                  ·
                    rfl

theorem cell22_2663613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_2663613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663613 prefixEnd_2663613 := by exact prefixLift 2663613
  have htrace : WordTrace (prefixWord ++ tailWord_2663613) baseStart_2663613 baseEnd_2663613 := by
    simpa [prefixWord, tailWord_2663613, baseEnd_2663613] using wordTrace_append hprefix tailTrace_2663613
  have hstable : (prefixWord ++ tailWord_2663613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663613).length < 2 ^ (prefixWord ++ tailWord_2663613).sum := by decide
  have hdescent : baseEnd_2663613 < baseStart_2663613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663660 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_2663660 : Nat := 118140960795 + 2663660 * 2 ^ 59
def prefixEnd_2663660 : Nat := 4983230072969 + 3 ^ 40 * 2663660 * 2
def baseEnd_2663660 : Nat := 911825253436769101133371

theorem tailTrace_2663660 : CollatzResearch.WordTrace tailWord_2663660 prefixEnd_2663660 911825253436769101133371 := by
  unfold tailWord_2663660
  simp only [CollatzResearch.WordTrace]
  refine ⟨48575830765011105877662217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64767774353348141170216289 48575830765011105877662217)
  ·
    refine ⟨36431873073758329408246663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48575830765011105877662217 36431873073758329408246663)
    ·
      refine ⟨54647809610637494112369995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36431873073758329408246663 54647809610637494112369995)
      ·
        refine ⟨81971714415956241168554993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54647809610637494112369995 81971714415956241168554993)
        ·
          refine ⟨61478785811967180876416245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81971714415956241168554993 61478785811967180876416245)
          ·
            refine ⟨5763636169871923207164023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61478785811967180876416245 5763636169871923207164023)
            ·
              refine ⟨8645454254807884810746035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5763636169871923207164023 8645454254807884810746035)
              ·
                refine ⟨12968181382211827216119053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8645454254807884810746035 12968181382211827216119053)
                ·
                  refine ⟨4863068018329435206044645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12968181382211827216119053 4863068018329435206044645)
                  ·
                    refine ⟨911825253436769101133371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4863068018329435206044645 911825253436769101133371)
                    ·
                      rfl

theorem cell22_2663660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_2663660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663660 prefixEnd_2663660 := by exact prefixLift 2663660
  have htrace : WordTrace (prefixWord ++ tailWord_2663660) baseStart_2663660 baseEnd_2663660 := by
    simpa [prefixWord, tailWord_2663660, baseEnd_2663660] using wordTrace_append hprefix tailTrace_2663660
  have hstable : (prefixWord ++ tailWord_2663660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663660).length < 2 ^ (prefixWord ++ tailWord_2663660).sum := by decide
  have hdescent : baseEnd_2663660 < baseStart_2663660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663692 : List Nat := [2, 2, 1, 2, 2, 4, 1, 4, 4]
def baseStart_2663692 : Nat := 118140960795 + 2663692 * 2 ^ 59
def prefixEnd_2663692 : Nat := 4983230072969 + 3 ^ 40 * 2663692 * 2
def baseEnd_2663692 : Nat := 303945402563577228111091

theorem tailTrace_2663692 : CollatzResearch.WordTrace tailWord_2663692 prefixEnd_2663692 303945402563577228111091 := by
  unfold tailWord_2663692
  simp only [CollatzResearch.WordTrace]
  refine ⟨48576414332953140610244665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64768552443937520813659553 48576414332953140610244665)
  ·
    refine ⟨36432310749714855457683499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48576414332953140610244665 36432310749714855457683499)
    ·
      refine ⟨54648466124572283186525249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36432310749714855457683499 54648466124572283186525249)
      ·
        refine ⟨40986349593429212389893937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54648466124572283186525249 40986349593429212389893937)
        ·
          refine ⟨30739762195071909292420453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40986349593429212389893937 30739762195071909292420453)
          ·
            refine ⟨5763705411575982992328835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30739762195071909292420453 5763705411575982992328835)
            ·
              refine ⟨8645558117363974488493253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5763705411575982992328835 8645558117363974488493253)
              ·
                refine ⟨1621042147005745216592485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8645558117363974488493253 1621042147005745216592485)
                ·
                  refine ⟨303945402563577228111091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1621042147005745216592485 303945402563577228111091)
                  ·
                    rfl

theorem cell22_2663692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_2663692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663692 prefixEnd_2663692 := by exact prefixLift 2663692
  have htrace : WordTrace (prefixWord ++ tailWord_2663692) baseStart_2663692 baseEnd_2663692 := by
    simpa [prefixWord, tailWord_2663692, baseEnd_2663692] using wordTrace_append hprefix tailTrace_2663692
  have hstable : (prefixWord ++ tailWord_2663692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663692).length < 2 ^ (prefixWord ++ tailWord_2663692).sum := by decide
  have hdescent : baseEnd_2663692 < baseStart_2663692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663722 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2663722 : Nat := 118140960795 + 2663722 * 2 ^ 59
def prefixEnd_2663722 : Nat := 4983230072969 + 3 ^ 40 * 2663722 * 2
def baseEnd_2663722 : Nat := 911846477303821606083181

theorem tailTrace_2663722 : CollatzResearch.WordTrace tailWord_2663722 prefixEnd_2663722 911846477303821606083181 := by
  unfold tailWord_2663722
  simp only [CollatzResearch.WordTrace]
  refine ⟨24288480713949399086020355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64769281903865064229387613 24288480713949399086020355)
  ·
    refine ⟨36432721070924098629030533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24288480713949399086020355 36432721070924098629030533)
    ·
      refine ⟨6831135200798268492943225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36432721070924098629030533 6831135200798268492943225)
      ·
        refine ⟨5123351400598701369707419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6831135200798268492943225 5123351400598701369707419)
        ·
          refine ⟨7685027100898052054561129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5123351400598701369707419 7685027100898052054561129)
          ·
            refine ⟨5763770325673539040920847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7685027100898052054561129 5763770325673539040920847)
            ·
              refine ⟨8645655488510308561381271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5763770325673539040920847 8645655488510308561381271)
              ·
                refine ⟨12968483232765462842071907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8645655488510308561381271 12968483232765462842071907)
                ·
                  refine ⟨19452724849148194263107861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12968483232765462842071907 19452724849148194263107861)
                  ·
                    refine ⟨911846477303821606083181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19452724849148194263107861 911846477303821606083181)
                    ·
                      rfl

theorem cell22_2663722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2663722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663722 prefixEnd_2663722 := by exact prefixLift 2663722
  have htrace : WordTrace (prefixWord ++ tailWord_2663722) baseStart_2663722 baseEnd_2663722 := by
    simpa [prefixWord, tailWord_2663722, baseEnd_2663722] using wordTrace_append hprefix tailTrace_2663722
  have hstable : (prefixWord ++ tailWord_2663722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663722).length < 2 ^ (prefixWord ++ tailWord_2663722).sum := by decide
  have hdescent : baseEnd_2663722 < baseStart_2663722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663842 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2663842 : Nat := 118140960795 + 2663842 * 2 ^ 59
def prefixEnd_2663842 : Nat := 4983230072969 + 3 ^ 40 * 2663842 * 2
def baseEnd_2663842 : Nat := 911887555756181293082813

theorem tailTrace_2663842 : CollatzResearch.WordTrace tailWord_2663842 prefixEnd_2663842 911887555756181293082813 := by
  unfold tailWord_2663842
  simp only [CollatzResearch.WordTrace]
  refine ⟨24289574903840714209612445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64772199743575237892299853 24289574903840714209612445)
  ·
    refine ⟨9108590588940267828604667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24289574903840714209612445 9108590588940267828604667)
    ·
      refine ⟨13662885883410401742907001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9108590588940267828604667 13662885883410401742907001)
      ·
        refine ⟨10247164412557801307180251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13662885883410401742907001 10247164412557801307180251)
        ·
          refine ⟨15370746618836701960770377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10247164412557801307180251 15370746618836701960770377)
          ·
            refine ⟨11528059964127526470577783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15370746618836701960770377 11528059964127526470577783)
            ·
              refine ⟨17292089946191289705866675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11528059964127526470577783 17292089946191289705866675)
              ·
                refine ⟨25938134919286934558800013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17292089946191289705866675 25938134919286934558800013)
                ·
                  refine ⟨9726800594732600459550005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25938134919286934558800013 9726800594732600459550005)
                  ·
                    refine ⟨911887555756181293082813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9726800594732600459550005 911887555756181293082813)
                    ·
                      rfl

theorem cell22_2663842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2663842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663842 prefixEnd_2663842 := by exact prefixLift 2663842
  have htrace : WordTrace (prefixWord ++ tailWord_2663842) baseStart_2663842 baseEnd_2663842 := by
    simpa [prefixWord, tailWord_2663842, baseEnd_2663842] using wordTrace_append hprefix tailTrace_2663842
  have hstable : (prefixWord ++ tailWord_2663842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663842).length < 2 ^ (prefixWord ++ tailWord_2663842).sum := by decide
  have hdescent : baseEnd_2663842 < baseStart_2663842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663857 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 2, 4]
def baseStart_2663857 : Nat := 118140960795 + 2663857 * 2 ^ 59
def prefixEnd_2663857 : Nat := 4983230072969 + 3 ^ 40 * 2663857 * 2
def baseEnd_2663857 : Nat := 911892690562726253957767

theorem tailTrace_2663857 : CollatzResearch.WordTrace tailWord_2663857 prefixEnd_2663857 911892690562726253957767 := by
  unfold tailWord_2663857
  simp only [CollatzResearch.WordTrace]
  refine ⟨97158846710308514400245825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64772564473539009600163883 97158846710308514400245825)
  ·
    refine ⟨72869135032731385800184369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97158846710308514400245825 72869135032731385800184369)
    ·
      refine ⟨54651851274548539350138277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72869135032731385800184369 54651851274548539350138277)
      ·
        refine ⟨10247222113977851128150927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54651851274548539350138277 10247222113977851128150927)
        ·
          refine ⟨15370833170966776692226391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10247222113977851128150927 15370833170966776692226391)
          ·
            refine ⟨23056249756450165038339587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15370833170966776692226391 23056249756450165038339587)
            ·
              refine ⟨34584374634675247557509381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23056249756450165038339587 34584374634675247557509381)
              ·
                refine ⟨6484570244001608917033009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34584374634675247557509381 6484570244001608917033009)
                ·
                  refine ⟨4863427683001206687774757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6484570244001608917033009 4863427683001206687774757)
                  ·
                    refine ⟨911892690562726253957767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4863427683001206687774757 911892690562726253957767)
                    ·
                      rfl

theorem cell22_2663857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_2663857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663857 prefixEnd_2663857 := by exact prefixLift 2663857
  have htrace : WordTrace (prefixWord ++ tailWord_2663857) baseStart_2663857 baseEnd_2663857 := by
    simpa [prefixWord, tailWord_2663857, baseEnd_2663857] using wordTrace_append hprefix tailTrace_2663857
  have hstable : (prefixWord ++ tailWord_2663857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663857).length < 2 ^ (prefixWord ++ tailWord_2663857).sum := by decide
  have hdescent : baseEnd_2663857 < baseStart_2663857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663861 : List Nat := [1, 3, 3, 2, 2, 1, 4, 2, 4]
def baseStart_2663861 : Nat := 118140960795 + 2663861 * 2 ^ 59
def prefixEnd_2663861 : Nat := 4983230072969 + 3 ^ 40 * 2663861 * 2
def baseEnd_2663861 : Nat := 303964686614823858952585

theorem tailTrace_2663861 : CollatzResearch.WordTrace tailWord_2663861 prefixEnd_2663861 303964686614823858952585 := by
  unfold tailWord_2663861
  simp only [CollatzResearch.WordTrace]
  refine ⟨97158992602294023083391437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64772661734862682055594291 97158992602294023083391437)
  ·
    refine ⟨36434622225860258656271789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97158992602294023083391437 36434622225860258656271789)
    ·
      refine ⟨13662983334697596996101921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36434622225860258656271789 13662983334697596996101921)
      ·
        refine ⟨10247237501023197747076441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13662983334697596996101921 10247237501023197747076441)
        ·
          refine ⟨7685428125767398310307331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10247237501023197747076441 7685428125767398310307331)
          ·
            refine ⟨11528142188651097465460997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7685428125767398310307331 11528142188651097465460997)
            ·
              refine ⟨2161526660372080774773937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11528142188651097465460997 2161526660372080774773937)
              ·
                refine ⟨1621144995279060581080453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2161526660372080774773937 1621144995279060581080453)
                ·
                  refine ⟨303964686614823858952585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1621144995279060581080453 303964686614823858952585)
                  ·
                    rfl

theorem cell22_2663861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_2663861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663861 prefixEnd_2663861 := by exact prefixLift 2663861
  have htrace : WordTrace (prefixWord ++ tailWord_2663861) baseStart_2663861 baseEnd_2663861 := by
    simpa [prefixWord, tailWord_2663861, baseEnd_2663861] using wordTrace_append hprefix tailTrace_2663861
  have hstable : (prefixWord ++ tailWord_2663861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663861).length < 2 ^ (prefixWord ++ tailWord_2663861).sum := by decide
  have hdescent : baseEnd_2663861 < baseStart_2663861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663876 : List Nat := [2, 3, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_2663876 : Nat := 118140960795 + 2663876 * 2 ^ 59
def prefixEnd_2663876 : Nat := 4983230072969 + 3 ^ 40 * 2663876 * 2
def baseEnd_2663876 : Nat := 911899194651016537732709

theorem tailTrace_2663876 : CollatzResearch.WordTrace tailWord_2663876 prefixEnd_2663876 911899194651016537732709 := by
  unfold tailWord_2663876
  simp only [CollatzResearch.WordTrace]
  refine ⟨48579769848619840322593741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64773026464826453763458321 48579769848619840322593741)
  ·
    refine ⟨18217413693232440120972653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48579769848619840322593741 18217413693232440120972653)
    ·
      refine ⟨6831530134962165045364745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18217413693232440120972653 6831530134962165045364745)
      ·
        refine ⟨5123647601221623784023559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6831530134962165045364745 5123647601221623784023559)
        ·
          refine ⟨7685471401832435676035339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5123647601221623784023559 7685471401832435676035339)
          ·
            refine ⟨11528207102748653514053009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7685471401832435676035339 11528207102748653514053009)
            ·
              refine ⟨8646155327061490135539757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11528207102748653514053009 8646155327061490135539757)
              ·
                refine ⟨3242308247648058800827409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8646155327061490135539757 3242308247648058800827409)
                ·
                  refine ⟨2431731185736044100620557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3242308247648058800827409 2431731185736044100620557)
                  ·
                    refine ⟨911899194651016537732709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2431731185736044100620557 911899194651016537732709)
                    ·
                      rfl

theorem cell22_2663876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_2663876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663876 prefixEnd_2663876 := by exact prefixLift 2663876
  have htrace : WordTrace (prefixWord ++ tailWord_2663876) baseStart_2663876 baseEnd_2663876 := by
    simpa [prefixWord, tailWord_2663876, baseEnd_2663876] using wordTrace_append hprefix tailTrace_2663876
  have hstable : (prefixWord ++ tailWord_2663876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663876).length < 2 ^ (prefixWord ++ tailWord_2663876).sum := by decide
  have hdescent : baseEnd_2663876 < baseStart_2663876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663887 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 5, 3]
def baseStart_2663887 : Nat := 118140960795 + 2663887 * 2 ^ 59
def prefixEnd_2663887 : Nat := 4983230072969 + 3 ^ 40 * 2663887 * 2
def baseEnd_2663887 : Nat := 911902960175816175707675

theorem tailTrace_2663887 : CollatzResearch.WordTrace tailWord_2663887 prefixEnd_2663887 911902960175816175707675 := by
  unfold tailWord_2663887
  simp only [CollatzResearch.WordTrace]
  refine ⟨97159940900199829523837915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64773293933466553015891943 97159940900199829523837915)
  ·
    refine ⟨145739911350299744285756873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97159940900199829523837915 145739911350299744285756873)
    ·
      refine ⟨109304933512724808214317655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145739911350299744285756873 109304933512724808214317655)
      ·
        refine ⟨163957400269087212321476483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109304933512724808214317655 163957400269087212321476483)
        ·
          refine ⟨245936100403630818482214725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163957400269087212321476483 245936100403630818482214725)
          ·
            refine ⟨46113018825680778465415261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245936100403630818482214725 46113018825680778465415261)
            ·
              refine ⟨17292382059630291924530723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46113018825680778465415261 17292382059630291924530723)
              ·
                refine ⟨25938573089445437886796085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17292382059630291924530723 25938573089445437886796085)
                ·
                  refine ⟨2431741227135509801887133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25938573089445437886796085 2431741227135509801887133)
                  ·
                    refine ⟨911902960175816175707675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2431741227135509801887133 911902960175816175707675)
                    ·
                      rfl

theorem cell22_2663887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 3].length) (baseStart_2663887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663887 prefixEnd_2663887 := by exact prefixLift 2663887
  have htrace : WordTrace (prefixWord ++ tailWord_2663887) baseStart_2663887 baseEnd_2663887 := by
    simpa [prefixWord, tailWord_2663887, baseEnd_2663887] using wordTrace_append hprefix tailTrace_2663887
  have hstable : (prefixWord ++ tailWord_2663887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663887).length < 2 ^ (prefixWord ++ tailWord_2663887).sum := by decide
  have hdescent : baseEnd_2663887 < baseStart_2663887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663921 : List Nat := [1, 2, 2, 2, 3, 2, 2, 4, 1, 3]
def baseStart_2663921 : Nat := 118140960795 + 2663921 * 2 ^ 59
def prefixEnd_2663921 : Nat := 4983230072969 + 3 ^ 40 * 2663921 * 2
def baseEnd_2663921 : Nat := 911914599070651420357571

theorem tailTrace_2663921 : CollatzResearch.WordTrace tailWord_2663921 prefixEnd_2663921 911914599070651420357571 := by
  unfold tailWord_2663921
  simp only [CollatzResearch.WordTrace]
  refine ⟨97161180982076653330575617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64774120654717768887050411 97161180982076653330575617)
  ·
    refine ⟨72870885736557489997931713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97161180982076653330575617 72870885736557489997931713)
    ·
      refine ⟨54653164302418117498448785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72870885736557489997931713 54653164302418117498448785)
      ·
        refine ⟨40989873226813588123836589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54653164302418117498448785 40989873226813588123836589)
        ·
          refine ⟨15371202460055095546438721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40989873226813588123836589 15371202460055095546438721)
          ·
            refine ⟨11528401845041321659829041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15371202460055095546438721 11528401845041321659829041)
            ·
              refine ⟨8646301383780991244871781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11528401845041321659829041 8646301383780991244871781)
              ·
                refine ⟨1621181509458935858413459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8646301383780991244871781 1621181509458935858413459)
                ·
                  refine ⟨2431772264188403787620189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621181509458935858413459 2431772264188403787620189)
                  ·
                    refine ⟨911914599070651420357571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2431772264188403787620189 911914599070651420357571)
                    ·
                      rfl

theorem cell22_2663921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_2663921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663921 prefixEnd_2663921 := by exact prefixLift 2663921
  have htrace : WordTrace (prefixWord ++ tailWord_2663921) baseStart_2663921 baseEnd_2663921 := by
    simpa [prefixWord, tailWord_2663921, baseEnd_2663921] using wordTrace_append hprefix tailTrace_2663921
  have hstable : (prefixWord ++ tailWord_2663921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663921).length < 2 ^ (prefixWord ++ tailWord_2663921).sum := by decide
  have hdescent : baseEnd_2663921 < baseStart_2663921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663932 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_2663932 : Nat := 118140960795 + 2663932 * 2 ^ 59
def prefixEnd_2663932 : Nat := 4983230072969 + 3 ^ 40 * 2663932 * 2
def baseEnd_2663932 : Nat := 911918364595451058332537

theorem tailTrace_2663932 : CollatzResearch.WordTrace tailWord_2663932 prefixEnd_2663932 911918364595451058332537 := by
  unfold tailWord_2663932
  simp only [CollatzResearch.WordTrace]
  refine ⟨48580791092518401104613025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64774388123357868139484033 48580791092518401104613025)
  ·
    refine ⟨36435593319388800828459769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48580791092518401104613025 36435593319388800828459769)
    ·
      refine ⟨27326694989541600621344827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36435593319388800828459769 27326694989541600621344827)
      ·
        refine ⟨40990042484312400932017241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27326694989541600621344827 40990042484312400932017241)
        ·
          refine ⟨30742531863234300699012931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40990042484312400932017241 30742531863234300699012931)
          ·
            refine ⟨46113797794851451048519397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30742531863234300699012931 46113797794851451048519397)
            ·
              refine ⟨8646337086534647071597387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46113797794851451048519397 8646337086534647071597387)
              ·
                refine ⟨12969505629801970607396081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8646337086534647071597387 12969505629801970607396081)
                ·
                  refine ⟨9727129222351477955547061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12969505629801970607396081 9727129222351477955547061)
                  ·
                    refine ⟨911918364595451058332537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9727129222351477955547061 911918364595451058332537)
                    ·
                      rfl

theorem cell22_2663932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_2663932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663932 prefixEnd_2663932 := by exact prefixLift 2663932
  have htrace : WordTrace (prefixWord ++ tailWord_2663932) baseStart_2663932 baseEnd_2663932 := by
    simpa [prefixWord, tailWord_2663932, baseEnd_2663932] using wordTrace_append hprefix tailTrace_2663932
  have hstable : (prefixWord ++ tailWord_2663932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663932).length < 2 ^ (prefixWord ++ tailWord_2663932).sum := by decide
  have hdescent : baseEnd_2663932 < baseStart_2663932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663964 : List Nat := [2, 2, 3, 1, 2, 1, 1, 5, 1, 4]
def baseStart_2663964 : Nat := 118140960795 + 2663964 * 2 ^ 59
def prefixEnd_2663964 : Nat := 4983230072969 + 3 ^ 40 * 2663964 * 2
def baseEnd_2663964 : Nat := 911929318849413641532439

theorem tailTrace_2663964 : CollatzResearch.WordTrace tailWord_2663964 prefixEnd_2663964 911929318849413641532439 := by
  unfold tailWord_2663964
  simp only [CollatzResearch.WordTrace]
  refine ⟨48581374660460435837195473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64775166213947247782927297 48581374660460435837195473)
  ·
    refine ⟨36436030995345326877896605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48581374660460435837195473 36436030995345326877896605)
    ·
      refine ⟨13663511623254497579211227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36436030995345326877896605 13663511623254497579211227)
      ·
        refine ⟨20495267434881746368816841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13663511623254497579211227 20495267434881746368816841)
        ·
          refine ⟨15371450576161309776612631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20495267434881746368816841 15371450576161309776612631)
          ·
            refine ⟨23057175864241964664918947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15371450576161309776612631 23057175864241964664918947)
            ·
              refine ⟨34585763796362946997378421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23057175864241964664918947 34585763796362946997378421)
              ·
                refine ⟨3242415355909026281004227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34585763796362946997378421 3242415355909026281004227)
                ·
                  refine ⟨4863623033863539421506341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242415355909026281004227 4863623033863539421506341)
                  ·
                    refine ⟨911929318849413641532439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4863623033863539421506341 911929318849413641532439)
                    ·
                      rfl

theorem cell22_2663964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_2663964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2663964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2663964 prefixEnd_2663964 := by exact prefixLift 2663964
  have htrace : WordTrace (prefixWord ++ tailWord_2663964) baseStart_2663964 baseEnd_2663964 := by
    simpa [prefixWord, tailWord_2663964, baseEnd_2663964] using wordTrace_append hprefix tailTrace_2663964
  have hstable : (prefixWord ++ tailWord_2663964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663964).length < 2 ^ (prefixWord ++ tailWord_2663964).sum := by decide
  have hdescent : baseEnd_2663964 < baseStart_2663964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664028 : List Nat := [2, 2, 4, 1, 2, 2, 2, 2, 2, 3]
def baseStart_2664028 : Nat := 118140960795 + 2664028 * 2 ^ 59
def prefixEnd_2664028 : Nat := 4983230072969 + 3 ^ 40 * 2664028 * 2
def baseEnd_2664028 : Nat := 911951227357338807932243

theorem tailTrace_2664028 : CollatzResearch.WordTrace tailWord_2664028 prefixEnd_2664028 911951227357338807932243 := by
  unfold tailWord_2664028
  simp only [CollatzResearch.WordTrace]
  refine ⟨48582541796344505302360369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64776722395126007069813825 48582541796344505302360369)
  ·
    refine ⟨36436906347258378976770277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48582541796344505302360369 36436906347258378976770277)
    ·
      refine ⟨6831919940110946058144427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36436906347258378976770277 6831919940110946058144427)
      ·
        refine ⟨10247879910166419087216641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6831919940110946058144427 10247879910166419087216641)
        ·
          refine ⟨7685909932624814315412481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10247879910166419087216641 7685909932624814315412481)
          ·
            refine ⟨5764432449468610736559361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7685909932624814315412481 5764432449468610736559361)
            ·
              refine ⟨4323324337101458052419521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5764432449468610736559361 4323324337101458052419521)
              ·
                refine ⟨3242493252826093539314641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4323324337101458052419521 3242493252826093539314641)
                ·
                  refine ⟨2431869939619570154485981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3242493252826093539314641 2431869939619570154485981)
                  ·
                    refine ⟨911951227357338807932243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2431869939619570154485981 911951227357338807932243)
                    ·
                      rfl

theorem cell22_2664028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_2664028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664028 prefixEnd_2664028 := by exact prefixLift 2664028
  have htrace : WordTrace (prefixWord ++ tailWord_2664028) baseStart_2664028 baseEnd_2664028 := by
    simpa [prefixWord, tailWord_2664028, baseEnd_2664028] using wordTrace_append hprefix tailTrace_2664028
  have hstable : (prefixWord ++ tailWord_2664028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664028).length < 2 ^ (prefixWord ++ tailWord_2664028).sum := by decide
  have hdescent : baseEnd_2664028 < baseStart_2664028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664067 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 3, 7]
def baseStart_2664067 : Nat := 118140960795 + 2664067 * 2 ^ 59
def prefixEnd_2664067 : Nat := 4983230072969 + 3 ^ 40 * 2664067 * 2
def baseEnd_2664067 : Nat := 911964577854355706207123

theorem tailTrace_2664067 : CollatzResearch.WordTrace tailWord_2664067 prefixEnd_2664067 911964577854355706207123 := by
  unfold tailWord_2664067
  simp only [CollatzResearch.WordTrace]
  refine ⟨97166506039547720265390455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64777670693031813510260303 97166506039547720265390455)
  ·
    refine ⟨145749759059321580398085683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97166506039547720265390455 145749759059321580398085683)
    ·
      refine ⟨218624638588982370597128525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145749759059321580398085683 218624638588982370597128525)
      ·
        refine ⟨81984239470868388973923197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218624638588982370597128525 81984239470868388973923197)
        ·
          refine ⟨30744089801575645865221199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81984239470868388973923197 30744089801575645865221199)
          ·
            refine ⟨46116134702363468797831799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30744089801575645865221199 46116134702363468797831799)
            ·
              refine ⟨69174202053545203196747699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46116134702363468797831799 69174202053545203196747699)
              ·
                refine ⟨103761303080317804795121549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69174202053545203196747699 103761303080317804795121549)
                ·
                  refine ⟨38910488655119176798170581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103761303080317804795121549 38910488655119176798170581)
                  ·
                    refine ⟨911964577854355706207123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38910488655119176798170581 911964577854355706207123)
                    ·
                      rfl

theorem cell22_2664067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_2664067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664067 prefixEnd_2664067 := by exact prefixLift 2664067
  have htrace : WordTrace (prefixWord ++ tailWord_2664067) baseStart_2664067 baseEnd_2664067 := by
    simpa [prefixWord, tailWord_2664067, baseEnd_2664067] using wordTrace_append hprefix tailTrace_2664067
  have hstable : (prefixWord ++ tailWord_2664067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664067).length < 2 ^ (prefixWord ++ tailWord_2664067).sum := by decide
  have hdescent : baseEnd_2664067 < baseStart_2664067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664114 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 6]
def baseStart_2664114 : Nat := 118140960795 + 2664114 * 2 ^ 59
def prefixEnd_2664114 : Nat := 4983230072969 + 3 ^ 40 * 2664114 * 2
def baseEnd_2664114 : Nat := 303993555638287750093993

theorem tailTrace_2664114 : CollatzResearch.WordTrace tailWord_2664114 prefixEnd_2664114 303993555638287750093993 := by
  unfold tailWord_2664114
  simp only [CollatzResearch.WordTrace]
  refine ⟨24292055067594361823087849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64778813513584964861567597 24292055067594361823087849)
  ·
    refine ⟨18219041300695771367315887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24292055067594361823087849 18219041300695771367315887)
    ·
      refine ⟨27328561951043657050973831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18219041300695771367315887 27328561951043657050973831)
      ·
        refine ⟨40992842926565485576460747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27328561951043657050973831 40992842926565485576460747)
        ·
          refine ⟨61489264389848228364691121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40992842926565485576460747 61489264389848228364691121)
          ·
            refine ⟨46116948292386171273518341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61489264389848228364691121 46116948292386171273518341)
            ·
              refine ⟨8646927804822407113784689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46116948292386171273518341 8646927804822407113784689)
              ·
                refine ⟨6485195853616805335338517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8646927804822407113784689 6485195853616805335338517)
                ·
                  refine ⟨303993555638287750093993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6485195853616805335338517 303993555638287750093993)
                  ·
                    rfl

theorem cell22_2664114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_2664114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664114 prefixEnd_2664114 := by exact prefixLift 2664114
  have htrace : WordTrace (prefixWord ++ tailWord_2664114) baseStart_2664114 baseEnd_2664114 := by
    simpa [prefixWord, tailWord_2664114, baseEnd_2664114] using wordTrace_append hprefix tailTrace_2664114
  have hstable : (prefixWord ++ tailWord_2664114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664114).length < 2 ^ (prefixWord ++ tailWord_2664114).sum := by decide
  have hdescent : baseEnd_2664114 < baseStart_2664114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664148 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 6]
def baseStart_2664148 : Nat := 118140960795 + 2664148 * 2 ^ 59
def prefixEnd_2664148 : Nat := 4983230072969 + 3 ^ 40 * 2664148 * 2
def baseEnd_2664148 : Nat := 303997435269899498310625

theorem tailTrace_2664148 : CollatzResearch.WordTrace tailWord_2664148 prefixEnd_2664148 303997435269899498310625 := by
  unfold tailWord_2664148
  simp only [CollatzResearch.WordTrace]
  refine ⟨48584730176127135549544549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64779640234836180732726065 48584730176127135549544549)
  ·
    refine ⟨9109636908023837915539603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48584730176127135549544549 9109636908023837915539603)
    ·
      refine ⟨13664455362035756873309405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9109636908023837915539603 13664455362035756873309405)
      ·
        refine ⟨5124170760763408827491027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13664455362035756873309405 5124170760763408827491027)
        ·
          refine ⟨7686256141145113241236541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5124170760763408827491027 7686256141145113241236541)
          ·
            refine ⟨2882346052929417465463703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7686256141145113241236541 2882346052929417465463703)
            ·
              refine ⟨4323519079394126198195555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2882346052929417465463703 4323519079394126198195555)
              ·
                refine ⟨6485278619091189297293333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4323519079394126198195555 6485278619091189297293333)
                ·
                  refine ⟨303997435269899498310625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6485278619091189297293333 303997435269899498310625)
                  ·
                    rfl

theorem cell22_2664148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_2664148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664148 prefixEnd_2664148 := by exact prefixLift 2664148
  have htrace : WordTrace (prefixWord ++ tailWord_2664148) baseStart_2664148 baseEnd_2664148 := by
    simpa [prefixWord, tailWord_2664148, baseEnd_2664148] using wordTrace_append hprefix tailTrace_2664148
  have hstable : (prefixWord ++ tailWord_2664148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664148).length < 2 ^ (prefixWord ++ tailWord_2664148).sum := by decide
  have hdescent : baseEnd_2664148 < baseStart_2664148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664159 : List Nat := [1, 1, 2, 3, 2, 2, 4, 7]
def baseStart_2664159 : Nat := 118140960795 + 2664159 * 2 ^ 59
def prefixEnd_2664159 : Nat := 4983230072969 + 3 ^ 40 * 2664159 * 2
def baseEnd_2664159 : Nat := 101332896814944236989649

theorem tailTrace_2664159 : CollatzResearch.WordTrace tailWord_2664159 prefixEnd_2664159 101332896814944236989649 := by
  unfold tailWord_2664159
  simp only [CollatzResearch.WordTrace]
  refine ⟨97169861555214419977739531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64779907703476279985159687 97169861555214419977739531)
  ·
    refine ⟨145754792332821629966609297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97169861555214419977739531 145754792332821629966609297)
    ·
      refine ⟨109316094249616222474956973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145754792332821629966609297 109316094249616222474956973)
      ·
        refine ⟨40993535343606083428108865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109316094249616222474956973 40993535343606083428108865)
        ·
          refine ⟨30745151507704562571081649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40993535343606083428108865 30745151507704562571081649)
          ·
            refine ⟨23058863630778421928311237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30745151507704562571081649 23058863630778421928311237)
            ·
              refine ⟨4323536930770954111558357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23058863630778421928311237 4323536930770954111558357)
              ·
                refine ⟨101332896814944236989649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4323536930770954111558357 101332896814944236989649)
                ·
                  rfl

theorem cell22_2664159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 7].length) (baseStart_2664159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664159 prefixEnd_2664159 := by exact prefixLift 2664159
  have htrace : WordTrace (prefixWord ++ tailWord_2664159) baseStart_2664159 baseEnd_2664159 := by
    simpa [prefixWord, tailWord_2664159, baseEnd_2664159] using wordTrace_append hprefix tailTrace_2664159
  have hstable : (prefixWord ++ tailWord_2664159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664159).length < 2 ^ (prefixWord ++ tailWord_2664159).sum := by decide
  have hdescent : baseEnd_2664159 < baseStart_2664159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664167 : List Nat := [1, 1, 5, 4, 2, 1, 1, 2, 1, 4]
def baseStart_2664167 : Nat := 118140960795 + 2664167 * 2 ^ 59
def prefixEnd_2664167 : Nat := 4983230072969 + 3 ^ 40 * 2664167 * 2
def baseEnd_2664167 : Nat := 911998809897988778706817

theorem tailTrace_2664167 : CollatzResearch.WordTrace tailWord_2664167 prefixEnd_2664167 911998809897988778706817 := by
  unfold tailWord_2664167
  simp only [CollatzResearch.WordTrace]
  refine ⟨97170153339185437344030755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64780102226123624896020503 97170153339185437344030755)
  ·
    refine ⟨145755230008778156016046133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97170153339185437344030755 145755230008778156016046133)
    ·
      refine ⟨13664552813322952126504325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145755230008778156016046133 13664552813322952126504325)
      ·
        refine ⟨2562103652498053523719561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13664552813322952126504325 2562103652498053523719561)
        ·
          refine ⟨1921577739373540142789671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2562103652498053523719561 1921577739373540142789671)
          ·
            refine ⟨2882366609060310214184507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1921577739373540142789671 2882366609060310214184507)
            ·
              refine ⟨4323549913590465321276761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2882366609060310214184507 4323549913590465321276761)
              ·
                refine ⟨3242662435192848990957571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4323549913590465321276761 3242662435192848990957571)
                ·
                  refine ⟨4863993652789273486436357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242662435192848990957571 4863993652789273486436357)
                  ·
                    refine ⟨911998809897988778706817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4863993652789273486436357 911998809897988778706817)
                    ·
                      rfl

theorem cell22_2664167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_2664167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664167 prefixEnd_2664167 := by exact prefixLift 2664167
  have htrace : WordTrace (prefixWord ++ tailWord_2664167) baseStart_2664167 baseEnd_2664167 := by
    simpa [prefixWord, tailWord_2664167, baseEnd_2664167] using wordTrace_append hprefix tailTrace_2664167
  have hstable : (prefixWord ++ tailWord_2664167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664167).length < 2 ^ (prefixWord ++ tailWord_2664167).sum := by decide
  have hdescent : baseEnd_2664167 < baseStart_2664167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664180 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2664180 : Nat := 118140960795 + 2664180 * 2 ^ 59
def prefixEnd_2664180 : Nat := 4983230072969 + 3 ^ 40 * 2664180 * 2
def baseEnd_2664180 : Nat := 912003260063661078131777

theorem tailTrace_2664180 : CollatzResearch.WordTrace tailWord_2664180 prefixEnd_2664180 912003260063661078131777 := by
  unfold tailWord_2664180
  simp only [CollatzResearch.WordTrace]
  refine ⟨48585313744069170282126997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64780418325425560376169329 48585313744069170282126997)
  ·
    refine ⟨2277436581753242356974703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48585313744069170282126997 2277436581753242356974703)
    ·
      refine ⟨3416154872629863535462055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2277436581753242356974703 3416154872629863535462055)
      ·
        refine ⟨5124232308944795303193083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3416154872629863535462055 5124232308944795303193083)
        ·
          refine ⟨7686348463417192954789625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5124232308944795303193083 7686348463417192954789625)
          ·
            refine ⟨5764761347562894716092219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7686348463417192954789625 5764761347562894716092219)
            ·
              refine ⟨8647142021344342074138329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5764761347562894716092219 8647142021344342074138329)
              ·
                refine ⟨6485356516008256555603747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8647142021344342074138329 6485356516008256555603747)
                ·
                  refine ⟨9728034774012384833405621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6485356516008256555603747 9728034774012384833405621)
                  ·
                    refine ⟨912003260063661078131777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9728034774012384833405621 912003260063661078131777)
                    ·
                      rfl

theorem cell22_2664180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2664180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664180 prefixEnd_2664180 := by exact prefixLift 2664180
  have htrace : WordTrace (prefixWord ++ tailWord_2664180) baseStart_2664180 baseEnd_2664180 := by
    simpa [prefixWord, tailWord_2664180, baseEnd_2664180] using wordTrace_append hprefix tailTrace_2664180
  have hstable : (prefixWord ++ tailWord_2664180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664180).length < 2 ^ (prefixWord ++ tailWord_2664180).sum := by decide
  have hdescent : baseEnd_2664180 < baseStart_2664180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664204 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 7]
def baseStart_2664204 : Nat := 118140960795 + 2664204 * 2 ^ 59
def prefixEnd_2664204 : Nat := 4983230072969 + 3 ^ 40 * 2664204 * 2
def baseEnd_2664204 : Nat := 304003825251377671843901

theorem tailTrace_2664204 : CollatzResearch.WordTrace tailWord_2664204 prefixEnd_2664204 304003825251377671843901 := by
  unfold tailWord_2664204
  simp only [CollatzResearch.WordTrace]
  refine ⟨48585751420025696331563833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64781001893367595108751777 48585751420025696331563833)
  ·
    refine ⟨36439313565019272248672875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48585751420025696331563833 36439313565019272248672875)
    ·
      refine ⟨54658970347528908373009313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36439313565019272248672875 54658970347528908373009313)
      ·
        refine ⟨40994227760646681279756985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54658970347528908373009313 40994227760646681279756985)
        ·
          refine ⟨30745670820485010959817739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40994227760646681279756985 30745670820485010959817739)
          ·
            refine ⟨46118506230727516439726609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30745670820485010959817739 46118506230727516439726609)
            ·
              refine ⟨34588879673045637329794957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46118506230727516439726609 34588879673045637329794957)
              ·
                refine ⟨12970829877392113998673109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34588879673045637329794957 12970829877392113998673109)
                ·
                  refine ⟨304003825251377671843901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12970829877392113998673109 304003825251377671843901)
                  ·
                    rfl

theorem cell22_2664204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_2664204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664204 prefixEnd_2664204 := by exact prefixLift 2664204
  have htrace : WordTrace (prefixWord ++ tailWord_2664204) baseStart_2664204 baseEnd_2664204 := by
    simpa [prefixWord, tailWord_2664204, baseEnd_2664204] using wordTrace_append hprefix tailTrace_2664204
  have hstable : (prefixWord ++ tailWord_2664204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664204).length < 2 ^ (prefixWord ++ tailWord_2664204).sum := by decide
  have hdescent : baseEnd_2664204 < baseStart_2664204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664219 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 2, 5]
def baseStart_2664219 : Nat := 118140960795 + 2664219 * 2 ^ 59
def prefixEnd_2664219 : Nat := 4983230072969 + 3 ^ 40 * 2664219 * 2
def baseEnd_2664219 : Nat := 912016610560677976406657

theorem tailTrace_2664219 : CollatzResearch.WordTrace tailWord_2664219 prefixEnd_2664219 912016610560677976406657 := by
  unfold tailWord_2664219
  simp only [CollatzResearch.WordTrace]
  refine ⟨97172049934997050224923711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64781366623331366816615807 97172049934997050224923711)
  ·
    refine ⟨145758074902495575337385567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97172049934997050224923711 145758074902495575337385567)
    ·
      refine ⟨218637112353743363006078351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145758074902495575337385567 218637112353743363006078351)
      ·
        refine ⟨327955668530615044509117527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218637112353743363006078351 327955668530615044509117527)
        ·
          refine ⟨491933502795922566763676291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327955668530615044509117527 491933502795922566763676291)
          ·
            refine ⟨737900254193883850145514437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491933502795922566763676291 737900254193883850145514437)
            ·
              refine ⟨138356297661353221902283957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 737900254193883850145514437 138356297661353221902283957)
              ·
                refine ⟨12970902905751864553339121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138356297661353221902283957 12970902905751864553339121)
                ·
                  refine ⟨9728177179313898415004341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12970902905751864553339121 9728177179313898415004341)
                  ·
                    refine ⟨912016610560677976406657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9728177179313898415004341 912016610560677976406657)
                    ·
                      rfl

theorem cell22_2664219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 5].length) (baseStart_2664219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664219 prefixEnd_2664219 := by exact prefixLift 2664219
  have htrace : WordTrace (prefixWord ++ tailWord_2664219) baseStart_2664219 baseEnd_2664219 := by
    simpa [prefixWord, tailWord_2664219, baseEnd_2664219] using wordTrace_append hprefix tailTrace_2664219
  have hstable : (prefixWord ++ tailWord_2664219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664219).length < 2 ^ (prefixWord ++ tailWord_2664219).sum := by decide
  have hdescent : baseEnd_2664219 < baseStart_2664219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664255 : List Nat := [1, 1, 2, 2, 7, 1, 1, 2, 5]
def baseStart_2664255 : Nat := 118140960795 + 2664255 * 2 ^ 59
def prefixEnd_2664255 : Nat := 4983230072969 + 3 ^ 40 * 2664255 * 2
def baseEnd_2664255 : Nat := 304009644698795294168849

theorem tailTrace_2664255 : CollatzResearch.WordTrace tailWord_2664255 prefixEnd_2664255 304009644698795294168849 := by
  unfold tailWord_2664255
  simp only [CollatzResearch.WordTrace]
  refine ⟨97173362962866628373234219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64782241975244418915489479 97173362962866628373234219)
  ·
    refine ⟨145760044444299942559851329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97173362962866628373234219 145760044444299942559851329)
    ·
      refine ⟨109320033333224956919888497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145760044444299942559851329 109320033333224956919888497)
      ·
        refine ⟨81990024999918717689916373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109320033333224956919888497 81990024999918717689916373)
        ·
          refine ⟨1921641210935594945857415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 81990024999918717689916373 1921641210935594945857415)
          ·
            refine ⟨2882461816403392418786123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1921641210935594945857415 2882461816403392418786123)
            ·
              refine ⟨4323692724605088628179185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2882461816403392418786123 4323692724605088628179185)
              ·
                refine ⟨3242769543453816471134389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4323692724605088628179185 3242769543453816471134389)
                ·
                  refine ⟨304009644698795294168849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3242769543453816471134389 304009644698795294168849)
                  ·
                    rfl

theorem cell22_2664255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 5].length) (baseStart_2664255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664255 prefixEnd_2664255 := by exact prefixLift 2664255
  have htrace : WordTrace (prefixWord ++ tailWord_2664255) baseStart_2664255 baseEnd_2664255 := by
    simpa [prefixWord, tailWord_2664255, baseEnd_2664255] using wordTrace_append hprefix tailTrace_2664255
  have hstable : (prefixWord ++ tailWord_2664255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664255).length < 2 ^ (prefixWord ++ tailWord_2664255).sum := by decide
  have hdescent : baseEnd_2664255 < baseStart_2664255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664266 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 6]
def baseStart_2664266 : Nat := 118140960795 + 2664266 * 2 ^ 59
def prefixEnd_2664266 : Nat := 4983230072969 + 3 ^ 40 * 2664266 * 2
def baseEnd_2664266 : Nat := 304010899873728506827171

theorem tailTrace_2664266 : CollatzResearch.WordTrace tailWord_2664266 prefixEnd_2664266 304010899873728506827171 := by
  unfold tailWord_2664266
  simp only [CollatzResearch.WordTrace]
  refine ⟨24293441041456694312971163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64782509443884518167923101 24293441041456694312971163)
  ·
    refine ⟨36440161562185041469456745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24293441041456694312971163 36440161562185041469456745)
    ·
      refine ⟨27330121171638781102092559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36440161562185041469456745 27330121171638781102092559)
      ·
        refine ⟨40995181757458171653138839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27330121171638781102092559 40995181757458171653138839)
        ·
          refine ⟨61492772636187257479708259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40995181757458171653138839 61492772636187257479708259)
          ·
            refine ⟨92239158954280886219562389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61492772636187257479708259 92239158954280886219562389)
            ·
              refine ⟨4323710575981916541541987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92239158954280886219562389 4323710575981916541541987)
              ·
                refine ⟨6485565863972874812312981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4323710575981916541541987 6485565863972874812312981)
                ·
                  refine ⟨304010899873728506827171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6485565863972874812312981 304010899873728506827171)
                  ·
                    rfl

theorem cell22_2664266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_2664266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664266 prefixEnd_2664266 := by exact prefixLift 2664266
  have htrace : WordTrace (prefixWord ++ tailWord_2664266) baseStart_2664266 baseEnd_2664266 := by
    simpa [prefixWord, tailWord_2664266, baseEnd_2664266] using wordTrace_append hprefix tailTrace_2664266
  have hstable : (prefixWord ++ tailWord_2664266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664266).length < 2 ^ (prefixWord ++ tailWord_2664266).sum := by decide
  have hdescent : baseEnd_2664266 < baseStart_2664266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664296 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 1, 6]
def baseStart_2664296 : Nat := 118140960795 + 2664296 * 2 ^ 59
def prefixEnd_2664296 : Nat := 4983230072969 + 3 ^ 40 * 2664296 * 2
def baseEnd_2664296 : Nat := 912042969234275442231421

theorem tailTrace_2664296 : CollatzResearch.WordTrace tailWord_2664296 prefixEnd_2664296 912042969234275442231421 := by
  unfold tailWord_2664296
  simp only [CollatzResearch.WordTrace]
  refine ⟨48587429177859046187738371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64783238903812061583651161 48587429177859046187738371)
  ·
    refine ⟨72881143766788569281607557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48587429177859046187738371 72881143766788569281607557)
    ·
      refine ⟨13665214456272856740301417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72881143766788569281607557 13665214456272856740301417)
      ·
        refine ⟨10248910842204642555226063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13665214456272856740301417 10248910842204642555226063)
        ·
          refine ⟨15373366263306963832839095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10248910842204642555226063 15373366263306963832839095)
          ·
            refine ⟨23060049394960445749258643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15373366263306963832839095 23060049394960445749258643)
            ·
              refine ⟨34590074092440668623887965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23060049394960445749258643 34590074092440668623887965)
              ·
                refine ⟨12971277784665250733957987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34590074092440668623887965 12971277784665250733957987)
                ·
                  refine ⟨19456916676997876100936981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12971277784665250733957987 19456916676997876100936981)
                  ·
                    refine ⟨912042969234275442231421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19456916676997876100936981 912042969234275442231421)
                    ·
                      rfl

theorem cell22_2664296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_2664296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664296 prefixEnd_2664296 := by exact prefixLift 2664296
  have htrace : WordTrace (prefixWord ++ tailWord_2664296) baseStart_2664296 baseEnd_2664296 := by
    simpa [prefixWord, tailWord_2664296, baseEnd_2664296] using wordTrace_append hprefix tailTrace_2664296
  have hstable : (prefixWord ++ tailWord_2664296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664296).length < 2 ^ (prefixWord ++ tailWord_2664296).sum := by decide
  have hdescent : baseEnd_2664296 < baseStart_2664296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664300 : List Nat := [2, 2, 1, 1, 4, 4, 1, 3, 4]
def baseStart_2664300 : Nat := 118140960795 + 2664300 * 2 ^ 59
def prefixEnd_2664300 : Nat := 4983230072969 + 3 ^ 40 * 2664300 * 2
def baseEnd_2664300 : Nat := 304014779505340255043803

theorem tailTrace_2664300 : CollatzResearch.WordTrace tailWord_2664300 prefixEnd_2664300 304014779505340255043803 := by
  unfold tailWord_2664300
  simp only [CollatzResearch.WordTrace]
  refine ⟨48587502123851800529311177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64783336165135734039081569 48587502123851800529311177)
  ·
    refine ⟨36440626592888850396983383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48587502123851800529311177 36440626592888850396983383)
    ·
      refine ⟨54660939889333275595475075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36440626592888850396983383 54660939889333275595475075)
      ·
        refine ⟨81991409833999913393212613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54660939889333275595475075 81991409833999913393212613)
        ·
          refine ⟨15373389343874983761227365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81991409833999913393212613 15373389343874983761227365)
          ·
            refine ⟨2882510501976559455230131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15373389343874983761227365 2882510501976559455230131)
            ·
              refine ⟨4323765752964839182845197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2882510501976559455230131 4323765752964839182845197)
              ·
                refine ⟨1621412157361814693566949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4323765752964839182845197 1621412157361814693566949)
                ·
                  refine ⟨304014779505340255043803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1621412157361814693566949 304014779505340255043803)
                  ·
                    rfl

theorem cell22_2664300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_2664300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664300 prefixEnd_2664300 := by exact prefixLift 2664300
  have htrace : WordTrace (prefixWord ++ tailWord_2664300) baseStart_2664300 baseEnd_2664300 := by
    simpa [prefixWord, tailWord_2664300, baseEnd_2664300] using wordTrace_append hprefix tailTrace_2664300
  have hstable : (prefixWord ++ tailWord_2664300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664300).length < 2 ^ (prefixWord ++ tailWord_2664300).sum := by decide
  have hdescent : baseEnd_2664300 < baseStart_2664300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664328 : List Nat := [2, 1, 3, 3, 3, 1, 2, 7]
def baseStart_2664328 : Nat := 118140960795 + 2664328 * 2 ^ 59
def prefixEnd_2664328 : Nat := 4983230072969 + 3 ^ 40 * 2664328 * 2
def baseEnd_2664328 : Nat := 101339324832026447270147

theorem tailTrace_2664328 : CollatzResearch.WordTrace tailWord_2664328 prefixEnd_2664328 101339324832026447270147 := by
  unfold tailWord_2664328
  simp only [CollatzResearch.WordTrace]
  refine ⟨48588012745801080920320819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64784016994401441227094425 48588012745801080920320819)
  ·
    refine ⟨72882019118701621380481229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48588012745801080920320819 72882019118701621380481229)
    ·
      refine ⟨27330757169513108017680461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72882019118701621380481229 27330757169513108017680461)
      ·
        refine ⟨10249033938567415506630173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27330757169513108017680461 10249033938567415506630173)
        ·
          refine ⟨3843387726962780814986315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10249033938567415506630173 3843387726962780814986315)
          ·
            refine ⟨5765081590444171222479473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3843387726962780814986315 5765081590444171222479473)
            ·
              refine ⟨4323811192833128416859605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5765081590444171222479473 4323811192833128416859605)
              ·
                refine ⟨101339324832026447270147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4323811192833128416859605 101339324832026447270147)
                ·
                  rfl

theorem cell22_2664328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 7].length) (baseStart_2664328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664328 prefixEnd_2664328 := by exact prefixLift 2664328
  have htrace : WordTrace (prefixWord ++ tailWord_2664328) baseStart_2664328 baseEnd_2664328 := by
    simpa [prefixWord, tailWord_2664328, baseEnd_2664328] using wordTrace_append hprefix tailTrace_2664328
  have hstable : (prefixWord ++ tailWord_2664328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664328).length < 2 ^ (prefixWord ++ tailWord_2664328).sum := by decide
  have hdescent : baseEnd_2664328 < baseStart_2664328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664366 : List Nat := [4, 1, 5, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2664366 : Nat := 118140960795 + 2664366 * 2 ^ 59
def prefixEnd_2664366 : Nat := 4983230072969 + 3 ^ 40 * 2664366 * 2
def baseEnd_2664366 : Nat := 912066931664818592981207

theorem tailTrace_2664366 : CollatzResearch.WordTrace tailWord_2664366 prefixEnd_2664366 912066931664818592981207 := by
  unfold tailWord_2664366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12147176433183061791315619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64784940976976329553683301 12147176433183061791315619)
  ·
    refine ⟨18220764649774592686973429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12147176433183061791315619 18220764649774592686973429)
    ·
      refine ⟨1708196685916368064403759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18220764649774592686973429 1708196685916368064403759)
      ·
        refine ⟨2562295028874552096605639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1708196685916368064403759 2562295028874552096605639)
        ·
          refine ⟨3843442543311828144908459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2562295028874552096605639 3843442543311828144908459)
          ·
            refine ⟨5765163814967742217362689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3843442543311828144908459 5765163814967742217362689)
            ·
              refine ⟨4323872861225806663022017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5765163814967742217362689 4323872861225806663022017)
              ·
                refine ⟨3242904645919354997266513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4323872861225806663022017 3242904645919354997266513)
                ·
                  refine ⟨2432178484439516247949885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3242904645919354997266513 2432178484439516247949885)
                  ·
                    refine ⟨912066931664818592981207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2432178484439516247949885 912066931664818592981207)
                    ·
                      rfl

theorem cell22_2664366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2664366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664366 prefixEnd_2664366 := by exact prefixLift 2664366
  have htrace : WordTrace (prefixWord ++ tailWord_2664366) baseStart_2664366 baseEnd_2664366 := by
    simpa [prefixWord, tailWord_2664366, baseEnd_2664366] using wordTrace_append hprefix tailTrace_2664366
  have hstable : (prefixWord ++ tailWord_2664366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664366).length < 2 ^ (prefixWord ++ tailWord_2664366).sum := by decide
  have hdescent : baseEnd_2664366 < baseStart_2664366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664371 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 2, 5]
def baseStart_2664371 : Nat := 118140960795 + 2664371 * 2 ^ 59
def prefixEnd_2664371 : Nat := 4983230072969 + 3 ^ 40 * 2664371 * 2
def baseEnd_2664371 : Nat := 912068643267000246606191

theorem tailTrace_2664371 : CollatzResearch.WordTrace tailWord_2664371 prefixEnd_2664371 912068643267000246606191 := by
  unfold tailWord_2664371
  simp only [CollatzResearch.WordTrace]
  refine ⟨97177593830446380184456967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64785062553630920122971311 97177593830446380184456967)
  ·
    refine ⟨145766390745669570276685451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97177593830446380184456967 145766390745669570276685451)
    ·
      refine ⟨218649586118504355415028177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145766390745669570276685451 218649586118504355415028177)
      ·
        refine ⟨163987189588878266561271133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218649586118504355415028177 163987189588878266561271133)
        ·
          refine ⟨61495196095829349960476675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163987189588878266561271133 61495196095829349960476675)
          ·
            refine ⟨92242794143744024940715013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61495196095829349960476675 92242794143744024940715013)
            ·
              refine ⟨17295523901952004676384065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92242794143744024940715013 17295523901952004676384065)
              ·
                refine ⟨12971642926464003507288049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17295523901952004676384065 12971642926464003507288049)
                ·
                  refine ⟨9728732194848002630466037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12971642926464003507288049 9728732194848002630466037)
                  ·
                    refine ⟨912068643267000246606191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9728732194848002630466037 912068643267000246606191)
                    ·
                      rfl

theorem cell22_2664371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 5].length) (baseStart_2664371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664371 prefixEnd_2664371 := by exact prefixLift 2664371
  have htrace : WordTrace (prefixWord ++ tailWord_2664371) baseStart_2664371 baseEnd_2664371 := by
    simpa [prefixWord, tailWord_2664371, baseEnd_2664371] using wordTrace_append hprefix tailTrace_2664371
  have hstable : (prefixWord ++ tailWord_2664371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664371).length < 2 ^ (prefixWord ++ tailWord_2664371).sum := by decide
  have hdescent : baseEnd_2664371 < baseStart_2664371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664373 : List Nat := [1, 3, 3, 2, 1, 2, 1, 4, 5]
def baseStart_2664373 : Nat := 118140960795 + 2664373 * 2 ^ 59
def prefixEnd_2664373 : Nat := 4983230072969 + 3 ^ 40 * 2664373 * 2
def baseEnd_2664373 : Nat := 304023109302624302685395

theorem tailTrace_2664373 : CollatzResearch.WordTrace tailWord_2664373 prefixEnd_2664373 304023109302624302685395 := by
  unfold tailWord_2664373
  simp only [CollatzResearch.WordTrace]
  refine ⟨97177666776439134526029773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64785111184292756350686515 97177666776439134526029773)
  ·
    refine ⟨36441625041164675447261165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97177666776439134526029773 36441625041164675447261165)
    ·
      refine ⟨13665609390436753292722937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36441625041164675447261165 13665609390436753292722937)
      ·
        refine ⟨10249207042827564969542203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13665609390436753292722937 10249207042827564969542203)
        ·
          refine ⟨15373810564241347454313305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10249207042827564969542203 15373810564241347454313305)
          ·
            refine ⟨11530357923181010590734979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15373810564241347454313305 11530357923181010590734979)
            ·
              refine ⟨17295536884771515886102469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11530357923181010590734979 17295536884771515886102469)
              ·
                refine ⟨3242913165894659228644213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17295536884771515886102469 3242913165894659228644213)
                ·
                  refine ⟨304023109302624302685395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3242913165894659228644213 304023109302624302685395)
                  ·
                    rfl

theorem cell22_2664373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_2664373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664373 prefixEnd_2664373 := by exact prefixLift 2664373
  have htrace : WordTrace (prefixWord ++ tailWord_2664373) baseStart_2664373 baseEnd_2664373 := by
    simpa [prefixWord, tailWord_2664373, baseEnd_2664373] using wordTrace_append hprefix tailTrace_2664373
  have hstable : (prefixWord ++ tailWord_2664373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664373).length < 2 ^ (prefixWord ++ tailWord_2664373).sum := by decide
  have hdescent : baseEnd_2664373 < baseStart_2664373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664469 : List Nat := [1, 3, 2, 1, 6, 1, 1, 3, 4]
def baseStart_2664469 : Nat := 118140960795 + 2664469 * 2 ^ 59
def prefixEnd_2664469 : Nat := 4983230072969 + 3 ^ 40 * 2664469 * 2
def baseEnd_2664469 : Nat := 304034063556586885885297

theorem tailTrace_2664469 : CollatzResearch.WordTrace tailWord_2664469 prefixEnd_2664469 304034063556586885885297 := by
  unfold tailWord_2664469
  simp only [CollatzResearch.WordTrace]
  refine ⟨97181168184091342921524461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64787445456060895281016307 97181168184091342921524461)
  ·
    refine ⟨36442938069034253595571673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97181168184091342921524461 36442938069034253595571673)
    ·
      refine ⟨27332203551775690196678755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36442938069034253595571673 27332203551775690196678755)
      ·
        refine ⟨40998305327663535295018133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27332203551775690196678755 40998305327663535295018133)
        ·
          refine ⟨1921795562234228216953975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40998305327663535295018133 1921795562234228216953975)
          ·
            refine ⟨2882693343351342325430963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1921795562234228216953975 2882693343351342325430963)
            ·
              refine ⟨4324040015027013488146445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2882693343351342325430963 4324040015027013488146445)
              ·
                refine ⟨1621515005635130058054917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4324040015027013488146445 1621515005635130058054917)
                ·
                  refine ⟨304034063556586885885297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1621515005635130058054917 304034063556586885885297)
                  ·
                    rfl

theorem cell22_2664469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_2664469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664469 prefixEnd_2664469 := by exact prefixLift 2664469
  have htrace : WordTrace (prefixWord ++ tailWord_2664469) baseStart_2664469 baseEnd_2664469 := by
    simpa [prefixWord, tailWord_2664469, baseEnd_2664469] using wordTrace_append hprefix tailTrace_2664469
  have hstable : (prefixWord ++ tailWord_2664469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664469).length < 2 ^ (prefixWord ++ tailWord_2664469).sum := by decide
  have hdescent : baseEnd_2664469 < baseStart_2664469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664546 : List Nat := [3, 3, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2664546 : Nat := 118140960795 + 2664546 * 2 ^ 59
def prefixEnd_2664546 : Nat := 4983230072969 + 3 ^ 40 * 2664546 * 2
def baseEnd_2664546 : Nat := 912128549343358123480655

theorem tailTrace_2664546 : CollatzResearch.WordTrace tailWord_2664546 prefixEnd_2664546 912128549343358123480655 := by
  unfold tailWord_2664546
  simp only [CollatzResearch.WordTrace]
  refine ⟨24295994151203096268019373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64789317736541590048051661 24295994151203096268019373)
  ·
    refine ⟨9110997806701161100507265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24295994151203096268019373 9110997806701161100507265)
    ·
      refine ⟨6833248355025870825380449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9110997806701161100507265 6833248355025870825380449)
      ·
        refine ⟨5124936266269403119035337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6833248355025870825380449 5124936266269403119035337)
        ·
          refine ⟨3843702199702052339276503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5124936266269403119035337 3843702199702052339276503)
          ·
            refine ⟨5765553299553078508914755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3843702199702052339276503 5765553299553078508914755)
            ·
              refine ⟨8648329949329617763372133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5765553299553078508914755 8648329949329617763372133)
              ·
                refine ⟨1621561865499303330632275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8648329949329617763372133 1621561865499303330632275)
                ·
                  refine ⟨2432342798248954995948413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621561865499303330632275 2432342798248954995948413)
                  ·
                    refine ⟨912128549343358123480655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2432342798248954995948413 912128549343358123480655)
                    ·
                      rfl

theorem cell22_2664546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2664546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664546 prefixEnd_2664546 := by exact prefixLift 2664546
  have htrace : WordTrace (prefixWord ++ tailWord_2664546) baseStart_2664546 baseEnd_2664546 := by
    simpa [prefixWord, tailWord_2664546, baseEnd_2664546] using wordTrace_append hprefix tailTrace_2664546
  have hstable : (prefixWord ++ tailWord_2664546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664546).length < 2 ^ (prefixWord ++ tailWord_2664546).sum := by decide
  have hdescent : baseEnd_2664546 < baseStart_2664546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664553 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 6]
def baseStart_2664553 : Nat := 118140960795 + 2664553 * 2 ^ 59
def prefixEnd_2664553 : Nat := 4983230072969 + 3 ^ 40 * 2664553 * 2
def baseEnd_2664553 : Nat := 304043648528804146185211

theorem tailTrace_2664553 : CollatzResearch.WordTrace tailWord_2664553 prefixEnd_2664553 304043648528804146185211 := by
  unfold tailWord_2664553
  simp only [CollatzResearch.WordTrace]
  refine ⟨97184231915787025267582313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64789487943858016845054875 97184231915787025267582313)
  ·
    refine ⟨72888173936840268950686735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97184231915787025267582313 72888173936840268950686735)
    ·
      refine ⟨109332260905260403426030103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72888173936840268950686735 109332260905260403426030103)
      ·
        refine ⟨163998391357890605139045155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109332260905260403426030103 163998391357890605139045155)
        ·
          refine ⟨245997587036835907708567733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163998391357890605139045155 245997587036835907708567733)
          ·
            refine ⟨23062273784703366347678225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 245997587036835907708567733 23062273784703366347678225)
            ·
              refine ⟨17296705338527524760758669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23062273784703366347678225 17296705338527524760758669)
              ·
                refine ⟨6486264501947821785284501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17296705338527524760758669 6486264501947821785284501)
                ·
                  refine ⟨304043648528804146185211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6486264501947821785284501 304043648528804146185211)
                  ·
                    rfl

theorem cell22_2664553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 6].length) (baseStart_2664553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664553 prefixEnd_2664553 := by exact prefixLift 2664553
  have htrace : WordTrace (prefixWord ++ tailWord_2664553) baseStart_2664553 baseEnd_2664553 := by
    simpa [prefixWord, tailWord_2664553, baseEnd_2664553] using wordTrace_append hprefix tailTrace_2664553
  have hstable : (prefixWord ++ tailWord_2664553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664553).length < 2 ^ (prefixWord ++ tailWord_2664553).sum := by decide
  have hdescent : baseEnd_2664553 < baseStart_2664553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664585 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 4, 3]
def baseStart_2664585 : Nat := 118140960795 + 2664585 * 2 ^ 59
def prefixEnd_2664585 : Nat := 4983230072969 + 3 ^ 40 * 2664585 * 2
def baseEnd_2664585 : Nat := 912141899840375021755535

theorem tailTrace_2664585 : CollatzResearch.WordTrace tailWord_2664585 prefixEnd_2664585 912141899840375021755535 := by
  unfold tailWord_2664585
  simp only [CollatzResearch.WordTrace]
  refine ⟨97185399051671094732747209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64790266034447396488498139 97185399051671094732747209)
  ·
    refine ⟨72889049288753321049560407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97185399051671094732747209 72889049288753321049560407)
    ·
      refine ⟨109333573933129981574340611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72889049288753321049560407 109333573933129981574340611)
      ·
        refine ⟨164000360899694972361510917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109333573933129981574340611 164000360899694972361510917)
        ·
          refine ⟨30750067668692807317783297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164000360899694972361510917 30750067668692807317783297)
          ·
            refine ⟨23062550751519605488337473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30750067668692807317783297 23062550751519605488337473)
            ·
              refine ⟨17296913063639704116253105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23062550751519605488337473 17296913063639704116253105)
              ·
                refine ⟨12972684797729778087189829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17296913063639704116253105 12972684797729778087189829)
                ·
                  refine ⟨2432378399574333391348093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12972684797729778087189829 2432378399574333391348093)
                  ·
                    refine ⟨912141899840375021755535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2432378399574333391348093 912141899840375021755535)
                    ·
                      rfl

theorem cell22_2664585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 3].length) (baseStart_2664585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664585 prefixEnd_2664585 := by exact prefixLift 2664585
  have htrace : WordTrace (prefixWord ++ tailWord_2664585) baseStart_2664585 baseEnd_2664585 := by
    simpa [prefixWord, tailWord_2664585, baseEnd_2664585] using wordTrace_append hprefix tailTrace_2664585
  have hstable : (prefixWord ++ tailWord_2664585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664585).length < 2 ^ (prefixWord ++ tailWord_2664585).sum := by decide
  have hdescent : baseEnd_2664585 < baseStart_2664585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664664 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 3, 3]
def baseStart_2664664 : Nat := 118140960795 + 2664664 * 2 ^ 59
def prefixEnd_2664664 : Nat := 4983230072969 + 3 ^ 40 * 2664664 * 2
def baseEnd_2664664 : Nat := 912168943154845149030293

theorem tailTrace_2664664 : CollatzResearch.WordTrace tailWord_2664664 prefixEnd_2664664 912168943154845149030293 := by
  unfold tailWord_2664664
  simp only [CollatzResearch.WordTrace]
  refine ⟨48594140209192445612436523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64792186945589927483248697 48594140209192445612436523)
  ·
    refine ⟨72891210313788668418654785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48594140209192445612436523 72891210313788668418654785)
    ·
      refine ⟨54668407735341501313991089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72891210313788668418654785 54668407735341501313991089)
      ·
        refine ⟨41001305801506125985493317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54668407735341501313991089 41001305801506125985493317)
        ·
          refine ⟨7687744837782398622279997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41001305801506125985493317 7687744837782398622279997)
          ·
            refine ⟨2882904314168399483354999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7687744837782398622279997 2882904314168399483354999)
            ·
              refine ⟨4324356471252599225032499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2882904314168399483354999 4324356471252599225032499)
              ·
                refine ⟨6486534706878898837548749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4324356471252599225032499 6486534706878898837548749)
                ·
                  refine ⟨2432450515079587064080781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6486534706878898837548749 2432450515079587064080781)
                  ·
                    refine ⟨912168943154845149030293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2432450515079587064080781 912168943154845149030293)
                    ·
                      rfl

theorem cell22_2664664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_2664664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664664 prefixEnd_2664664 := by exact prefixLift 2664664
  have htrace : WordTrace (prefixWord ++ tailWord_2664664) baseStart_2664664 baseEnd_2664664 := by
    simpa [prefixWord, tailWord_2664664, baseEnd_2664664] using wordTrace_append hprefix tailTrace_2664664
  have hstable : (prefixWord ++ tailWord_2664664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664664).length < 2 ^ (prefixWord ++ tailWord_2664664).sum := by decide
  have hdescent : baseEnd_2664664 < baseStart_2664664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664677 : List Nat := [1, 3, 1, 4, 2, 2, 1, 3, 5]
def baseStart_2664677 : Nat := 118140960795 + 2664677 * 2 ^ 59
def prefixEnd_2664677 : Nat := 4983230072969 + 3 ^ 40 * 2664677 * 2
def baseEnd_2664677 : Nat := 304057797773505816151751

theorem tailTrace_2664677 : CollatzResearch.WordTrace tailWord_2664677 prefixEnd_2664677 304057797773505816151751 := by
  unfold tailWord_2664677
  simp only [CollatzResearch.WordTrace]
  refine ⟨97188754567337794445096285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64792503044891862963397523 97188754567337794445096285)
  ·
    refine ⟨36445782962751672916911107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97188754567337794445096285 36445782962751672916911107)
    ·
      refine ⟨54668674444127509375366661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36445782962751672916911107 54668674444127509375366661)
      ·
        refine ⟨10250376458273908007881249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54668674444127509375366661 10250376458273908007881249)
        ·
          refine ⟨7687782343705431005910937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10250376458273908007881249 7687782343705431005910937)
          ·
            refine ⟨5765836757779073254433203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7687782343705431005910937 5765836757779073254433203)
            ·
              refine ⟨8648755136668609881649805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5765836757779073254433203 8648755136668609881649805)
              ·
                refine ⟨3243283176250728705618677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8648755136668609881649805 3243283176250728705618677)
                ·
                  refine ⟨304057797773505816151751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3243283176250728705618677 304057797773505816151751)
                  ·
                    rfl

theorem cell22_2664677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_2664677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664677 prefixEnd_2664677 := by exact prefixLift 2664677
  have htrace : WordTrace (prefixWord ++ tailWord_2664677) baseStart_2664677 baseEnd_2664677 := by
    simpa [prefixWord, tailWord_2664677, baseEnd_2664677] using wordTrace_append hprefix tailTrace_2664677
  have hstable : (prefixWord ++ tailWord_2664677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664677).length < 2 ^ (prefixWord ++ tailWord_2664677).sum := by decide
  have hdescent : baseEnd_2664677 < baseStart_2664677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664756 : List Nat := [2, 5, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2664756 : Nat := 118140960795 + 2664756 * 2 ^ 59
def prefixEnd_2664756 : Nat := 4983230072969 + 3 ^ 40 * 2664756 * 2
def baseEnd_2664756 : Nat := 304066812211662525243337

theorem tailTrace_2664756 : CollatzResearch.WordTrace tailWord_2664756 prefixEnd_2664756 304066812211662525243337 := by
  unfold tailWord_2664756
  simp only [CollatzResearch.WordTrace]
  refine ⟨48595817967025795468611061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64794423956034393958148081 48595817967025795468611061)
  ·
    refine ⟨4555857934408668325182287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48595817967025795468611061 4555857934408668325182287)
    ·
      refine ⟨6833786901613002487773431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4555857934408668325182287 6833786901613002487773431)
      ·
        refine ⟨10250680352419503731660147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6833786901613002487773431 10250680352419503731660147)
        ·
          refine ⟨15376020528629255597490221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10250680352419503731660147 15376020528629255597490221)
          ·
            refine ⟨5766007698235970849058833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15376020528629255597490221 5766007698235970849058833)
            ·
              refine ⟨4324505773676978136794125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5766007698235970849058833 4324505773676978136794125)
              ·
                refine ⟨1621689665128866801297797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4324505773676978136794125 1621689665128866801297797)
                ·
                  refine ⟨304066812211662525243337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1621689665128866801297797 304066812211662525243337)
                  ·
                    rfl

theorem cell22_2664756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2664756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664756 prefixEnd_2664756 := by exact prefixLift 2664756
  have htrace : WordTrace (prefixWord ++ tailWord_2664756) baseStart_2664756 baseEnd_2664756 := by
    simpa [prefixWord, tailWord_2664756, baseEnd_2664756] using wordTrace_append hprefix tailTrace_2664756
  have hstable : (prefixWord ++ tailWord_2664756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664756).length < 2 ^ (prefixWord ++ tailWord_2664756).sum := by decide
  have hdescent : baseEnd_2664756 < baseStart_2664756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664816 : List Nat := [2, 1, 1, 1, 4, 3, 3, 3, 1, 3]
def baseStart_2664816 : Nat := 118140960795 + 2664816 * 2 ^ 59
def prefixEnd_2664816 : Nat := 4983230072969 + 3 ^ 40 * 2664816 * 2
def baseEnd_2664816 : Nat := 912220975861167419229827

theorem tailTrace_2664816 : CollatzResearch.WordTrace tailWord_2664816 prefixEnd_2664816 912220975861167419229827 := by
  unfold tailWord_2664816
  simp only [CollatzResearch.WordTrace]
  refine ⟨48596912156917110592203151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64795882875889480789604201 48596912156917110592203151)
  ·
    refine ⟨72895368235375665888304727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48596912156917110592203151 72895368235375665888304727)
    ·
      refine ⟨109343052353063498832457091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72895368235375665888304727 109343052353063498832457091)
      ·
        refine ⟨164014578529595248248685637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109343052353063498832457091 164014578529595248248685637)
        ·
          refine ⟨30752733474299109046628557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164014578529595248248685637 30752733474299109046628557)
          ·
            refine ⟨11532275052862165892485709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30752733474299109046628557 11532275052862165892485709)
            ·
              refine ⟨4324603144823312209682141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11532275052862165892485709 4324603144823312209682141)
              ·
                refine ⟨1621726179308742078630803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4324603144823312209682141 1621726179308742078630803)
                ·
                  refine ⟨2432589268963113117946205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621726179308742078630803 2432589268963113117946205)
                  ·
                    refine ⟨912220975861167419229827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2432589268963113117946205 912220975861167419229827)
                    ·
                      rfl

theorem cell22_2664816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 1, 3].length) (baseStart_2664816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664816 prefixEnd_2664816 := by exact prefixLift 2664816
  have htrace : WordTrace (prefixWord ++ tailWord_2664816) baseStart_2664816 baseEnd_2664816 := by
    simpa [prefixWord, tailWord_2664816, baseEnd_2664816] using wordTrace_append hprefix tailTrace_2664816
  have hstable : (prefixWord ++ tailWord_2664816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664816).length < 2 ^ (prefixWord ++ tailWord_2664816).sum := by decide
  have hdescent : baseEnd_2664816 < baseStart_2664816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664846 : List Nat := [4, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_2664846 : Nat := 118140960795 + 2664846 * 2 ^ 59
def prefixEnd_2664846 : Nat := 4983230072969 + 3 ^ 40 * 2664846 * 2
def baseEnd_2664846 : Nat := 304077081824752446993245

theorem tailTrace_2664846 : CollatzResearch.WordTrace tailWord_2664846 prefixEnd_2664846 304077081824752446993245 := by
  unfold tailWord_2664846
  simp only [CollatzResearch.WordTrace]
  refine ⟨12149364812965692038499799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64796612335817024205332261 12149364812965692038499799)
  ·
    refine ⟨18224047219448538057749699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12149364812965692038499799 18224047219448538057749699)
    ·
      refine ⟨27336070829172807086624549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18224047219448538057749699 27336070829172807086624549)
      ·
        refine ⟨5125513280469901328742103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27336070829172807086624549 5125513280469901328742103)
        ·
          refine ⟨7688269920704851993113155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5125513280469901328742103 7688269920704851993113155)
          ·
            refine ⟨11532404881057277989669733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7688269920704851993113155 11532404881057277989669733)
            ·
              refine ⟨2162325915198239623063075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11532404881057277989669733 2162325915198239623063075)
              ·
                refine ⟨3243488872797359434594613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2162325915198239623063075 3243488872797359434594613)
                ·
                  refine ⟨304077081824752446993245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3243488872797359434594613 304077081824752446993245)
                  ·
                    rfl

theorem cell22_2664846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_2664846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664846 prefixEnd_2664846 := by exact prefixLift 2664846
  have htrace : WordTrace (prefixWord ++ tailWord_2664846) baseStart_2664846 baseEnd_2664846 := by
    simpa [prefixWord, tailWord_2664846, baseEnd_2664846] using wordTrace_append hprefix tailTrace_2664846
  have hstable : (prefixWord ++ tailWord_2664846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664846).length < 2 ^ (prefixWord ++ tailWord_2664846).sum := by decide
  have hdescent : baseEnd_2664846 < baseStart_2664846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664884 : List Nat := [2, 5, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_2664884 : Nat := 118140960795 + 2664884 * 2 ^ 59
def prefixEnd_2664884 : Nat := 4983230072969 + 3 ^ 40 * 2664884 * 2
def baseEnd_2664884 : Nat := 912244253650837908529619

theorem tailTrace_2664884 : CollatzResearch.WordTrace tailWord_2664884 prefixEnd_2664884 912244253650837908529619 := by
  unfold tailWord_2664884
  simp only [CollatzResearch.WordTrace]
  refine ⟨48598152238793934398940853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64797536318391912531921137 48598152238793934398940853)
  ·
    refine ⟨4556076772386931349900705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48598152238793934398940853 4556076772386931349900705)
    ·
      refine ⟨3417057579290198512425529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4556076772386931349900705 3417057579290198512425529)
      ·
        refine ⟨2562793184467648884319147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3417057579290198512425529 2562793184467648884319147)
        ·
          refine ⟨3844189776701473326478721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2562793184467648884319147 3844189776701473326478721)
          ·
            refine ⟨2883142332526104994859041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3844189776701473326478721 2883142332526104994859041)
            ·
              refine ⟨2162356749394578746144281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2883142332526104994859041 2162356749394578746144281)
              ·
                refine ⟨1621767562045934059608211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2162356749394578746144281 1621767562045934059608211)
                ·
                  refine ⟨2432651343068901089412317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621767562045934059608211 2432651343068901089412317)
                  ·
                    refine ⟨912244253650837908529619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2432651343068901089412317 912244253650837908529619)
                    ·
                      rfl

theorem cell22_2664884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_2664884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664884 prefixEnd_2664884 := by exact prefixLift 2664884
  have htrace : WordTrace (prefixWord ++ tailWord_2664884) baseStart_2664884 baseEnd_2664884 := by
    simpa [prefixWord, tailWord_2664884, baseEnd_2664884] using wordTrace_append hprefix tailTrace_2664884
  have hstable : (prefixWord ++ tailWord_2664884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664884).length < 2 ^ (prefixWord ++ tailWord_2664884).sum := by decide
  have hdescent : baseEnd_2664884 < baseStart_2664884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664947 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 7]
def baseStart_2664947 : Nat := 118140960795 + 2664947 * 2 ^ 59
def prefixEnd_2664947 : Nat := 4983230072969 + 3 ^ 40 * 2664947 * 2
def baseEnd_2664947 : Nat := 304088606612775581401475

theorem tailTrace_2664947 : CollatzResearch.WordTrace tailWord_2664947 prefixEnd_2664947 304088606612775581401475 := by
  unfold tailWord_2664947
  simp only [CollatzResearch.WordTrace]
  refine ⟨97198602276359630557425095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64799068184239753704950063 97198602276359630557425095)
  ·
    refine ⟨145797903414539445836137643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97198602276359630557425095 145797903414539445836137643)
    ·
      refine ⟨218696855121809168754206465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145797903414539445836137643 218696855121809168754206465)
      ·
        refine ⟨164022641341356876565654849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218696855121809168754206465 164022641341356876565654849)
        ·
          refine ⟨123016981006017657424241137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164022641341356876565654849 123016981006017657424241137)
          ·
            refine ⟨92262735754513243068180853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123016981006017657424241137 92262735754513243068180853)
            ·
              refine ⟨8649631476985616537641955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92262735754513243068180853 8649631476985616537641955)
              ·
                refine ⟨12974447215478424806462933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8649631476985616537641955 12974447215478424806462933)
                ·
                  refine ⟨304088606612775581401475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12974447215478424806462933 304088606612775581401475)
                  ·
                    rfl

theorem cell22_2664947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 7].length) (baseStart_2664947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664947 prefixEnd_2664947 := by exact prefixLift 2664947
  have htrace : WordTrace (prefixWord ++ tailWord_2664947) baseStart_2664947 baseEnd_2664947 := by
    simpa [prefixWord, tailWord_2664947, baseEnd_2664947] using wordTrace_append hprefix tailTrace_2664947
  have hstable : (prefixWord ++ tailWord_2664947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664947).length < 2 ^ (prefixWord ++ tailWord_2664947).sum := by decide
  have hdescent : baseEnd_2664947 < baseStart_2664947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664994 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_2664994 : Nat := 118140960795 + 2664994 * 2 ^ 59
def prefixEnd_2664994 : Nat := 4983230072969 + 3 ^ 40 * 2664994 * 2
def baseEnd_2664994 : Nat := 912281908898834288279281

theorem tailTrace_2664994 : CollatzResearch.WordTrace tailWord_2664994 prefixEnd_2664994 912281908898834288279281 := by
  unfold tailWord_2664994
  simp only [CollatzResearch.WordTrace]
  refine ⟨24300079126797339396096509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64800211004792905056257357 24300079126797339396096509)
  ·
    refine ⟨9112529672549002273536191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24300079126797339396096509 9112529672549002273536191)
    ·
      refine ⟨13668794508823503410304287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9112529672549002273536191 13668794508823503410304287)
      ·
        refine ⟨20503191763235255115456431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13668794508823503410304287 20503191763235255115456431)
        ·
          refine ⟨30754787644852882673184647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20503191763235255115456431 30754787644852882673184647)
          ·
            refine ⟨46132181467279324009776971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30754787644852882673184647 46132181467279324009776971)
            ·
              refine ⟨69198272200918986014665457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46132181467279324009776971 69198272200918986014665457)
              ·
                refine ⟨51898704150689239510999093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69198272200918986014665457 51898704150689239510999093)
                ·
                  refine ⟨4865503514127116204156165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51898704150689239510999093 4865503514127116204156165)
                  ·
                    refine ⟨912281908898834288279281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4865503514127116204156165 912281908898834288279281)
                    ·
                      rfl

theorem cell22_2664994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_2664994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2664994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2664994 prefixEnd_2664994 := by exact prefixLift 2664994
  have htrace : WordTrace (prefixWord ++ tailWord_2664994) baseStart_2664994 baseEnd_2664994 := by
    simpa [prefixWord, tailWord_2664994, baseEnd_2664994] using wordTrace_append hprefix tailTrace_2664994
  have hstable : (prefixWord ++ tailWord_2664994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664994).length < 2 ^ (prefixWord ++ tailWord_2664994).sum := by decide
  have hdescent : baseEnd_2664994 < baseStart_2664994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665009 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 6]
def baseStart_2665009 : Nat := 118140960795 + 2665009 * 2 ^ 59
def prefixEnd_2665009 : Nat := 4983230072969 + 3 ^ 40 * 2665009 * 2
def baseEnd_2665009 : Nat := 304095681235126416384745

theorem tailTrace_2665009 : CollatzResearch.WordTrace tailWord_2665009 prefixEnd_2665009 304095681235126416384745 := by
  unfold tailWord_2665009
  simp only [CollatzResearch.WordTrace]
  refine ⟨97200863602135015146182081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64800575734756676764121387 97200863602135015146182081)
  ·
    refine ⟨72900647701601261359636561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97200863602135015146182081 72900647701601261359636561)
    ·
      refine ⟨54675485776200946019727421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72900647701601261359636561 54675485776200946019727421)
      ·
        refine ⟨20503307166075354757397783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54675485776200946019727421 20503307166075354757397783)
        ·
          refine ⟨30754960749113032136096675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20503307166075354757397783 30754960749113032136096675)
          ·
            refine ⟨46132441123669548204145013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30754960749113032136096675 46132441123669548204145013)
            ·
              refine ⟨4324916355344020144138595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46132441123669548204145013 4324916355344020144138595)
              ·
                refine ⟨6487374533016030216207893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4324916355344020144138595 6487374533016030216207893)
                ·
                  refine ⟨304095681235126416384745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6487374533016030216207893 304095681235126416384745)
                  ·
                    rfl

theorem cell22_2665009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 6].length) (baseStart_2665009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665009 prefixEnd_2665009 := by exact prefixLift 2665009
  have htrace : WordTrace (prefixWord ++ tailWord_2665009) baseStart_2665009 baseEnd_2665009 := by
    simpa [prefixWord, tailWord_2665009, baseEnd_2665009] using wordTrace_append hprefix tailTrace_2665009
  have hstable : (prefixWord ++ tailWord_2665009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665009).length < 2 ^ (prefixWord ++ tailWord_2665009).sum := by decide
  have hdescent : baseEnd_2665009 < baseStart_2665009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665039 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 2, 4]
def baseStart_2665039 : Nat := 118140960795 + 2665039 * 2 ^ 59
def prefixEnd_2665039 : Nat := 4983230072969 + 3 ^ 40 * 2665039 * 2
def baseEnd_2665039 : Nat := 912297313318469170904143

theorem tailTrace_2665039 : CollatzResearch.WordTrace tailWord_2665039 prefixEnd_2665039 912297313318469170904143 := by
  unfold tailWord_2665039
  simp only [CollatzResearch.WordTrace]
  refine ⟨97201957792026330269774171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64801305194684220179849447 97201957792026330269774171)
  ·
    refine ⟨145802936688039495404661257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97201957792026330269774171 145802936688039495404661257)
    ·
      refine ⟨109352202516029621553495943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145802936688039495404661257 109352202516029621553495943)
      ·
        refine ⟨164028303774044432330243915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109352202516029621553495943 164028303774044432330243915)
        ·
          refine ⟨246042455661066648495365873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164028303774044432330243915 246042455661066648495365873)
          ·
            refine ⟨184531841745799986371524405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246042455661066648495365873 184531841745799986371524405)
            ·
              refine ⟨17299860163668748722330413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184531841745799986371524405 17299860163668748722330413)
              ·
                refine ⟨6487447561375780770873905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17299860163668748722330413 6487447561375780770873905)
                ·
                  refine ⟨4865585671031835578155429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6487447561375780770873905 4865585671031835578155429)
                  ·
                    refine ⟨912297313318469170904143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4865585671031835578155429 912297313318469170904143)
                    ·
                      rfl

theorem cell22_2665039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_2665039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665039 prefixEnd_2665039 := by exact prefixLift 2665039
  have htrace : WordTrace (prefixWord ++ tailWord_2665039) baseStart_2665039 baseEnd_2665039 := by
    simpa [prefixWord, tailWord_2665039, baseEnd_2665039] using wordTrace_append hprefix tailTrace_2665039
  have hstable : (prefixWord ++ tailWord_2665039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665039).length < 2 ^ (prefixWord ++ tailWord_2665039).sum := by decide
  have hdescent : baseEnd_2665039 < baseStart_2665039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665116 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 7]
def baseStart_2665116 : Nat := 118140960795 + 2665116 * 2 ^ 59
def prefixEnd_2665116 : Nat := 4983230072969 + 3 ^ 40 * 2665116 * 2
def baseEnd_2665116 : Nat := 304107890664022212242969

theorem tailTrace_2665116 : CollatzResearch.WordTrace tailWord_2665116 prefixEnd_2665116 304107890664022212242969 := by
  unfold tailWord_2665116
  simp only [CollatzResearch.WordTrace]
  refine ⟨48602383106373686210163601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64803177475164914946884801 48602383106373686210163601)
  ·
    refine ⟨36451787329780264657622701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48602383106373686210163601 36451787329780264657622701)
    ·
      refine ⟨13669420248667599246608513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36451787329780264657622701 13669420248667599246608513)
      ·
        refine ⟨10252065186500699434956385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13669420248667599246608513 10252065186500699434956385)
        ·
          refine ⟨7689048889875524576217289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10252065186500699434956385 7689048889875524576217289)
          ·
            refine ⟨5766786667406643432162967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7689048889875524576217289 5766786667406643432162967)
            ·
              refine ⟨8650180001109965148244451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5766786667406643432162967 8650180001109965148244451)
              ·
                refine ⟨12975270001664947722366677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8650180001109965148244451 12975270001664947722366677)
                ·
                  refine ⟨304107890664022212242969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12975270001664947722366677 304107890664022212242969)
                  ·
                    rfl

theorem cell22_2665116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_2665116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665116 prefixEnd_2665116 := by exact prefixLift 2665116
  have htrace : WordTrace (prefixWord ++ tailWord_2665116) baseStart_2665116 baseEnd_2665116 := by
    simpa [prefixWord, tailWord_2665116, baseEnd_2665116] using wordTrace_append hprefix tailTrace_2665116
  have hstable : (prefixWord ++ tailWord_2665116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665116).length < 2 ^ (prefixWord ++ tailWord_2665116).sum := by decide
  have hdescent : baseEnd_2665116 < baseStart_2665116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665206 : List Nat := [5, 1, 1, 1, 1, 2, 1, 10]
def baseStart_2665206 : Nat := 118140960795 + 2665206 * 2 ^ 59
def prefixEnd_2665206 : Nat := 4983230072969 + 3 ^ 40 * 2665206 * 2
def baseEnd_2665206 : Nat := 101372720092370711330959

theorem tailTrace_2665206 : CollatzResearch.WordTrace tailWord_2665206 prefixEnd_2665206 101372720092370711330959 := by
  unfold tailWord_2665206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6075503048901332361943967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64805365854947545194068981 6075503048901332361943967)
  ·
    refine ⟨9113254573351998542915951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6075503048901332361943967 9113254573351998542915951)
    ·
      refine ⟨13669881860027997814373927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9113254573351998542915951 13669881860027997814373927)
      ·
        refine ⟨20504822790041996721560891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13669881860027997814373927 20504822790041996721560891)
        ·
          refine ⟨30757234185062995082341337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20504822790041996721560891 30757234185062995082341337)
          ·
            refine ⟨23067925638797246311756003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30757234185062995082341337 23067925638797246311756003)
            ·
              refine ⟨34601888458195869467634005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23067925638797246311756003 34601888458195869467634005)
              ·
                refine ⟨101372720092370711330959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34601888458195869467634005 101372720092370711330959)
                ·
                  rfl

theorem cell22_2665206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_2665206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665206 prefixEnd_2665206 := by exact prefixLift 2665206
  have htrace : WordTrace (prefixWord ++ tailWord_2665206) baseStart_2665206 baseEnd_2665206 := by
    simpa [prefixWord, tailWord_2665206, baseEnd_2665206] using wordTrace_append hprefix tailTrace_2665206
  have hstable : (prefixWord ++ tailWord_2665206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665206).length < 2 ^ (prefixWord ++ tailWord_2665206).sum := by decide
  have hdescent : baseEnd_2665206 < baseStart_2665206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665266 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_2665266 : Nat := 118140960795 + 2665266 * 2 ^ 59
def prefixEnd_2665266 : Nat := 4983230072969 + 3 ^ 40 * 2665266 * 2
def baseEnd_2665266 : Nat := 912375020057516245478447

theorem tailTrace_2665266 : CollatzResearch.WordTrace tailWord_2665266 prefixEnd_2665266 912375020057516245478447 := by
  unfold tailWord_2665266
  simp only [CollatzResearch.WordTrace]
  refine ⟨24302559290550987009571913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64806824774802632025525101 24302559290550987009571913)
  ·
    refine ⟨18226919467913240257178935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24302559290550987009571913 18226919467913240257178935)
    ·
      refine ⟨27340379201869860385768403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18226919467913240257178935 27340379201869860385768403)
      ·
        refine ⟨41010568802804790578652605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27340379201869860385768403 41010568802804790578652605)
        ·
          refine ⟨15378963301051796466994727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41010568802804790578652605 15378963301051796466994727)
          ·
            refine ⟨23068444951577694700492091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15378963301051796466994727 23068444951577694700492091)
            ·
              refine ⟨34602667427366542050738137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23068444951577694700492091 34602667427366542050738137)
              ·
                refine ⟨25952000570524906538053603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34602667427366542050738137 25952000570524906538053603)
                ·
                  refine ⟨38928000855787359807080405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25952000570524906538053603 38928000855787359807080405)
                  ·
                    refine ⟨912375020057516245478447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38928000855787359807080405 912375020057516245478447)
                    ·
                      rfl

theorem cell22_2665266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_2665266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665266 prefixEnd_2665266 := by exact prefixLift 2665266
  have htrace : WordTrace (prefixWord ++ tailWord_2665266) baseStart_2665266 baseEnd_2665266 := by
    simpa [prefixWord, tailWord_2665266, baseEnd_2665266] using wordTrace_append hprefix tailTrace_2665266
  have hstable : (prefixWord ++ tailWord_2665266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665266).length < 2 ^ (prefixWord ++ tailWord_2665266).sum := by decide
  have hdescent : baseEnd_2665266 < baseStart_2665266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665296 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 6]
def baseStart_2665296 : Nat := 118140960795 + 2665296 * 2 ^ 59
def prefixEnd_2665296 : Nat := 4983230072969 + 3 ^ 40 * 2665296 * 2
def baseEnd_2665296 : Nat := 304128429890202055742785

theorem tailTrace_2665296 : CollatzResearch.WordTrace tailWord_2665296 prefixEnd_2665296 304128429890202055742785 := by
  unfold tailWord_2665296
  simp only [CollatzResearch.WordTrace]
  refine ⟨48605665676047631580939871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64807554234730175441253161 48605665676047631580939871)
  ·
    refine ⟨72908498514071447371409807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48605665676047631580939871 72908498514071447371409807)
    ·
      refine ⟨109362747771107171057114711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72908498514071447371409807 109362747771107171057114711)
      ·
        refine ⟨164044121656660756585672067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109362747771107171057114711 164044121656660756585672067)
        ·
          refine ⟨246066182484991134878508101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164044121656660756585672067 246066182484991134878508101)
          ·
            refine ⟨46137409215935837789720269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246066182484991134878508101 46137409215935837789720269)
            ·
              refine ⟨17301528455975939171145101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46137409215935837789720269 17301528455975939171145101)
              ·
                refine ⟨6488073170990977189179413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17301528455975939171145101 6488073170990977189179413)
                ·
                  refine ⟨304128429890202055742785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6488073170990977189179413 304128429890202055742785)
                  ·
                    rfl

theorem cell22_2665296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 6].length) (baseStart_2665296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665296 prefixEnd_2665296 := by exact prefixLift 2665296
  have htrace : WordTrace (prefixWord ++ tailWord_2665296) baseStart_2665296 baseEnd_2665296 := by
    simpa [prefixWord, tailWord_2665296, baseEnd_2665296] using wordTrace_append hprefix tailTrace_2665296
  have hstable : (prefixWord ++ tailWord_2665296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665296).length < 2 ^ (prefixWord ++ tailWord_2665296).sum := by decide
  have hdescent : baseEnd_2665296 < baseStart_2665296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665315 : List Nat := [1, 1, 1, 5, 3, 2, 2, 2, 1, 4]
def baseStart_2665315 : Nat := 118140960795 + 2665315 * 2 ^ 59
def prefixEnd_2665315 : Nat := 4983230072969 + 3 ^ 40 * 2665315 * 2
def baseEnd_2665315 : Nat := 912391793758896451003297

theorem tailTrace_2665315 : CollatzResearch.WordTrace tailWord_2665315 prefixEnd_2665315 912391793758896451003297 := by
  unfold tailWord_2665315
  simp only [CollatzResearch.WordTrace]
  refine ⟨97212024339026429406821399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64808016226017619604547599 97212024339026429406821399)
  ·
    refine ⟨145818036508539644110232099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97212024339026429406821399 145818036508539644110232099)
    ·
      refine ⟨218727054762809466165348149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145818036508539644110232099 218727054762809466165348149)
      ·
        refine ⟨20505661384013387453001389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 218727054762809466165348149 20505661384013387453001389)
        ·
          refine ⟨7689623019005020294875521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20505661384013387453001389 7689623019005020294875521)
          ·
            refine ⟨5767217264253765221156641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7689623019005020294875521 5767217264253765221156641)
            ·
              refine ⟨4325412948190323915867481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5767217264253765221156641 4325412948190323915867481)
              ·
                refine ⟨3244059711142742936900611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4325412948190323915867481 3244059711142742936900611)
                ·
                  refine ⟨4866089566714114405350917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244059711142742936900611 4866089566714114405350917)
                  ·
                    refine ⟨912391793758896451003297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4866089566714114405350917 912391793758896451003297)
                    ·
                      rfl

theorem cell22_2665315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 4].length) (baseStart_2665315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665315 prefixEnd_2665315 := by exact prefixLift 2665315
  have htrace : WordTrace (prefixWord ++ tailWord_2665315) baseStart_2665315 baseEnd_2665315 := by
    simpa [prefixWord, tailWord_2665315, baseEnd_2665315] using wordTrace_append hprefix tailTrace_2665315
  have hstable : (prefixWord ++ tailWord_2665315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665315).length < 2 ^ (prefixWord ++ tailWord_2665315).sum := by decide
  have hdescent : baseEnd_2665315 < baseStart_2665315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665328 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 4, 3]
def baseStart_2665328 : Nat := 118140960795 + 2665328 * 2 ^ 59
def prefixEnd_2665328 : Nat := 4983230072969 + 3 ^ 40 * 2665328 * 2
def baseEnd_2665328 : Nat := 912396243924568750428257

theorem tailTrace_2665328 : CollatzResearch.WordTrace tailWord_2665328 prefixEnd_2665328 912396243924568750428257 := by
  unfold tailWord_2665328
  simp only [CollatzResearch.WordTrace]
  refine ⟨48606249243989666313522319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64808332325319555084696425 48606249243989666313522319)
  ·
    refine ⟨72909373865984499470283479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48606249243989666313522319 72909373865984499470283479)
    ·
      refine ⟨109364060798976749205425219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72909373865984499470283479 109364060798976749205425219)
      ·
        refine ⟨164046091198465123808137829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109364060798976749205425219 164046091198465123808137829)
        ·
          refine ⟨30758642099712210714025843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164046091198465123808137829 30758642099712210714025843)
          ·
            refine ⟨46137963149568316071038765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30758642099712210714025843 46137963149568316071038765)
            ·
              refine ⟨17301736181088118526639537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46137963149568316071038765 17301736181088118526639537)
              ·
                refine ⟨12976302135816088894979653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17301736181088118526639537 12976302135816088894979653)
                ·
                  refine ⟨2433056650465516667808685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12976302135816088894979653 2433056650465516667808685)
                  ·
                    refine ⟨912396243924568750428257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2433056650465516667808685 912396243924568750428257)
                    ·
                      rfl

theorem cell22_2665328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 4, 3].length) (baseStart_2665328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665328 prefixEnd_2665328 := by exact prefixLift 2665328
  have htrace : WordTrace (prefixWord ++ tailWord_2665328) baseStart_2665328 baseEnd_2665328 := by
    simpa [prefixWord, tailWord_2665328, baseEnd_2665328] using wordTrace_append hprefix tailTrace_2665328
  have hstable : (prefixWord ++ tailWord_2665328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665328).length < 2 ^ (prefixWord ++ tailWord_2665328).sum := by decide
  have hdescent : baseEnd_2665328 < baseStart_2665328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665330 : List Nat := [3, 2, 1, 2, 1, 1, 5, 3, 4]
def baseStart_2665330 : Nat := 118140960795 + 2665330 * 2 ^ 59
def prefixEnd_2665330 : Nat := 4983230072969 + 3 ^ 40 * 2665330 * 2
def baseEnd_2665330 : Nat := 304132309521813803959417

theorem tailTrace_2665330 : CollatzResearch.WordTrace tailWord_2665330 prefixEnd_2665330 304132309521813803959417 := by
  unfold tailWord_2665330
  simp only [CollatzResearch.WordTrace]
  refine ⟨24303142858493021742154361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64808380955981391312411629 24303142858493021742154361)
  ·
    refine ⟨18227357143869766306615771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24303142858493021742154361 18227357143869766306615771)
    ·
      refine ⟨27341035715804649459923657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18227357143869766306615771 27341035715804649459923657)
      ·
        refine ⟨20505776786853487094942743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27341035715804649459923657 20505776786853487094942743)
        ·
          refine ⟨30758665180280230642414115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20505776786853487094942743 30758665180280230642414115)
          ·
            refine ⟨46137997770420345963621173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30758665180280230642414115 46137997770420345963621173)
            ·
              refine ⟨4325437290976907434089485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46137997770420345963621173 4325437290976907434089485)
              ·
                refine ⟨1622038984116340287783557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4325437290976907434089485 1622038984116340287783557)
                ·
                  refine ⟨304132309521813803959417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1622038984116340287783557 304132309521813803959417)
                  ·
                    rfl

theorem cell22_2665330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_2665330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665330 prefixEnd_2665330 := by exact prefixLift 2665330
  have htrace : WordTrace (prefixWord ++ tailWord_2665330) baseStart_2665330 baseEnd_2665330 := by
    simpa [prefixWord, tailWord_2665330, baseEnd_2665330] using wordTrace_append hprefix tailTrace_2665330
  have hstable : (prefixWord ++ tailWord_2665330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665330).length < 2 ^ (prefixWord ++ tailWord_2665330).sum := by decide
  have hdescent : baseEnd_2665330 < baseStart_2665330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665341 : List Nat := [1, 4, 1, 1, 2, 1, 12]
def baseStart_2665341 : Nat := 118140960795 + 2665341 * 2 ^ 59
def prefixEnd_2665341 : Nat := 4983230072969 + 3 ^ 40 * 2665341 * 2
def baseEnd_2665341 : Nat := 33792618299638557401971

theorem tailTrace_2665341 : CollatzResearch.WordTrace tailWord_2665341 prefixEnd_2665341 33792618299638557401971 := by
  unfold tailWord_2665341
  simp only [CollatzResearch.WordTrace]
  refine ⟨97212972636932235847267877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64808648424621490564845251 97212972636932235847267877)
  ·
    refine ⟨18227432369424794221362727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97212972636932235847267877 18227432369424794221362727)
    ·
      refine ⟨27341148554137191332044091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18227432369424794221362727 27341148554137191332044091)
      ·
        refine ⟨41011722831205786998066137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27341148554137191332044091 41011722831205786998066137)
        ·
          refine ⟨30758792123404340248549603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41011722831205786998066137 30758792123404340248549603)
          ·
            refine ⟨46138188185106510372824405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30758792123404340248549603 46138188185106510372824405)
            ·
              refine ⟨33792618299638557401971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 46138188185106510372824405 33792618299638557401971)
              ·
                rfl

theorem cell22_2665341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 12].length) (baseStart_2665341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665341 prefixEnd_2665341 := by exact prefixLift 2665341
  have htrace : WordTrace (prefixWord ++ tailWord_2665341) baseStart_2665341 baseEnd_2665341 := by
    simpa [prefixWord, tailWord_2665341, baseEnd_2665341] using wordTrace_append hprefix tailTrace_2665341
  have hstable : (prefixWord ++ tailWord_2665341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665341).length < 2 ^ (prefixWord ++ tailWord_2665341).sum := by decide
  have hdescent : baseEnd_2665341 < baseStart_2665341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665366 : List Nat := [5, 3, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2665366 : Nat := 118140960795 + 2665366 * 2 ^ 59
def prefixEnd_2665366 : Nat := 4983230072969 + 3 ^ 40 * 2665366 * 2
def baseEnd_2665366 : Nat := 912409252101149317978141

theorem tailTrace_2665366 : CollatzResearch.WordTrace tailWord_2665366 prefixEnd_2665366 912409252101149317978141 := by
  unfold tailWord_2665366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6075867778865104069807997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64809256307894443411285301 6075867778865104069807997)
  ·
    refine ⟨2278450417074414026177999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6075867778865104069807997 2278450417074414026177999)
    ·
      refine ⟨3417675625611621039266999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2278450417074414026177999 3417675625611621039266999)
      ·
        refine ⟨5126513438417431558900499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3417675625611621039266999 5126513438417431558900499)
        ·
          refine ⟨7689770157626147338350749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5126513438417431558900499 7689770157626147338350749)
          ·
            refine ⟨2883663809109805251881531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7689770157626147338350749 2883663809109805251881531)
            ·
              refine ⟨4325495713664707877822297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2883663809109805251881531 4325495713664707877822297)
              ·
                refine ⟨3244121785248530908366723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4325495713664707877822297 3244121785248530908366723)
                ·
                  refine ⟨4866182677872796362550085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244121785248530908366723 4866182677872796362550085)
                  ·
                    refine ⟨912409252101149317978141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4866182677872796362550085 912409252101149317978141)
                    ·
                      rfl

theorem cell22_2665366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2665366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665366 prefixEnd_2665366 := by exact prefixLift 2665366
  have htrace : WordTrace (prefixWord ++ tailWord_2665366) baseStart_2665366 baseEnd_2665366 := by
    simpa [prefixWord, tailWord_2665366, baseEnd_2665366] using wordTrace_append hprefix tailTrace_2665366
  have hstable : (prefixWord ++ tailWord_2665366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665366).length < 2 ^ (prefixWord ++ tailWord_2665366).sum := by decide
  have hdescent : baseEnd_2665366 < baseStart_2665366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665454 : List Nat := [4, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_2665454 : Nat := 118140960795 + 2665454 * 2 ^ 59
def prefixEnd_2665454 : Nat := 4983230072969 + 3 ^ 40 * 2665454 * 2
def baseEnd_2665454 : Nat := 304146458766515473925957

theorem tailTrace_2665454 : CollatzResearch.WordTrace tailWord_2665454 prefixEnd_2665454 304146458766515473925957 := by
  unfold tailWord_2665454
  simp only [CollatzResearch.WordTrace]
  refine ⟨12152136760690357018266427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64811396057015237430754277 12152136760690357018266427)
  ·
    refine ⟨18228205141035535527399641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12152136760690357018266427 18228205141035535527399641)
    ·
      refine ⟨13671153855776651645549731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18228205141035535527399641 13671153855776651645549731)
      ·
        refine ⟨20506730783664977468324597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13671153855776651645549731 20506730783664977468324597)
        ·
          refine ⟨1922506010968591637655431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20506730783664977468324597 1922506010968591637655431)
          ·
            refine ⟨2883759016452887456483147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922506010968591637655431 2883759016452887456483147)
            ·
              refine ⟨4325638524679331184724721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2883759016452887456483147 4325638524679331184724721)
              ·
                refine ⟨3244228893509498388543541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4325638524679331184724721 3244228893509498388543541)
                ·
                  refine ⟨304146458766515473925957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3244228893509498388543541 304146458766515473925957)
                  ·
                    rfl

theorem cell22_2665454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_2665454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665454 prefixEnd_2665454 := by exact prefixLift 2665454
  have htrace : WordTrace (prefixWord ++ tailWord_2665454) baseStart_2665454 baseEnd_2665454 := by
    simpa [prefixWord, tailWord_2665454, baseEnd_2665454] using wordTrace_append hprefix tailTrace_2665454
  have hstable : (prefixWord ++ tailWord_2665454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665454).length < 2 ^ (prefixWord ++ tailWord_2665454).sum := by decide
  have hdescent : baseEnd_2665454 < baseStart_2665454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665465 : List Nat := [1, 2, 1, 3, 1, 3, 1, 6, 4]
def baseStart_2665465 : Nat := 118140960795 + 2665465 * 2 ^ 59
def prefixEnd_2665465 : Nat := 4983230072969 + 3 ^ 40 * 2665465 * 2
def baseEnd_2665465 : Nat := 304147713941448686584279

theorem tailTrace_2665465 : CollatzResearch.WordTrace tailWord_2665465 prefixEnd_2665465 304147713941448686584279 := by
  unfold tailWord_2665465
  simp only [CollatzResearch.WordTrace]
  refine ⟨97217495288483005024781849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64811663525655336683187899 97217495288483005024781849)
  ·
    refine ⟨72913121466362253768586387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97217495288483005024781849 72913121466362253768586387)
    ·
      refine ⟨109369682199543380652879581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72913121466362253768586387 109369682199543380652879581)
      ·
        refine ⟨41013630824828767744829843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109369682199543380652879581 41013630824828767744829843)
        ·
          refine ⟨61520446237243151617244765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41013630824828767744829843 61520446237243151617244765)
          ·
            refine ⟨23070167338966181856466787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61520446237243151617244765 23070167338966181856466787)
            ·
              refine ⟨34605251008449272784700181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23070167338966181856466787 34605251008449272784700181)
              ·
                refine ⟨1622121141021059661782821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34605251008449272784700181 1622121141021059661782821)
                ·
                  refine ⟨304147713941448686584279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1622121141021059661782821 304147713941448686584279)
                  ·
                    rfl

theorem cell22_2665465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 4].length) (baseStart_2665465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665465 prefixEnd_2665465 := by exact prefixLift 2665465
  have htrace : WordTrace (prefixWord ++ tailWord_2665465) baseStart_2665465 baseEnd_2665465 := by
    simpa [prefixWord, tailWord_2665465, baseEnd_2665465] using wordTrace_append hprefix tailTrace_2665465
  have hstable : (prefixWord ++ tailWord_2665465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665465).length < 2 ^ (prefixWord ++ tailWord_2665465).sum := by decide
  have hdescent : baseEnd_2665465 < baseStart_2665465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665480 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 1, 5]
def baseStart_2665480 : Nat := 118140960795 + 2665480 * 2 ^ 59
def prefixEnd_2665480 : Nat := 4983230072969 + 3 ^ 40 * 2665480 * 2
def baseEnd_2665480 : Nat := 912448276630891020627791

theorem tailTrace_2665480 : CollatzResearch.WordTrace tailWord_2665480 prefixEnd_2665480 912448276630891020627791 := by
  unfold tailWord_2665480
  simp only [CollatzResearch.WordTrace]
  refine ⟨48609021191714331293288947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64812028255619108391051929 48609021191714331293288947)
  ·
    refine ⟨72913531787571496939933421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48609021191714331293288947 72913531787571496939933421)
    ·
      refine ⟨27342574420339311352475033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72913531787571496939933421 27342574420339311352475033)
      ·
        refine ⟨20506930815254483514356275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27342574420339311352475033 20506930815254483514356275)
        ·
          refine ⟨30760396222881725271534413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20506930815254483514356275 30760396222881725271534413)
          ·
            refine ⟨11535148583580646976825405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30760396222881725271534413 11535148583580646976825405)
            ·
              refine ⟨4325680718842742616309527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11535148583580646976825405 4325680718842742616309527)
              ·
                refine ⟨6488521078264113924464291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4325680718842742616309527 6488521078264113924464291)
                ·
                  refine ⟨9732781617396170886696437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6488521078264113924464291 9732781617396170886696437)
                  ·
                    refine ⟨912448276630891020627791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9732781617396170886696437 912448276630891020627791)
                    ·
                      rfl

theorem cell22_2665480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_2665480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665480 prefixEnd_2665480 := by exact prefixLift 2665480
  have htrace : WordTrace (prefixWord ++ tailWord_2665480) baseStart_2665480 baseEnd_2665480 := by
    simpa [prefixWord, tailWord_2665480, baseEnd_2665480] using wordTrace_append hprefix tailTrace_2665480
  have hstable : (prefixWord ++ tailWord_2665480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665480).length < 2 ^ (prefixWord ++ tailWord_2665480).sum := by decide
  have hdescent : baseEnd_2665480 < baseStart_2665480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665495 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 1, 6]
def baseStart_2665495 : Nat := 118140960795 + 2665495 * 2 ^ 59
def prefixEnd_2665495 : Nat := 4983230072969 + 3 ^ 40 * 2665495 * 2
def baseEnd_2665495 : Nat := 912453411437435981502745

theorem tailTrace_2665495 : CollatzResearch.WordTrace tailWord_2665495 prefixEnd_2665495 912453411437435981502745 := by
  unfold tailWord_2665495
  simp only [CollatzResearch.WordTrace]
  refine ⟨97218589478374320148373939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64812392985582880098915959 97218589478374320148373939)
  ·
    refine ⟨145827884217561480222560909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97218589478374320148373939 145827884217561480222560909)
    ·
      refine ⟨54685456581585555083460341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145827884217561480222560909 54685456581585555083460341)
      ·
        refine ⟨5126761554523645789074407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54685456581585555083460341 5126761554523645789074407)
        ·
          refine ⟨7690142331785468683611611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5126761554523645789074407 7690142331785468683611611)
          ·
            refine ⟨11535213497678203025417417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7690142331785468683611611 11535213497678203025417417)
            ·
              refine ⟨8651410123258652269063063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11535213497678203025417417 8651410123258652269063063)
              ·
                refine ⟨12977115184887978403594595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8651410123258652269063063 12977115184887978403594595)
                ·
                  refine ⟨19465672777331967605391893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12977115184887978403594595 19465672777331967605391893)
                  ·
                    refine ⟨912453411437435981502745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19465672777331967605391893 912453411437435981502745)
                    ·
                      rfl

theorem cell22_2665495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_2665495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665495 prefixEnd_2665495 := by exact prefixLift 2665495
  have htrace : WordTrace (prefixWord ++ tailWord_2665495) baseStart_2665495 baseEnd_2665495 := by
    simpa [prefixWord, tailWord_2665495, baseEnd_2665495] using wordTrace_append hprefix tailTrace_2665495
  have hstable : (prefixWord ++ tailWord_2665495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665495).length < 2 ^ (prefixWord ++ tailWord_2665495).sum := by decide
  have hdescent : baseEnd_2665495 < baseStart_2665495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665523 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 2, 6]
def baseStart_2665523 : Nat := 118140960795 + 2665523 * 2 ^ 59
def prefixEnd_2665523 : Nat := 4983230072969 + 3 ^ 40 * 2665523 * 2
def baseEnd_2665523 : Nat := 912462996409653241802659

theorem tailTrace_2665523 : CollatzResearch.WordTrace tailWord_2665523 prefixEnd_2665523 912462996409653241802659 := by
  unfold tailWord_2665523
  simp only [CollatzResearch.WordTrace]
  refine ⟨97219610722272880930393223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64813073814848587286928815 97219610722272880930393223)
  ·
    refine ⟨145829416083409321395589835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97219610722272880930393223 145829416083409321395589835)
    ·
      refine ⟨218744124125113982093384753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145829416083409321395589835 218744124125113982093384753)
      ·
        refine ⟨164058093093835486570038565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218744124125113982093384753 164058093093835486570038565)
        ·
          refine ⟨30760892455094153731882231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164058093093835486570038565 30760892455094153731882231)
          ·
            refine ⟨46141338682641230597823347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30760892455094153731882231 46141338682641230597823347)
            ·
              refine ⟨69212008023961845896735021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46141338682641230597823347 69212008023961845896735021)
              ·
                refine ⟨25954503008985692211275633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69212008023961845896735021 25954503008985692211275633)
                ·
                  refine ⟨19465877256739269158456725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25954503008985692211275633 19465877256739269158456725)
                  ·
                    refine ⟨912462996409653241802659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19465877256739269158456725 912462996409653241802659)
                    ·
                      rfl

theorem cell22_2665523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 6].length) (baseStart_2665523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665523 prefixEnd_2665523 := by exact prefixLift 2665523
  have htrace : WordTrace (prefixWord ++ tailWord_2665523) baseStart_2665523 baseEnd_2665523 := by
    simpa [prefixWord, tailWord_2665523, baseEnd_2665523] using wordTrace_append hprefix tailTrace_2665523
  have hstable : (prefixWord ++ tailWord_2665523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665523).length < 2 ^ (prefixWord ++ tailWord_2665523).sum := by decide
  have hdescent : baseEnd_2665523 < baseStart_2665523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665632 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 4, 3]
def baseStart_2665632 : Nat := 118140960795 + 2665632 * 2 ^ 59
def prefixEnd_2665632 : Nat := 4983230072969 + 3 ^ 40 * 2665632 * 2
def baseEnd_2665632 : Nat := 912500309337213290827325

theorem tailTrace_2665632 : CollatzResearch.WordTrace tailWord_2665632 prefixEnd_2665632 912500309337213290827325 := by
  unfold tailWord_2665632
  simp only [CollatzResearch.WordTrace]
  refine ⟨48611793139438996273055575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64815724185918661697407433 48611793139438996273055575)
  ·
    refine ⟨72917689709158494409583363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48611793139438996273055575 72917689709158494409583363)
    ·
      refine ⟨109376534563737741614375045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72917689709158494409583363 109376534563737741614375045)
      ·
        refine ⟨20508100230700826552695321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109376534563737741614375045 20508100230700826552695321)
        ·
          refine ⟨15381075173025619914521491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20508100230700826552695321 15381075173025619914521491)
          ·
            refine ⟨23071612759538429871782237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15381075173025619914521491 23071612759538429871782237)
            ·
              refine ⟨8651854784826911201918339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23071612759538429871782237 8651854784826911201918339)
              ·
                refine ⟨12977782177240366802877509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8651854784826911201918339 12977782177240366802877509)
                ·
                  refine ⟨2433334158232568775539533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12977782177240366802877509 2433334158232568775539533)
                  ·
                    refine ⟨912500309337213290827325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2433334158232568775539533 912500309337213290827325)
                    ·
                      rfl

theorem cell22_2665632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 4, 3].length) (baseStart_2665632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665632 prefixEnd_2665632 := by exact prefixLift 2665632
  have htrace : WordTrace (prefixWord ++ tailWord_2665632) baseStart_2665632 baseEnd_2665632 := by
    simpa [prefixWord, tailWord_2665632, baseEnd_2665632] using wordTrace_append hprefix tailTrace_2665632
  have hstable : (prefixWord ++ tailWord_2665632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665632).length < 2 ^ (prefixWord ++ tailWord_2665632).sum := by decide
  have hdescent : baseEnd_2665632 < baseStart_2665632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665634 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 6]
def baseStart_2665634 : Nat := 118140960795 + 2665634 * 2 ^ 59
def prefixEnd_2665634 : Nat := 4983230072969 + 3 ^ 40 * 2665634 * 2
def baseEnd_2665634 : Nat := 304166997992695317425773

theorem tailTrace_2665634 : CollatzResearch.WordTrace tailWord_2665634 prefixEnd_2665634 304166997992695317425773 := by
  unfold tailWord_2665634
  simp only [CollatzResearch.WordTrace]
  refine ⟨24305914806217686721920989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64815772816580497925122637 24305914806217686721920989)
  ·
    refine ⟨9114718052331632520720371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24305914806217686721920989 9114718052331632520720371)
    ·
      refine ⟨13672077078497448781080557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9114718052331632520720371 13672077078497448781080557)
      ·
        refine ⟨5127028904436543292905209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13672077078497448781080557 5127028904436543292905209)
        ·
          refine ⟨3845271678327407469678907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5127028904436543292905209 3845271678327407469678907)
          ·
            refine ⟨5767907517491111204518361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3845271678327407469678907 5767907517491111204518361)
            ·
              refine ⟨4325930638118333403388771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5767907517491111204518361 4325930638118333403388771)
              ·
                refine ⟨6488895957177500105083157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4325930638118333403388771 6488895957177500105083157)
                ·
                  refine ⟨304166997992695317425773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6488895957177500105083157 304166997992695317425773)
                  ·
                    rfl

theorem cell22_2665634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_2665634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665634 prefixEnd_2665634 := by exact prefixLift 2665634
  have htrace : WordTrace (prefixWord ++ tailWord_2665634) baseStart_2665634 baseEnd_2665634 := by
    simpa [prefixWord, tailWord_2665634, baseEnd_2665634] using wordTrace_append hprefix tailTrace_2665634
  have hstable : (prefixWord ++ tailWord_2665634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665634).length < 2 ^ (prefixWord ++ tailWord_2665634).sum := by decide
  have hdescent : baseEnd_2665634 < baseStart_2665634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665649 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 1, 5]
def baseStart_2665649 : Nat := 118140960795 + 2665649 * 2 ^ 59
def prefixEnd_2665649 : Nat := 4983230072969 + 3 ^ 40 * 2665649 * 2
def baseEnd_2665649 : Nat := 912506128784630913152273

theorem tailTrace_2665649 : CollatzResearch.WordTrace tailWord_2665649 prefixEnd_2665649 912506128784630913152273 := by
  unfold tailWord_2665649
  simp only [CollatzResearch.WordTrace]
  refine ⟨97224206319816404449480001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64816137546544269632986667 97224206319816404449480001)
  ·
    refine ⟨72918154739862303337110001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97224206319816404449480001 72918154739862303337110001)
    ·
      refine ⟨54688616054896727502832501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72918154739862303337110001 54688616054896727502832501)
      ·
        refine ⟨5127057755146568203390547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54688616054896727502832501 5127057755146568203390547)
        ·
          refine ⟨7690586632719852305085821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5127057755146568203390547 7690586632719852305085821)
          ·
            refine ⟨2883969987269944614407183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7690586632719852305085821 2883969987269944614407183)
            ·
              refine ⟨4325954980904916921610775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2883969987269944614407183 4325954980904916921610775)
              ·
                refine ⟨6488932471357375382416163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4325954980904916921610775 6488932471357375382416163)
                ·
                  refine ⟨9733398707036063073624245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6488932471357375382416163 9733398707036063073624245)
                  ·
                    refine ⟨912506128784630913152273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9733398707036063073624245 912506128784630913152273)
                    ·
                      rfl

theorem cell22_2665649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_2665649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665649 prefixEnd_2665649 := by exact prefixLift 2665649
  have htrace : WordTrace (prefixWord ++ tailWord_2665649) baseStart_2665649 baseEnd_2665649 := by
    simpa [prefixWord, tailWord_2665649, baseEnd_2665649] using wordTrace_append hprefix tailTrace_2665649
  have hstable : (prefixWord ++ tailWord_2665649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665649).length < 2 ^ (prefixWord ++ tailWord_2665649).sum := by decide
  have hdescent : baseEnd_2665649 < baseStart_2665649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665662 : List Nat := [4, 2, 1, 1, 3, 2, 1, 8]
def baseStart_2665662 : Nat := 118140960795 + 2665662 * 2 ^ 59
def prefixEnd_2665662 : Nat := 4983230072969 + 3 ^ 40 * 2665662 * 2
def baseEnd_2665662 : Nat := 101390064327811468064137

theorem tailTrace_2665662 : CollatzResearch.WordTrace tailWord_2665662 prefixEnd_2665662 101390064327811468064137 := by
  unfold tailWord_2665662
  simp only [CollatzResearch.WordTrace]
  refine ⟨12153085058596163458712905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64816453645846205113135493 12153085058596163458712905)
  ·
    refine ⟨9114813793947122594034679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12153085058596163458712905 9114813793947122594034679)
    ·
      refine ⟨13672220690920683891052019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9114813793947122594034679 13672220690920683891052019)
      ·
        refine ⟨20508331036381025836578029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13672220690920683891052019 20508331036381025836578029)
        ·
          refine ⟨7690624138642884688716761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20508331036381025836578029 7690624138642884688716761)
          ·
            refine ⟨5767968103982163516537571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7690624138642884688716761 5767968103982163516537571)
            ·
              refine ⟨8651952155973245274806357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767968103982163516537571 8651952155973245274806357)
              ·
                refine ⟨101390064327811468064137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8651952155973245274806357 101390064327811468064137)
                ·
                  rfl

theorem cell22_2665662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_2665662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665662 prefixEnd_2665662 := by exact prefixLift 2665662
  have htrace : WordTrace (prefixWord ++ tailWord_2665662) baseStart_2665662 baseEnd_2665662 := by
    simpa [prefixWord, tailWord_2665662, baseEnd_2665662] using wordTrace_append hprefix tailTrace_2665662
  have hstable : (prefixWord ++ tailWord_2665662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665662).length < 2 ^ (prefixWord ++ tailWord_2665662).sum := by decide
  have hdescent : baseEnd_2665662 < baseStart_2665662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665668 : List Nat := [2, 3, 3, 1, 4, 1, 1, 3, 4]
def baseStart_2665668 : Nat := 118140960795 + 2665668 * 2 ^ 59
def prefixEnd_2665668 : Nat := 4983230072969 + 3 ^ 40 * 2665668 * 2
def baseEnd_2665668 : Nat := 304170877624307065642405

theorem tailTrace_2665668 : CollatzResearch.WordTrace tailWord_2665668 prefixEnd_2665668 304170877624307065642405 := by
  unfold tailWord_2665668
  simp only [CollatzResearch.WordTrace]
  refine ⟨48612449653373785347210829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64816599537831713796281105 48612449653373785347210829)
  ·
    refine ⟨18229668620015169505204061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48612449653373785347210829 18229668620015169505204061)
    ·
      refine ⟨6836125732505688564451523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18229668620015169505204061 6836125732505688564451523)
      ·
        refine ⟨10254188598758532846677285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6836125732505688564451523 10254188598758532846677285)
        ·
          refine ⟨1922660362267224908751991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10254188598758532846677285 1922660362267224908751991)
          ·
            refine ⟨2883990543400837363127987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922660362267224908751991 2883990543400837363127987)
            ·
              refine ⟨4325985815101256044691981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2883990543400837363127987 4325985815101256044691981)
              ·
                refine ⟨1622244680662971016759493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4325985815101256044691981 1622244680662971016759493)
                ·
                  refine ⟨304170877624307065642405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1622244680662971016759493 304170877624307065642405)
                  ·
                    rfl

theorem cell22_2665668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_2665668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665668 prefixEnd_2665668 := by exact prefixLift 2665668
  have htrace : WordTrace (prefixWord ++ tailWord_2665668) baseStart_2665668 baseEnd_2665668 := by
    simpa [prefixWord, tailWord_2665668, baseEnd_2665668] using wordTrace_append hprefix tailTrace_2665668
  have hstable : (prefixWord ++ tailWord_2665668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665668).length < 2 ^ (prefixWord ++ tailWord_2665668).sum := by decide
  have hdescent : baseEnd_2665668 < baseStart_2665668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665707 : List Nat := [1, 1, 1, 1, 2, 7, 1, 3, 5]
def baseStart_2665707 : Nat := 118140960795 + 2665707 * 2 ^ 59
def prefixEnd_2665707 : Nat := 4983230072969 + 3 ^ 40 * 2665707 * 2
def baseEnd_2665707 : Nat := 304175327789979365067365

theorem tailTrace_2665707 : CollatzResearch.WordTrace tailWord_2665707 prefixEnd_2665707 304175327789979365067365 := by
  unfold tailWord_2665707
  simp only [CollatzResearch.WordTrace]
  refine ⟨97226321753606280355091375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64817547835737520236727583 97226321753606280355091375)
  ·
    refine ⟨145839482630409420532637063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97226321753606280355091375 145839482630409420532637063)
    ·
      refine ⟨218759223945614130798955595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145839482630409420532637063 218759223945614130798955595)
      ·
        refine ⟨328138835918421196198433393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218759223945614130798955595 328138835918421196198433393)
        ·
          refine ⟨246104126938815897148825045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328138835918421196198433393 246104126938815897148825045)
          ·
            refine ⟨5768065475128497589425587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 246104126938815897148825045 5768065475128497589425587)
            ·
              refine ⟨8652098212692746384138381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5768065475128497589425587 8652098212692746384138381)
              ·
                refine ⟨3244536829759779894051893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8652098212692746384138381 3244536829759779894051893)
                ·
                  refine ⟨304175327789979365067365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3244536829759779894051893 304175327789979365067365)
                  ·
                    rfl

theorem cell22_2665707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 5].length) (baseStart_2665707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665707 prefixEnd_2665707 := by exact prefixLift 2665707
  have htrace : WordTrace (prefixWord ++ tailWord_2665707) baseStart_2665707 baseEnd_2665707 := by
    simpa [prefixWord, tailWord_2665707, baseEnd_2665707] using wordTrace_append hprefix tailTrace_2665707
  have hstable : (prefixWord ++ tailWord_2665707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665707).length < 2 ^ (prefixWord ++ tailWord_2665707).sum := by decide
  have hdescent : baseEnd_2665707 < baseStart_2665707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665829 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 3, 3]
def baseStart_2665829 : Nat := 118140960795 + 2665829 * 2 ^ 59
def prefixEnd_2665829 : Nat := 4983230072969 + 3 ^ 40 * 2665829 * 2
def baseEnd_2665829 : Nat := 912567746463170443651721

theorem tailTrace_2665829 : CollatzResearch.WordTrace tailWord_2665829 prefixEnd_2665829 912567746463170443651721 := by
  unfold tailWord_2665829
  simp only [CollatzResearch.WordTrace]
  refine ⟨97230771459164295191032541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64820514306109530127355027 97230771459164295191032541)
  ·
    refine ⟨36461539297186610696637203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97230771459164295191032541 36461539297186610696637203)
    ·
      refine ⟨54692308945779916044955805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36461539297186610696637203 54692308945779916044955805)
      ·
        refine ⟨20509615854667468516858427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54692308945779916044955805 20509615854667468516858427)
        ·
          refine ⟨30764423782001202775287641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20509615854667468516858427 30764423782001202775287641)
          ·
            refine ⟨23073317836500902081465731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30764423782001202775287641 23073317836500902081465731)
            ·
              refine ⟨34609976754751353122198597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23073317836500902081465731 34609976754751353122198597)
              ·
                refine ⟨6489370641515878710412237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34609976754751353122198597 6489370641515878710412237)
                ·
                  refine ⟨2433513990568454516404589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6489370641515878710412237 2433513990568454516404589)
                  ·
                    refine ⟨912567746463170443651721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2433513990568454516404589 912567746463170443651721)
                    ·
                      rfl

theorem cell22_2665829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_2665829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665829 prefixEnd_2665829 := by exact prefixLift 2665829
  have htrace : WordTrace (prefixWord ++ tailWord_2665829) baseStart_2665829 baseEnd_2665829 := by
    simpa [prefixWord, tailWord_2665829, baseEnd_2665829] using wordTrace_append hprefix tailTrace_2665829
  have hstable : (prefixWord ++ tailWord_2665829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665829).length < 2 ^ (prefixWord ++ tailWord_2665829).sum := by decide
  have hdescent : baseEnd_2665829 < baseStart_2665829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665831 : List Nat := [1, 1, 5, 1, 4, 2, 2, 6]
def baseStart_2665831 : Nat := 118140960795 + 2665831 * 2 ^ 59
def prefixEnd_2665831 : Nat := 4983230072969 + 3 ^ 40 * 2665831 * 2
def baseEnd_2665831 : Nat := 101396492344893678344635

theorem tailTrace_2665831 : CollatzResearch.WordTrace tailWord_2665831 prefixEnd_2665831 101396492344893678344635 := by
  unfold tailWord_2665831
  simp only [CollatzResearch.WordTrace]
  refine ⟨97230844405157049532605347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64820562936771366355070231 97230844405157049532605347)
  ·
    refine ⟨145846266607735574298908021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97230844405157049532605347 145846266607735574298908021)
    ·
      refine ⟨13673087494475210090522627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145846266607735574298908021 13673087494475210090522627)
      ·
        refine ⟨20509631241712815135783941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13673087494475210090522627 20509631241712815135783941)
        ·
          refine ⟨3845555857821152837959489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20509631241712815135783941 3845555857821152837959489)
          ·
            refine ⟨2884166893365864628469617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3845555857821152837959489 2884166893365864628469617)
            ·
              refine ⟨2163125170024398471352213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2884166893365864628469617 2163125170024398471352213)
              ·
                refine ⟨101396492344893678344635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2163125170024398471352213 101396492344893678344635)
                ·
                  rfl

theorem cell22_2665831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 6].length) (baseStart_2665831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665831 prefixEnd_2665831 := by exact prefixLift 2665831
  have htrace : WordTrace (prefixWord ++ tailWord_2665831) baseStart_2665831 baseEnd_2665831 := by
    simpa [prefixWord, tailWord_2665831, baseEnd_2665831] using wordTrace_append hprefix tailTrace_2665831
  have hstable : (prefixWord ++ tailWord_2665831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665831).length < 2 ^ (prefixWord ++ tailWord_2665831).sum := by decide
  have hdescent : baseEnd_2665831 < baseStart_2665831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665842 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 9]
def baseStart_2665842 : Nat := 118140960795 + 2665842 * 2 ^ 59
def prefixEnd_2665842 : Nat := 4983230072969 + 3 ^ 40 * 2665842 * 2
def baseEnd_2665842 : Nat := 304190732209614247692227

theorem tailTrace_2665842 : CollatzResearch.WordTrace tailWord_2665842 prefixEnd_2665842 304190732209614247692227 := by
  unfold tailWord_2665842
  simp only [CollatzResearch.WordTrace]
  refine ⟨24307811402029299602813945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64820830405411465607503853 24307811402029299602813945)
  ·
    refine ⟨18230858551521974702110459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24307811402029299602813945 18230858551521974702110459)
    ·
      refine ⟨27346287827282962053165689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18230858551521974702110459 27346287827282962053165689)
      ·
        refine ⟨20509715870462221539874267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27346287827282962053165689 20509715870462221539874267)
        ·
          refine ⟨30764573805693332309811401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20509715870462221539874267 30764573805693332309811401)
          ·
            refine ⟨23073430354269999232358551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30764573805693332309811401 23073430354269999232358551)
            ·
              refine ⟨34610145531404998848537827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23073430354269999232358551 34610145531404998848537827)
              ·
                refine ⟨51915218297107498272806741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34610145531404998848537827 51915218297107498272806741)
                ·
                  refine ⟨304190732209614247692227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51915218297107498272806741 304190732209614247692227)
                  ·
                    rfl

theorem cell22_2665842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_2665842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665842 prefixEnd_2665842 := by exact prefixLift 2665842
  have htrace : WordTrace (prefixWord ++ tailWord_2665842) baseStart_2665842 baseEnd_2665842 := by
    simpa [prefixWord, tailWord_2665842, baseEnd_2665842] using wordTrace_append hprefix tailTrace_2665842
  have hstable : (prefixWord ++ tailWord_2665842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665842).length < 2 ^ (prefixWord ++ tailWord_2665842).sum := by decide
  have hdescent : baseEnd_2665842 < baseStart_2665842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665876 : List Nat := [2, 4, 2, 1, 2, 2, 1, 3, 5]
def baseStart_2665876 : Nat := 118140960795 + 2665876 * 2 ^ 59
def prefixEnd_2665876 : Nat := 4983230072969 + 3 ^ 40 * 2665876 * 2
def baseEnd_2665876 : Nat := 304194611841225995908859

theorem tailTrace_2665876 : CollatzResearch.WordTrace tailWord_2665876 prefixEnd_2665876 304194611841225995908859 := by
  unfold tailWord_2665876
  simp only [CollatzResearch.WordTrace]
  refine ⟨48616242844997011108996741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64821657126662681478662321 48616242844997011108996741)
  ·
    refine ⟨9115545533436939582936889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48616242844997011108996741 9115545533436939582936889)
    ·
      refine ⟨6836659150077704687202667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9115545533436939582936889 6836659150077704687202667)
      ·
        refine ⟨10254988725116557030804001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6836659150077704687202667 10254988725116557030804001)
        ·
          refine ⟨7691241543837417773103001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10254988725116557030804001 7691241543837417773103001)
          ·
            refine ⟨5768431157878063329827251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7691241543837417773103001 5768431157878063329827251)
            ·
              refine ⟨8652646736817094994740877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5768431157878063329827251 8652646736817094994740877)
              ·
                refine ⟨3244742526306410623027829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8652646736817094994740877 3244742526306410623027829)
                ·
                  refine ⟨304194611841225995908859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3244742526306410623027829 304194611841225995908859)
                  ·
                    rfl

theorem cell22_2665876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_2665876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665876 prefixEnd_2665876 := by exact prefixLift 2665876
  have htrace : WordTrace (prefixWord ++ tailWord_2665876) baseStart_2665876 baseEnd_2665876 := by
    simpa [prefixWord, tailWord_2665876, baseEnd_2665876] using wordTrace_append hprefix tailTrace_2665876
  have hstable : (prefixWord ++ tailWord_2665876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665876).length < 2 ^ (prefixWord ++ tailWord_2665876).sum := by decide
  have hdescent : baseEnd_2665876 < baseStart_2665876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665919 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 4, 3]
def baseStart_2665919 : Nat := 118140960795 + 2665919 * 2 ^ 59
def prefixEnd_2665919 : Nat := 4983230072969 + 3 ^ 40 * 2665919 * 2
def baseEnd_2665919 : Nat := 912598555302440208901445

theorem tailTrace_2665919 : CollatzResearch.WordTrace tailWord_2665919 prefixEnd_2665919 912598555302440208901445 := by
  unfold tailWord_2665919
  simp only [CollatzResearch.WordTrace]
  refine ⟨97234054028838240561808811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64822702685892160374539207 97234054028838240561808811)
  ·
    refine ⟨145851081043257360842713217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97234054028838240561808811 145851081043257360842713217)
    ·
      refine ⟨109388310782443020632034913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145851081043257360842713217 109388310782443020632034913)
      ·
        refine ⟨82041233086832265474026185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109388310782443020632034913 82041233086832265474026185)
        ·
          refine ⟨61530924815124199105519639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82041233086832265474026185 61530924815124199105519639)
          ·
            refine ⟨92296387222686298658279459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61530924815124199105519639 92296387222686298658279459)
            ·
              refine ⟨138444580834029447987419189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92296387222686298658279459 138444580834029447987419189)
              ·
                refine ⟨12979179453190260748820549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138444580834029447987419189 12979179453190260748820549)
                ·
                  refine ⟨2433596147473173890403853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12979179453190260748820549 2433596147473173890403853)
                  ·
                    refine ⟨912598555302440208901445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2433596147473173890403853 912598555302440208901445)
                    ·
                      rfl

theorem cell22_2665919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 3].length) (baseStart_2665919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665919 prefixEnd_2665919 := by exact prefixLift 2665919
  have htrace : WordTrace (prefixWord ++ tailWord_2665919) baseStart_2665919 baseEnd_2665919 := by
    simpa [prefixWord, tailWord_2665919, baseEnd_2665919] using wordTrace_append hprefix tailTrace_2665919
  have hstable : (prefixWord ++ tailWord_2665919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665919).length < 2 ^ (prefixWord ++ tailWord_2665919).sum := by decide
  have hdescent : baseEnd_2665919 < baseStart_2665919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665934 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_2665934 : Nat := 118140960795 + 2665934 * 2 ^ 59
def prefixEnd_2665934 : Nat := 4983230072969 + 3 ^ 40 * 2665934 * 2
def baseEnd_2665934 : Nat := 912603690108985169776399

theorem tailTrace_2665934 : CollatzResearch.WordTrace tailWord_2665934 prefixEnd_2665934 912603690108985169776399 := by
  unfold tailWord_2665934
  simp only [CollatzResearch.WordTrace]
  refine ⟨12154325140472987265450607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64823067415855932082403237 12154325140472987265450607)
  ·
    refine ⟨18231487710709480898175911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12154325140472987265450607 18231487710709480898175911)
    ·
      refine ⟨27347231566064221347263867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18231487710709480898175911 27347231566064221347263867)
      ·
        refine ⟨41020847349096332020895801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27347231566064221347263867 41020847349096332020895801)
        ·
          refine ⟨30765635511822249015671851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41020847349096332020895801 30765635511822249015671851)
          ·
            refine ⟨46148453267733373523507777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30765635511822249015671851 46148453267733373523507777)
            ·
              refine ⟨34611339950800030142630833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46148453267733373523507777 34611339950800030142630833)
              ·
                refine ⟨25958504963100022606973125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34611339950800030142630833 25958504963100022606973125)
                ·
                  refine ⟨4867219680581254238807461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25958504963100022606973125 4867219680581254238807461)
                  ·
                    refine ⟨912603690108985169776399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4867219680581254238807461 912603690108985169776399)
                    ·
                      rfl

theorem cell22_2665934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_2665934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665934 prefixEnd_2665934 := by exact prefixLift 2665934
  have htrace : WordTrace (prefixWord ++ tailWord_2665934) baseStart_2665934 baseEnd_2665934 := by
    simpa [prefixWord, tailWord_2665934, baseEnd_2665934] using wordTrace_append hprefix tailTrace_2665934
  have hstable : (prefixWord ++ tailWord_2665934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665934).length < 2 ^ (prefixWord ++ tailWord_2665934).sum := by decide
  have hdescent : baseEnd_2665934 < baseStart_2665934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665947 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 6, 7]
def baseStart_2665947 : Nat := 118140960795 + 2665947 * 2 ^ 59
def prefixEnd_2665947 : Nat := 4983230072969 + 3 ^ 40 * 2665947 * 2
def baseEnd_2665947 : Nat := 912608140274657469201359

theorem tailTrace_2665947 : CollatzResearch.WordTrace tailWord_2665947 prefixEnd_2665947 912608140274657469201359 := by
  unfold tailWord_2665947
  simp only [CollatzResearch.WordTrace]
  refine ⟨97235075272736801343828095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64823383515157867562552063 97235075272736801343828095)
  ·
    refine ⟨145852612909105202015742143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97235075272736801343828095 145852612909105202015742143)
    ·
      refine ⟨218778919363657803023613215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145852612909105202015742143 218778919363657803023613215)
      ·
        refine ⟨328168379045486704535419823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218778919363657803023613215 328168379045486704535419823)
        ·
          refine ⟨492252568568230056803129735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328168379045486704535419823 492252568568230056803129735)
          ·
            refine ⟨738378852852345085204694603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492252568568230056803129735 738378852852345085204694603)
            ·
              refine ⟨1107568279278517627807041905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738378852852345085204694603 1107568279278517627807041905)
              ·
                refine ⟨830676209458888220855281429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1107568279278517627807041905 830676209458888220855281429)
                ·
                  refine ⟨38937947318385385352591317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 830676209458888220855281429 38937947318385385352591317)
                  ·
                    refine ⟨912608140274657469201359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38937947318385385352591317 912608140274657469201359)
                    ·
                      rfl

theorem cell22_2665947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_2665947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665947 prefixEnd_2665947 := by exact prefixLift 2665947
  have htrace : WordTrace (prefixWord ++ tailWord_2665947) baseStart_2665947 baseEnd_2665947 := by
    simpa [prefixWord, tailWord_2665947, baseEnd_2665947] using wordTrace_append hprefix tailTrace_2665947
  have hstable : (prefixWord ++ tailWord_2665947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665947).length < 2 ^ (prefixWord ++ tailWord_2665947).sum := by decide
  have hdescent : baseEnd_2665947 < baseStart_2665947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665970 : List Nat := [3, 2, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_2665970 : Nat := 118140960795 + 2665970 * 2 ^ 59
def prefixEnd_2665970 : Nat := 4983230072969 + 3 ^ 40 * 2665970 * 2
def baseEnd_2665970 : Nat := 912616013644693075876289

theorem tailTrace_2665970 : CollatzResearch.WordTrace tailWord_2665970 prefixEnd_2665970 912616013644693075876289 := by
  unfold tailWord_2665970
  simp only [CollatzResearch.WordTrace]
  refine ⟨24308978537913369067978841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64823942767768984181276909 24308978537913369067978841)
  ·
    refine ⟨18231733903435026800984131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24308978537913369067978841 18231733903435026800984131)
    ·
      refine ⟨27347600855152540201476197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18231733903435026800984131 27347600855152540201476197)
      ·
        refine ⟨5127675160341101287776787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27347600855152540201476197 5127675160341101287776787)
        ·
          refine ⟨7691512740511651931665181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5127675160341101287776787 7691512740511651931665181)
          ·
            refine ⟨2884317277691869474374443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7691512740511651931665181 2884317277691869474374443)
            ·
              refine ⟨4326475916537804211561665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2884317277691869474374443 4326475916537804211561665)
              ·
                refine ⟨3244856937403353158671249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4326475916537804211561665 3244856937403353158671249)
                ·
                  refine ⟨2433642703052514869003437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3244856937403353158671249 2433642703052514869003437)
                  ·
                    refine ⟨912616013644693075876289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2433642703052514869003437 912616013644693075876289)
                    ·
                      rfl

theorem cell22_2665970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_2665970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665970 prefixEnd_2665970 := by exact prefixLift 2665970
  have htrace : WordTrace (prefixWord ++ tailWord_2665970) baseStart_2665970 baseEnd_2665970 := by
    simpa [prefixWord, tailWord_2665970, baseEnd_2665970] using wordTrace_append hprefix tailTrace_2665970
  have hstable : (prefixWord ++ tailWord_2665970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665970).length < 2 ^ (prefixWord ++ tailWord_2665970).sum := by decide
  have hdescent : baseEnd_2665970 < baseStart_2665970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665981 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_2665981 : Nat := 118140960795 + 2665981 * 2 ^ 59
def prefixEnd_2665981 : Nat := 4983230072969 + 3 ^ 40 * 2665981 * 2
def baseEnd_2665981 : Nat := 912619779169492713851255

theorem tailTrace_2665981 : CollatzResearch.WordTrace tailWord_2665981 prefixEnd_2665981 912619779169492713851255 := by
  unfold tailWord_2665981
  simp only [CollatzResearch.WordTrace]
  refine ⟨97236315354613625150565797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64824210236409083433710531 97236315354613625150565797)
  ·
    refine ⟨18231809128990054715731087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97236315354613625150565797 18231809128990054715731087)
    ·
      refine ⟨27347713693485082073596631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18231809128990054715731087 27347713693485082073596631)
      ·
        refine ⟨41021570540227623110394947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27347713693485082073596631 41021570540227623110394947)
        ·
          refine ⟨61532355810341434665592421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41021570540227623110394947 61532355810341434665592421)
          ·
            refine ⟨11537316714439018999798579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61532355810341434665592421 11537316714439018999798579)
            ·
              refine ⟨17305975071658528499697869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11537316714439018999798579 17305975071658528499697869)
              ·
                refine ⟨6489740651871948187386701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17305975071658528499697869 6489740651871948187386701)
                ·
                  refine ⟨2433652744451980570270013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6489740651871948187386701 2433652744451980570270013)
                  ·
                    refine ⟨912619779169492713851255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2433652744451980570270013 912619779169492713851255)
                    ·
                      rfl

theorem cell22_2665981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_2665981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665981 prefixEnd_2665981 := by exact prefixLift 2665981
  have htrace : WordTrace (prefixWord ++ tailWord_2665981) baseStart_2665981 baseEnd_2665981 := by
    simpa [prefixWord, tailWord_2665981, baseEnd_2665981] using wordTrace_append hprefix tailTrace_2665981
  have hstable : (prefixWord ++ tailWord_2665981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665981).length < 2 ^ (prefixWord ++ tailWord_2665981).sum := by decide
  have hdescent : baseEnd_2665981 < baseStart_2665981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666045 : List Nat := [1, 4, 1, 3, 3, 2, 2, 1, 5]
def baseStart_2666045 : Nat := 118140960795 + 2666045 * 2 ^ 59
def prefixEnd_2666045 : Nat := 4983230072969 + 3 ^ 40 * 2666045 * 2
def baseEnd_2666045 : Nat := 304213895892472626750353

theorem tailTrace_2666045 : CollatzResearch.WordTrace tailWord_2666045 prefixEnd_2666045 304213895892472626750353 := by
  unfold tailWord_2666045
  simp only [CollatzResearch.WordTrace]
  refine ⟨97238649626381764080895589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64825766417587842720597059 97238649626381764080895589)
  ·
    refine ⟨18232246804946580765167923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97238649626381764080895589 18232246804946580765167923)
    ·
      refine ⟨27348370207419871147751885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18232246804946580765167923 27348370207419871147751885)
      ·
        refine ⟨10255638827782451680406957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27348370207419871147751885 10255638827782451680406957)
        ·
          refine ⟨3845864560418419380152609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10255638827782451680406957 3845864560418419380152609)
          ·
            refine ⟨2884398420313814535114457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3845864560418419380152609 2884398420313814535114457)
            ·
              refine ⟨2163298815235360901335843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2884398420313814535114457 2163298815235360901335843)
              ·
                refine ⟨3244948222853041352003765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2163298815235360901335843 3244948222853041352003765)
                ·
                  refine ⟨304213895892472626750353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3244948222853041352003765 304213895892472626750353)
                  ·
                    rfl

theorem cell22_2666045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_2666045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666045 prefixEnd_2666045 := by exact prefixLift 2666045
  have htrace : WordTrace (prefixWord ++ tailWord_2666045) baseStart_2666045 baseEnd_2666045 := by
    simpa [prefixWord, tailWord_2666045, baseEnd_2666045] using wordTrace_append hprefix tailTrace_2666045
  have hstable : (prefixWord ++ tailWord_2666045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666045).length < 2 ^ (prefixWord ++ tailWord_2666045).sum := by decide
  have hdescent : baseEnd_2666045 < baseStart_2666045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666071 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 1, 5]
def baseStart_2666071 : Nat := 118140960795 + 2666071 * 2 ^ 59
def prefixEnd_2666071 : Nat := 4983230072969 + 3 ^ 40 * 2666071 * 2
def baseEnd_2666071 : Nat := 912650588008762479100979

theorem tailTrace_2666071 : CollatzResearch.WordTrace tailWord_2666071 prefixEnd_2666071 912650588008762479100979 := by
  unfold tailWord_2666071
  simp only [CollatzResearch.WordTrace]
  refine ⟨97239597924287570521342067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64826398616191713680894711 97239597924287570521342067)
  ·
    refine ⟨145859396886431355782013101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97239597924287570521342067 145859396886431355782013101)
    ·
      refine ⟨54697273832411758418254913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145859396886431355782013101 54697273832411758418254913)
      ·
        refine ⟨41022955374308818813691185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54697273832411758418254913 41022955374308818813691185)
        ·
          refine ⟨30767216530731614110268389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41022955374308818813691185 30767216530731614110268389)
          ·
            refine ⟨5768853099512177645675323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30767216530731614110268389 5768853099512177645675323)
            ·
              refine ⟨8653279649268266468512985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5768853099512177645675323 8653279649268266468512985)
              ·
                refine ⟨6489959736951199851384739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8653279649268266468512985 6489959736951199851384739)
                ·
                  refine ⟨9734939605426799777077109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6489959736951199851384739 9734939605426799777077109)
                  ·
                    refine ⟨912650588008762479100979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9734939605426799777077109 912650588008762479100979)
                    ·
                      rfl

theorem cell22_2666071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_2666071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666071 prefixEnd_2666071 := by exact prefixLift 2666071
  have htrace : WordTrace (prefixWord ++ tailWord_2666071) baseStart_2666071 baseEnd_2666071 := by
    simpa [prefixWord, tailWord_2666071, baseEnd_2666071] using wordTrace_append hprefix tailTrace_2666071
  have hstable : (prefixWord ++ tailWord_2666071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666071).length < 2 ^ (prefixWord ++ tailWord_2666071).sum := by decide
  have hdescent : baseEnd_2666071 < baseStart_2666071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666084 : List Nat := [2, 3, 1, 1, 2, 13]
def baseStart_2666084 : Nat := 118140960795 + 2666084 * 2 ^ 59
def prefixEnd_2666084 : Nat := 4983230072969 + 3 ^ 40 * 2666084 * 2
def baseEnd_2666084 : Nat := 11267346150301663932419

theorem tailTrace_2666084 : CollatzResearch.WordTrace tailWord_2666084 prefixEnd_2666084 11267346150301663932419 := by
  unfold tailWord_2666084
  simp only [CollatzResearch.WordTrace]
  refine ⟨48620036036620236870782653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64826714715493649161043537 48620036036620236870782653)
  ·
    refine ⟨18232513513732588826543495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48620036036620236870782653 18232513513732588826543495)
    ·
      refine ⟨27348770270598883239815243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18232513513732588826543495 27348770270598883239815243)
      ·
        refine ⟨41023155405898324859722865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27348770270598883239815243 41023155405898324859722865)
        ·
          refine ⟨30767366554423743644792149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41023155405898324859722865 30767366554423743644792149)
          ·
            refine ⟨11267346150301663932419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 30767366554423743644792149 11267346150301663932419)
            ·
              rfl

theorem cell22_2666084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 13].length) (baseStart_2666084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666084 prefixEnd_2666084 := by exact prefixLift 2666084
  have htrace : WordTrace (prefixWord ++ tailWord_2666084) baseStart_2666084 baseEnd_2666084 := by
    simpa [prefixWord, tailWord_2666084, baseEnd_2666084] using wordTrace_append hprefix tailTrace_2666084
  have hstable : (prefixWord ++ tailWord_2666084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666084).length < 2 ^ (prefixWord ++ tailWord_2666084).sum := by decide
  have hdescent : baseEnd_2666084 < baseStart_2666084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666090 : List Nat := [3, 1, 3, 2, 1, 2, 4, 2, 4]
def baseStart_2666090 : Nat := 118140960795 + 2666090 * 2 ^ 59
def prefixEnd_2666090 : Nat := 4983230072969 + 3 ^ 40 * 2666090 * 2
def baseEnd_2666090 : Nat := 304219030699017587625307

theorem tailTrace_2666090 : CollatzResearch.WordTrace tailWord_2666090 prefixEnd_2666090 304219030699017587625307 := by
  unfold tailWord_2666090
  simp only [CollatzResearch.WordTrace]
  refine ⟨24310072727804684191570931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64826860607479157844189149 24310072727804684191570931)
  ·
    refine ⟨36465109091707026287356397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24310072727804684191570931 36465109091707026287356397)
    ·
      refine ⟨13674415909390134857758649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36465109091707026287356397 13674415909390134857758649)
      ·
        refine ⟨10255811932042601143318987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13674415909390134857758649 10255811932042601143318987)
        ·
          refine ⟨15383717898063901714978481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10255811932042601143318987 15383717898063901714978481)
          ·
            refine ⟨11537788423547926286233861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15383717898063901714978481 11537788423547926286233861)
            ·
              refine ⟨2163335329415236178668849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11537788423547926286233861 2163335329415236178668849)
              ·
                refine ⟨1622501497061427134001637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2163335329415236178668849 1622501497061427134001637)
                ·
                  refine ⟨304219030699017587625307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1622501497061427134001637 304219030699017587625307)
                  ·
                    rfl

theorem cell22_2666090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_2666090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666090 prefixEnd_2666090 := by exact prefixLift 2666090
  have htrace : WordTrace (prefixWord ++ tailWord_2666090) baseStart_2666090 baseEnd_2666090 := by
    simpa [prefixWord, tailWord_2666090, baseEnd_2666090] using wordTrace_append hprefix tailTrace_2666090
  have hstable : (prefixWord ++ tailWord_2666090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666090).length < 2 ^ (prefixWord ++ tailWord_2666090).sum := by decide
  have hdescent : baseEnd_2666090 < baseStart_2666090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666163 : List Nat := [1, 1, 1, 2, 3, 3, 5, 1, 5]
def baseStart_2666163 : Nat := 118140960795 + 2666163 * 2 ^ 59
def prefixEnd_2666163 : Nat := 4983230072969 + 3 ^ 40 * 2666163 * 2
def baseEnd_2666163 : Nat := 304227360496301635266899

theorem tailTrace_2666163 : CollatzResearch.WordTrace tailWord_2666163 prefixEnd_2666163 304227360496301635266899 := by
  unfold tailWord_2666163
  simp only [CollatzResearch.WordTrace]
  refine ⟨97242953439954270233691143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64828635626636180155794095 97242953439954270233691143)
  ·
    refine ⟨145864430159931405350536715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97242953439954270233691143 145864430159931405350536715)
    ·
      refine ⟨218796645239897108025805073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145864430159931405350536715 218796645239897108025805073)
      ·
        refine ⟨164097483929922831019353805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218796645239897108025805073 164097483929922831019353805)
        ·
          refine ⟨61536556473721061632257677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164097483929922831019353805 61536556473721061632257677)
          ·
            refine ⟨23076208677645398112096629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61536556473721061632257677 23076208677645398112096629)
            ·
              refine ⟨2163394563529256073009059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23076208677645398112096629 2163394563529256073009059)
              ·
                refine ⟨3245091845293884109513589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2163394563529256073009059 3245091845293884109513589)
                ·
                  refine ⟨304227360496301635266899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3245091845293884109513589 304227360496301635266899)
                  ·
                    rfl

theorem cell22_2666163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 5].length) (baseStart_2666163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666163 prefixEnd_2666163 := by exact prefixLift 2666163
  have htrace : WordTrace (prefixWord ++ tailWord_2666163) baseStart_2666163 baseEnd_2666163 := by
    simpa [prefixWord, tailWord_2666163, baseEnd_2666163] using wordTrace_append hprefix tailTrace_2666163
  have hstable : (prefixWord ++ tailWord_2666163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666163).length < 2 ^ (prefixWord ++ tailWord_2666163).sum := by decide
  have hdescent : baseEnd_2666163 < baseStart_2666163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666193 : List Nat := [1, 2, 2, 1, 2, 4, 2, 3, 1, 4]
def baseStart_2666193 : Nat := 118140960795 + 2666193 * 2 ^ 59
def prefixEnd_2666193 : Nat := 4983230072969 + 3 ^ 40 * 2666193 * 2
def baseEnd_2666193 : Nat := 912692351101994827550605

theorem tailTrace_2666193 : CollatzResearch.WordTrace tailWord_2666193 prefixEnd_2666193 912692351101994827550605 := by
  unfold tailWord_2666193
  simp only [CollatzResearch.WordTrace]
  refine ⟨97244047629845585357283233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64829365086563723571522155 97244047629845585357283233)
  ·
    refine ⟨72933035722384189017962425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97244047629845585357283233 72933035722384189017962425)
    ·
      refine ⟨54699776791788141763471819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72933035722384189017962425 54699776791788141763471819)
      ·
        refine ⟨82049665187682212645207729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54699776791788141763471819 82049665187682212645207729)
        ·
          refine ⟨61537248890761659483905797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82049665187682212645207729 61537248890761659483905797)
          ·
            refine ⟨11538234167017811153232337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61537248890761659483905797 11538234167017811153232337)
            ·
              refine ⟨8653675625263358364924253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11538234167017811153232337 8653675625263358364924253)
              ·
                refine ⟨3245128359473759386846595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8653675625263358364924253 3245128359473759386846595)
                ·
                  refine ⟨4867692539210639080269893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3245128359473759386846595 4867692539210639080269893)
                  ·
                    refine ⟨912692351101994827550605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4867692539210639080269893 912692351101994827550605)
                    ·
                      rfl

theorem cell22_2666193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_2666193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666193 prefixEnd_2666193 := by exact prefixLift 2666193
  have htrace : WordTrace (prefixWord ++ tailWord_2666193) baseStart_2666193 baseEnd_2666193 := by
    simpa [prefixWord, tailWord_2666193, baseEnd_2666193] using wordTrace_append hprefix tailTrace_2666193
  have hstable : (prefixWord ++ tailWord_2666193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666193).length < 2 ^ (prefixWord ++ tailWord_2666193).sum := by decide
  have hdescent : baseEnd_2666193 < baseStart_2666193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666208 : List Nat := [2, 1, 1, 3, 1, 2, 2, 6, 4]
def baseStart_2666208 : Nat := 118140960795 + 2666208 * 2 ^ 59
def prefixEnd_2666208 : Nat := 4983230072969 + 3 ^ 40 * 2666208 * 2
def baseEnd_2666208 : Nat := 304232495302846596141853

theorem tailTrace_2666208 : CollatzResearch.WordTrace tailWord_2666208 prefixEnd_2666208 304232495302846596141853 := by
  unfold tailWord_2666208
  simp only [CollatzResearch.WordTrace]
  refine ⟨48622297362395621459539639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64829729816527495279386185 48622297362395621459539639)
  ·
    refine ⟨72933446043593432189309459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48622297362395621459539639 72933446043593432189309459)
    ·
      refine ⟨109400169065390148283964189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72933446043593432189309459 109400169065390148283964189)
      ·
        refine ⟨41025063399521305606486571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109400169065390148283964189 41025063399521305606486571)
        ·
          refine ⟨61537595099281958409729857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41025063399521305606486571 61537595099281958409729857)
          ·
            refine ⟨46153196324461468807297393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61537595099281958409729857 46153196324461468807297393)
            ·
              refine ⟨34614897243346101605473045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46153196324461468807297393 34614897243346101605473045)
              ·
                refine ⟨1622573308281848512756549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34614897243346101605473045 1622573308281848512756549)
                ·
                  refine ⟨304232495302846596141853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1622573308281848512756549 304232495302846596141853)
                  ·
                    rfl

theorem cell22_2666208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 4].length) (baseStart_2666208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666208 prefixEnd_2666208 := by exact prefixLift 2666208
  have htrace : WordTrace (prefixWord ++ tailWord_2666208) baseStart_2666208 baseEnd_2666208 := by
    simpa [prefixWord, tailWord_2666208, baseEnd_2666208] using wordTrace_append hprefix tailTrace_2666208
  have hstable : (prefixWord ++ tailWord_2666208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666208).length < 2 ^ (prefixWord ++ tailWord_2666208).sum := by decide
  have hdescent : baseEnd_2666208 < baseStart_2666208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666236 : List Nat := [2, 2, 2, 1, 3, 1, 1, 10]
def baseStart_2666236 : Nat := 118140960795 + 2666236 * 2 ^ 59
def prefixEnd_2666236 : Nat := 4983230072969 + 3 ^ 40 * 2666236 * 2
def baseEnd_2666236 : Nat := 101411896764528560969497

theorem tailTrace_2666236 : CollatzResearch.WordTrace tailWord_2666236 prefixEnd_2666236 101411896764528560969497 := by
  unfold tailWord_2666236
  simp only [CollatzResearch.WordTrace]
  refine ⟨48622807984344901850549281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64830410645793202467399041 48622807984344901850549281)
  ·
    refine ⟨36467105988258676387911961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48622807984344901850549281 36467105988258676387911961)
    ·
      refine ⟨27350329491194007290933971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36467105988258676387911961 27350329491194007290933971)
      ·
        refine ⟨41025494236791010936400957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27350329491194007290933971 41025494236791010936400957)
        ·
          refine ⟨15384560338796629101150359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41025494236791010936400957 15384560338796629101150359)
          ·
            refine ⟨23076840508194943651725539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15384560338796629101150359 23076840508194943651725539)
            ·
              refine ⟨34615260762292415477588309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23076840508194943651725539 34615260762292415477588309)
              ·
                refine ⟨101411896764528560969497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34615260762292415477588309 101411896764528560969497)
                ·
                  rfl

theorem cell22_2666236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 10].length) (baseStart_2666236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666236 prefixEnd_2666236 := by exact prefixLift 2666236
  have htrace : WordTrace (prefixWord ++ tailWord_2666236) baseStart_2666236 baseEnd_2666236 := by
    simpa [prefixWord, tailWord_2666236, baseEnd_2666236] using wordTrace_append hprefix tailTrace_2666236
  have hstable : (prefixWord ++ tailWord_2666236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666236).length < 2 ^ (prefixWord ++ tailWord_2666236).sum := by decide
  have hdescent : baseEnd_2666236 < baseStart_2666236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666343 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 6]
def baseStart_2666343 : Nat := 118140960795 + 2666343 * 2 ^ 59
def prefixEnd_2666343 : Nat := 4983230072969 + 3 ^ 40 * 2666343 * 2
def baseEnd_2666343 : Nat := 304247899722481478766715

theorem tailTrace_2666343 : CollatzResearch.WordTrace tailWord_2666343 prefixEnd_2666343 304247899722481478766715 := by
  unfold tailWord_2666343
  simp only [CollatzResearch.WordTrace]
  refine ⟨97249518579302160975243683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64833012386201440650162455 97249518579302160975243683)
  ·
    refine ⟨145874277868953241462865525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97249518579302160975243683 145874277868953241462865525)
    ·
      refine ⟨13675713550214366387143643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145874277868953241462865525 13675713550214366387143643)
      ·
        refine ⟨20513570325321549580715465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13675713550214366387143643 20513570325321549580715465)
        ·
          refine ⟨15385177743991162185536599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20513570325321549580715465 15385177743991162185536599)
          ·
            refine ⟨23077766615986743278304899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15385177743991162185536599 23077766615986743278304899)
            ·
              refine ⟨34616649923980114917457349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23077766615986743278304899 34616649923980114917457349)
              ·
                refine ⟨6490621860746271547023253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34616649923980114917457349 6490621860746271547023253)
                ·
                  refine ⟨304247899722481478766715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6490621860746271547023253 304247899722481478766715)
                  ·
                    rfl

theorem cell22_2666343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 6].length) (baseStart_2666343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666343 prefixEnd_2666343 := by exact prefixLift 2666343
  have htrace : WordTrace (prefixWord ++ tailWord_2666343) baseStart_2666343 baseEnd_2666343 := by
    simpa [prefixWord, tailWord_2666343, baseEnd_2666343] using wordTrace_append hprefix tailTrace_2666343
  have hstable : (prefixWord ++ tailWord_2666343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666343).length < 2 ^ (prefixWord ++ tailWord_2666343).sum := by decide
  have hdescent : baseEnd_2666343 < baseStart_2666343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666377 : List Nat := [1, 2, 1, 1, 5, 1, 5, 2, 4]
def baseStart_2666377 : Nat := 118140960795 + 2666377 * 2 ^ 59
def prefixEnd_2666377 : Nat := 4983230072969 + 3 ^ 40 * 2666377 * 2
def baseEnd_2666377 : Nat := 304251779354093226983347

theorem tailTrace_2666377 : CollatzResearch.WordTrace tailWord_2666377 prefixEnd_2666377 304251779354093226983347 := by
  unfold tailWord_2666377
  simp only [CollatzResearch.WordTrace]
  refine ⟨97250758661178984781981385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64833839107452656521320923 97250758661178984781981385)
  ·
    refine ⟨72938068995884238586486039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97250758661178984781981385 72938068995884238586486039)
    ·
      refine ⟨109407103493826357879729059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72938068995884238586486039 109407103493826357879729059)
      ·
        refine ⟨164110655240739536819593589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109407103493826357879729059 164110655240739536819593589)
        ·
          refine ⟨15385373928819331576836899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164110655240739536819593589 15385373928819331576836899)
          ·
            refine ⟨23078060893228997365255349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15385373928819331576836899 23078060893228997365255349)
            ·
              refine ⟨2163568208740218502992689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23078060893228997365255349 2163568208740218502992689)
              ·
                refine ⟨1622676156555163877244517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2163568208740218502992689 1622676156555163877244517)
                ·
                  refine ⟨304251779354093226983347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1622676156555163877244517 304251779354093226983347)
                  ·
                    rfl

theorem cell22_2666377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 4].length) (baseStart_2666377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666377 prefixEnd_2666377 := by exact prefixLift 2666377
  have htrace : WordTrace (prefixWord ++ tailWord_2666377) baseStart_2666377 baseEnd_2666377 := by
    simpa [prefixWord, tailWord_2666377, baseEnd_2666377] using wordTrace_append hprefix tailTrace_2666377
  have hstable : (prefixWord ++ tailWord_2666377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666377).length < 2 ^ (prefixWord ++ tailWord_2666377).sum := by decide
  have hdescent : baseEnd_2666377 < baseStart_2666377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666407 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2666407 : Nat := 118140960795 + 2666407 * 2 ^ 59
def prefixEnd_2666407 : Nat := 4983230072969 + 3 ^ 40 * 2666407 * 2
def baseEnd_2666407 : Nat := 912765607675369602699949

theorem tailTrace_2666407 : CollatzResearch.WordTrace tailWord_2666407 prefixEnd_2666407 912765607675369602699949 := by
  unfold tailWord_2666407
  simp only [CollatzResearch.WordTrace]
  refine ⟨97251852851070299905573475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64834568567380199937048983 97251852851070299905573475)
  ·
    refine ⟨145877779276605449858360213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97251852851070299905573475 145877779276605449858360213)
    ·
      refine ⟨6838020903590880462110635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 145877779276605449858360213 6838020903590880462110635)
      ·
        refine ⟨10257031355386320693165953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6838020903590880462110635 10257031355386320693165953)
        ·
          refine ⟨7692773516539740519874465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10257031355386320693165953 7692773516539740519874465)
          ·
            refine ⟨5769580137404805389905849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7692773516539740519874465 5769580137404805389905849)
            ·
              refine ⟨4327185103053604042429387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5769580137404805389905849 4327185103053604042429387)
              ·
                refine ⟨6490777654580406063644081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4327185103053604042429387 6490777654580406063644081)
                ·
                  refine ⟨4868083240935304547733061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6490777654580406063644081 4868083240935304547733061)
                  ·
                    refine ⟨912765607675369602699949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4868083240935304547733061 912765607675369602699949)
                    ·
                      rfl

theorem cell22_2666407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2666407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666407 prefixEnd_2666407 := by exact prefixLift 2666407
  have htrace : WordTrace (prefixWord ++ tailWord_2666407) baseStart_2666407 baseEnd_2666407 := by
    simpa [prefixWord, tailWord_2666407, baseEnd_2666407] using wordTrace_append hprefix tailTrace_2666407
  have hstable : (prefixWord ++ tailWord_2666407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666407).length < 2 ^ (prefixWord ++ tailWord_2666407).sum := by decide
  have hdescent : baseEnd_2666407 < baseStart_2666407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666418 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_2666418 : Nat := 118140960795 + 2666418 * 2 ^ 59
def prefixEnd_2666418 : Nat := 4983230072969 + 3 ^ 40 * 2666418 * 2
def baseEnd_2666418 : Nat := 912769373200169240674915

theorem tailTrace_2666418 : CollatzResearch.WordTrace tailWord_2666418 prefixEnd_2666418 912769373200169240674915 := by
  unfold tailWord_2666418
  simp only [CollatzResearch.WordTrace]
  refine ⟨24313063513507612196055977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64834836036020299189482605 24313063513507612196055977)
  ·
    refine ⟨18234797635130709147041983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24313063513507612196055977 18234797635130709147041983)
    ·
      refine ⟨27352196452696063720562975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18234797635130709147041983 27352196452696063720562975)
      ·
        refine ⟨41028294679044095580844463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27352196452696063720562975 41028294679044095580844463)
        ·
          refine ⟨61542442018566143371266695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41028294679044095580844463 61542442018566143371266695)
          ·
            refine ⟨92313663027849215056900043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61542442018566143371266695 92313663027849215056900043)
            ·
              refine ⟨138470494541773822585350065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92313663027849215056900043 138470494541773822585350065)
              ·
                refine ⟨103852870906330366939012549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138470494541773822585350065 103852870906330366939012549)
                ·
                  refine ⟨19472413294936943801064853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103852870906330366939012549 19472413294936943801064853)
                  ·
                    refine ⟨912769373200169240674915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19472413294936943801064853 912769373200169240674915)
                    ·
                      rfl

theorem cell22_2666418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_2666418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666418 prefixEnd_2666418 := by exact prefixLift 2666418
  have htrace : WordTrace (prefixWord ++ tailWord_2666418) baseStart_2666418 baseEnd_2666418 := by
    simpa [prefixWord, tailWord_2666418, baseEnd_2666418] using wordTrace_append hprefix tailTrace_2666418
  have hstable : (prefixWord ++ tailWord_2666418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666418).length < 2 ^ (prefixWord ++ tailWord_2666418).sum := by decide
  have hdescent : baseEnd_2666418 < baseStart_2666418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666428 : List Nat := [2, 2, 2, 5, 2, 1, 2, 2, 4]
def baseStart_2666428 : Nat := 118140960795 + 2666428 * 2 ^ 59
def prefixEnd_2666428 : Nat := 4983230072969 + 3 ^ 40 * 2666428 * 2
def baseEnd_2666428 : Nat := 304257598801510849308295

theorem tailTrace_2666428 : CollatzResearch.WordTrace tailWord_2666428 prefixEnd_2666428 304257598801510849308295 := by
  unfold tailWord_2666428
  simp only [CollatzResearch.WordTrace]
  refine ⟨48626309391997110246043969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64835079189329480328058625 48626309391997110246043969)
  ·
    refine ⟨36469732043997832684532977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48626309391997110246043969 36469732043997832684532977)
    ·
      refine ⟨27352299032998374513399733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36469732043997832684532977 27352299032998374513399733)
      ·
        refine ⟨2564278034343597610631225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27352299032998374513399733 2564278034343597610631225)
        ·
          refine ⟨1923208525757698207973419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2564278034343597610631225 1923208525757698207973419)
          ·
            refine ⟨2884812788636547311960129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923208525757698207973419 2884812788636547311960129)
            ·
              refine ⟨2163609591477410483970097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2884812788636547311960129 2163609591477410483970097)
              ·
                refine ⟨1622707193608057862977573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2163609591477410483970097 1622707193608057862977573)
                ·
                  refine ⟨304257598801510849308295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1622707193608057862977573 304257598801510849308295)
                  ·
                    rfl

theorem cell22_2666428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_2666428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666428 prefixEnd_2666428 := by exact prefixLift 2666428
  have htrace : WordTrace (prefixWord ++ tailWord_2666428) baseStart_2666428 baseEnd_2666428 := by
    simpa [prefixWord, tailWord_2666428, baseEnd_2666428] using wordTrace_append hprefix tailTrace_2666428
  have hstable : (prefixWord ++ tailWord_2666428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666428).length < 2 ^ (prefixWord ++ tailWord_2666428).sum := by decide
  have hdescent : baseEnd_2666428 < baseStart_2666428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666448 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 1, 7]
def baseStart_2666448 : Nat := 118140960795 + 2666448 * 2 ^ 59
def prefixEnd_2666448 : Nat := 4983230072969 + 3 ^ 40 * 2666448 * 2
def baseEnd_2666448 : Nat := 912779642813259162424823

theorem tailTrace_2666448 : CollatzResearch.WordTrace tailWord_2666448 prefixEnd_2666448 912779642813259162424823 := by
  unfold tailWord_2666448
  simp only [CollatzResearch.WordTrace]
  refine ⟨48626674121960881953907999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64835565495947842605210665 48626674121960881953907999)
  ·
    refine ⟨72940011182941322930861999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48626674121960881953907999 72940011182941322930861999)
    ·
      refine ⟨109410016774411984396292999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72940011182941322930861999 109410016774411984396292999)
      ·
        refine ⟨164115025161617976594439499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109410016774411984396292999 164115025161617976594439499)
        ·
          refine ⟨246172537742426964891659249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164115025161617976594439499 246172537742426964891659249)
          ·
            refine ⟨184629403306820223668744437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246172537742426964891659249 184629403306820223668744437)
            ·
              refine ⟨17309006560014395968944791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184629403306820223668744437 17309006560014395968944791)
              ·
                refine ⟨25963509840021593953417187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17309006560014395968944791 25963509840021593953417187)
                ·
                  refine ⟨38945264760032390930125781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25963509840021593953417187 38945264760032390930125781)
                  ·
                    refine ⟨912779642813259162424823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38945264760032390930125781 912779642813259162424823)
                    ·
                      rfl

theorem cell22_2666448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_2666448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666448 prefixEnd_2666448 := by exact prefixLift 2666448
  have htrace : WordTrace (prefixWord ++ tailWord_2666448) baseStart_2666448 baseEnd_2666448 := by
    simpa [prefixWord, tailWord_2666448, baseEnd_2666448] using wordTrace_append hprefix tailTrace_2666448
  have hstable : (prefixWord ++ tailWord_2666448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666448).length < 2 ^ (prefixWord ++ tailWord_2666448).sum := by decide
  have hdescent : baseEnd_2666448 < baseStart_2666448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666471 : List Nat := [1, 1, 5, 2, 3, 1, 2, 3, 1, 3]
def baseStart_2666471 : Nat := 118140960795 + 2666471 * 2 ^ 59
def prefixEnd_2666471 : Nat := 4983230072969 + 3 ^ 40 * 2666471 * 2
def baseEnd_2666471 : Nat := 912787516183294769099753

theorem tailTrace_2666471 : CollatzResearch.WordTrace tailWord_2666471 prefixEnd_2666471 912787516183294769099753 := by
  unfold tailWord_2666471
  simp only [CollatzResearch.WordTrace]
  refine ⟨97254187122838438835903267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64836124748558959223935511 97254187122838438835903267)
  ·
    refine ⟨145881280684257658253854901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97254187122838438835903267 145881280684257658253854901)
    ·
      refine ⟨13676370064149155461298897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145881280684257658253854901 13676370064149155461298897)
      ·
        refine ⟨10257277548111866595974173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13676370064149155461298897 10257277548111866595974173)
        ·
          refine ⟨3846479080541949973490315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10257277548111866595974173 3846479080541949973490315)
          ·
            refine ⟨5769718620812924960235473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3846479080541949973490315 5769718620812924960235473)
            ·
              refine ⟨4327288965609693720176605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5769718620812924960235473 4327288965609693720176605)
              ·
                refine ⟨1622733362103635145066227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4327288965609693720176605 1622733362103635145066227)
                ·
                  refine ⟨2434100043155452717599341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622733362103635145066227 2434100043155452717599341)
                  ·
                    refine ⟨912787516183294769099753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2434100043155452717599341 912787516183294769099753)
                    ·
                      rfl

theorem cell22_2666471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_2666471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666471 prefixEnd_2666471 := by exact prefixLift 2666471
  have htrace : WordTrace (prefixWord ++ tailWord_2666471) baseStart_2666471 baseEnd_2666471 := by
    simpa [prefixWord, tailWord_2666471, baseEnd_2666471] using wordTrace_append hprefix tailTrace_2666471
  have hstable : (prefixWord ++ tailWord_2666471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666471).length < 2 ^ (prefixWord ++ tailWord_2666471).sum := by decide
  have hdescent : baseEnd_2666471 < baseStart_2666471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666542 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2666542 : Nat := 118140960795 + 2666542 * 2 ^ 59
def prefixEnd_2666542 : Nat := 4983230072969 + 3 ^ 40 * 2666542 * 2
def baseEnd_2666542 : Nat := 912811820934274250574535

theorem tailTrace_2666542 : CollatzResearch.WordTrace tailWord_2666542 prefixEnd_2666542 912811820934274250574535 := by
  unfold tailWord_2666542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12157097088197652245217235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64837851137054145307825253 12157097088197652245217235)
  ·
    refine ⟨18235645632296478367825853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12157097088197652245217235 18235645632296478367825853)
    ·
      refine ⟨6838367112111179387934695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18235645632296478367825853 6838367112111179387934695)
      ·
        refine ⟨10257550668166769081902043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6838367112111179387934695 10257550668166769081902043)
        ·
          refine ⟨15386326002250153622853065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10257550668166769081902043 15386326002250153622853065)
          ·
            refine ⟨11539744501687615217139799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15386326002250153622853065 11539744501687615217139799)
            ·
              refine ⟨17309616752531422825709699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11539744501687615217139799 17309616752531422825709699)
              ·
                refine ⟨25964425128797134238564549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17309616752531422825709699 25964425128797134238564549)
                ·
                  refine ⟨4868329711649462669730853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25964425128797134238564549 4868329711649462669730853)
                  ·
                    refine ⟨912811820934274250574535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4868329711649462669730853 912811820934274250574535)
                    ·
                      rfl

theorem cell22_2666542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2666542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666542 prefixEnd_2666542 := by exact prefixLift 2666542
  have htrace : WordTrace (prefixWord ++ tailWord_2666542) baseStart_2666542 baseEnd_2666542 := by
    simpa [prefixWord, tailWord_2666542, baseEnd_2666542] using wordTrace_append hprefix tailTrace_2666542
  have hstable : (prefixWord ++ tailWord_2666542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666542).length < 2 ^ (prefixWord ++ tailWord_2666542).sum := by decide
  have hdescent : baseEnd_2666542 < baseStart_2666542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666561 : List Nat := [1, 2, 5, 1, 2, 1, 4, 1, 2, 3]
def baseStart_2666561 : Nat := 118140960795 + 2666561 * 2 ^ 59
def prefixEnd_2666561 : Nat := 4983230072969 + 3 ^ 40 * 2666561 * 2
def baseEnd_2666561 : Nat := 912818325022564534349477

theorem tailTrace_2666561 : CollatzResearch.WordTrace tailWord_2666561 prefixEnd_2666561 912818325022564534349477 := by
  unfold tailWord_2666561
  simp only [CollatzResearch.WordTrace]
  refine ⟨97257469692512384206679537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64838313128341589471119691 97257469692512384206679537)
  ·
    refine ⟨72943102269384288155009653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97257469692512384206679537 72943102269384288155009653)
    ·
      refine ⟨6838415837754777014532155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72943102269384288155009653 6838415837754777014532155)
      ·
        refine ⟨10257623756632165521798233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6838415837754777014532155 10257623756632165521798233)
        ·
          refine ⟨7693217817474124141348675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10257623756632165521798233 7693217817474124141348675)
          ·
            refine ⟨11539826726211186212023013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7693217817474124141348675 11539826726211186212023013)
            ·
              refine ⟨2163717511164597414754315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11539826726211186212023013 2163717511164597414754315)
              ·
                refine ⟨3245576266746896122131473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2163717511164597414754315 3245576266746896122131473)
                ·
                  refine ⟨2434182200060172091598605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3245576266746896122131473 2434182200060172091598605)
                  ·
                    refine ⟨912818325022564534349477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2434182200060172091598605 912818325022564534349477)
                    ·
                      rfl

theorem cell22_2666561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_2666561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666561 prefixEnd_2666561 := by exact prefixLift 2666561
  have htrace : WordTrace (prefixWord ++ tailWord_2666561) baseStart_2666561 baseEnd_2666561 := by
    simpa [prefixWord, tailWord_2666561, baseEnd_2666561] using wordTrace_append hprefix tailTrace_2666561
  have hstable : (prefixWord ++ tailWord_2666561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666561).length < 2 ^ (prefixWord ++ tailWord_2666561).sum := by decide
  have hdescent : baseEnd_2666561 < baseStart_2666561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666572 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 3, 3]
def baseStart_2666572 : Nat := 118140960795 + 2666572 * 2 ^ 59
def prefixEnd_2666572 : Nat := 4983230072969 + 3 ^ 40 * 2666572 * 2
def baseEnd_2666572 : Nat := 912822090547364172324443

theorem tailTrace_2666572 : CollatzResearch.WordTrace tailWord_2666572 prefixEnd_2666572 912822090547364172324443 := by
  unfold tailWord_2666572
  simp only [CollatzResearch.WordTrace]
  refine ⟨48628935447736266542664985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64838580596981688723553313 48628935447736266542664985)
  ·
    refine ⟨36471701585802199906998739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48628935447736266542664985 36471701585802199906998739)
    ·
      refine ⟨54707552378703299860498109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36471701585802199906998739 54707552378703299860498109)
      ·
        refine ⟨20515332142013737447686791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54707552378703299860498109 20515332142013737447686791)
        ·
          refine ⟨30772998213020606171530187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20515332142013737447686791 30772998213020606171530187)
          ·
            refine ⟨46159497319530909257295281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30772998213020606171530187 46159497319530909257295281)
            ·
              refine ⟨34619622989648181942971461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46159497319530909257295281 34619622989648181942971461)
              ·
                refine ⟨6491179310559034114307149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34619622989648181942971461 6491179310559034114307149)
                ·
                  refine ⟨2434192241459637792865181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6491179310559034114307149 2434192241459637792865181)
                  ·
                    refine ⟨912822090547364172324443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2434192241459637792865181 912822090547364172324443)
                    ·
                      rfl

theorem cell22_2666572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_2666572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666572 prefixEnd_2666572 := by exact prefixLift 2666572
  have htrace : WordTrace (prefixWord ++ tailWord_2666572) baseStart_2666572 baseEnd_2666572 := by
    simpa [prefixWord, tailWord_2666572, baseEnd_2666572] using wordTrace_append hprefix tailTrace_2666572
  have hstable : (prefixWord ++ tailWord_2666572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666572).length < 2 ^ (prefixWord ++ tailWord_2666572).sum := by decide
  have hdescent : baseEnd_2666572 < baseStart_2666572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666606 : List Nat := [4, 1, 2, 2, 1, 1, 3, 4, 1, 3]
def baseStart_2666606 : Nat := 118140960795 + 2666606 * 2 ^ 59
def prefixEnd_2666606 : Nat := 4983230072969 + 3 ^ 40 * 2666606 * 2
def baseEnd_2666606 : Nat := 912833729442199416974339

theorem tailTrace_2666606 : CollatzResearch.WordTrace tailWord_2666606 prefixEnd_2666606 912833729442199416974339 := by
  unfold tailWord_2666606
  simp only [CollatzResearch.WordTrace]
  refine ⟨12157388872168669611508459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64839407318232904594711781 12157388872168669611508459)
  ·
    refine ⟨18236083308253004417262689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12157388872168669611508459 18236083308253004417262689)
    ·
      refine ⟨13677062481189753312947017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18236083308253004417262689 13677062481189753312947017)
      ·
        refine ⟨10257796860892314984710263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13677062481189753312947017 10257796860892314984710263)
        ·
          refine ⟨15386695291338472477065395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10257796860892314984710263 15386695291338472477065395)
          ·
            refine ⟨23080042937007708715598093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15386695291338472477065395 23080042937007708715598093)
            ·
              refine ⟨8655016101377890768349285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23080042937007708715598093 8655016101377890768349285)
              ·
                refine ⟨1622815519008354519065491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8655016101377890768349285 1622815519008354519065491)
                ·
                  refine ⟨2434223278512531778598237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622815519008354519065491 2434223278512531778598237)
                  ·
                    refine ⟨912833729442199416974339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2434223278512531778598237 912833729442199416974339)
                    ·
                      rfl

theorem cell22_2666606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_2666606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666606 prefixEnd_2666606 := by exact prefixLift 2666606
  have htrace : WordTrace (prefixWord ++ tailWord_2666606) baseStart_2666606 baseEnd_2666606 := by
    simpa [prefixWord, tailWord_2666606, baseEnd_2666606] using wordTrace_append hprefix tailTrace_2666606
  have hstable : (prefixWord ++ tailWord_2666606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666606).length < 2 ^ (prefixWord ++ tailWord_2666606).sum := by decide
  have hdescent : baseEnd_2666606 < baseStart_2666606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666617 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 2, 5]
def baseStart_2666617 : Nat := 118140960795 + 2666617 * 2 ^ 59
def prefixEnd_2666617 : Nat := 4983230072969 + 3 ^ 40 * 2666617 * 2
def baseEnd_2666617 : Nat := 912837494966999054949305

theorem tailTrace_2666617 : CollatzResearch.WordTrace tailWord_2666617 prefixEnd_2666617 912837494966999054949305 := by
  unfold tailWord_2666617
  simp only [CollatzResearch.WordTrace]
  refine ⟨97259512180309505770718105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64839674786873003847145403 97259512180309505770718105)
  ·
    refine ⟨72944634135232129328038579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97259512180309505770718105 72944634135232129328038579)
    ·
      refine ⟨109416951202848193992057869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72944634135232129328038579 109416951202848193992057869)
      ·
        refine ⟨41031356701068072747021701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109416951202848193992057869 41031356701068072747021701)
        ·
          refine ⟨7693379381450263640066569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41031356701068072747021701 7693379381450263640066569)
          ·
            refine ⟨5770034536087697730049927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7693379381450263640066569 5770034536087697730049927)
            ·
              refine ⟨8655051804131546595074891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5770034536087697730049927 8655051804131546595074891)
              ·
                refine ⟨12982577706197319892612337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8655051804131546595074891 12982577706197319892612337)
                ·
                  refine ⟨9736933279647989919459253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12982577706197319892612337 9736933279647989919459253)
                  ·
                    refine ⟨912837494966999054949305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9736933279647989919459253 912837494966999054949305)
                    ·
                      rfl

theorem cell22_2666617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_2666617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2666617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2666617 prefixEnd_2666617 := by exact prefixLift 2666617
  have htrace : WordTrace (prefixWord ++ tailWord_2666617) baseStart_2666617 baseEnd_2666617 := by
    simpa [prefixWord, tailWord_2666617, baseEnd_2666617] using wordTrace_append hprefix tailTrace_2666617
  have hstable : (prefixWord ++ tailWord_2666617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666617).length < 2 ^ (prefixWord ++ tailWord_2666617).sum := by decide
  have hdescent : baseEnd_2666617 < baseStart_2666617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
