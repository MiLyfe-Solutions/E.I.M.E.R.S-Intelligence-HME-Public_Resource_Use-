import V185TrunkScan23Chunk0763

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4518239 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 3]
def baseStart_4518239 : Nat := 118140960795 + 4518239 * 2 ^ 59
def prefixEnd_4518239 : Nat := 4983230072969 + 3 ^ 40 * 4518239 * 2
def baseEnd_4518239 : Nat := 2320028318889853102833503

theorem tailTrace_4518239 : CollatzResearch.WordTrace tailWord_4518239 prefixEnd_4518239 2320028318889853102833503 := by
  unfold tailWord_4518239
  simp only [CollatzResearch.WordTrace]
  refine ⟨164793714678199231631813771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109862476452132821087875847 164793714678199231631813771)
  ·
    refine ⟨247190572017298847447720657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164793714678199231631813771 247190572017298847447720657)
    ·
      refine ⟨185392929012974135585790493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247190572017298847447720657 185392929012974135585790493)
      ·
        refine ⟨69522348379865300844671435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185392929012974135585790493 69522348379865300844671435)
        ·
          refine ⟨104283522569797951267007153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69522348379865300844671435 104283522569797951267007153)
          ·
            refine ⟨78212641927348463450255365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104283522569797951267007153 78212641927348463450255365)
            ·
              refine ⟨14664870361377836896922881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78212641927348463450255365 14664870361377836896922881)
              ·
                refine ⟨10998652771033377672692161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14664870361377836896922881 10998652771033377672692161)
                ·
                  refine ⟨8248989578275033254519121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10998652771033377672692161 8248989578275033254519121)
                  ·
                    refine ⟨6186742183706274940889341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8248989578275033254519121 6186742183706274940889341)
                    ·
                      refine ⟨2320028318889853102833503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6186742183706274940889341 2320028318889853102833503)
                      ·
                        rfl

theorem cell23_4518239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_4518239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518239 prefixEnd_4518239 := by exact prefixLift 4518239
  have htrace : WordTrace (prefixWord ++ tailWord_4518239) baseStart_4518239 baseEnd_4518239 := by
    simpa [prefixWord, tailWord_4518239, baseEnd_4518239] using wordTrace_append hprefix tailTrace_4518239
  have hstable : (prefixWord ++ tailWord_4518239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518239).length < 2 ^ (prefixWord ++ tailWord_4518239).sum := by decide
  have hdescent : baseEnd_4518239 < baseStart_4518239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518273 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_4518273 : Nat := 118140960795 + 4518273 * 2 ^ 59
def prefixEnd_4518273 : Nat := 4983230072969 + 3 ^ 40 * 4518273 * 2
def baseEnd_4518273 : Nat := 2320045777232105969808347

theorem tailTrace_4518273 : CollatzResearch.WordTrace tailWord_4518273 prefixEnd_4518273 2320045777232105969808347 := by
  unfold tailWord_4518273
  simp only [CollatzResearch.WordTrace]
  refine ⟨164794954760076055438551473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109863303173384036959034315 164794954760076055438551473)
  ·
    refine ⟨123596216070057041578913605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164794954760076055438551473 123596216070057041578913605)
    ·
      refine ⟨23174290513135695296046301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123596216070057041578913605 23174290513135695296046301)
      ·
        refine ⟨8690358942425885736017363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23174290513135695296046301 8690358942425885736017363)
        ·
          refine ⟨13035538413638828604026045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8690358942425885736017363 13035538413638828604026045)
          ·
            refine ⟨4888326905114560726509767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13035538413638828604026045 4888326905114560726509767)
            ·
              refine ⟨7332490357671841089764651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4888326905114560726509767 7332490357671841089764651)
              ·
                refine ⟨10998735536507761634646977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7332490357671841089764651 10998735536507761634646977)
                ·
                  refine ⟨8249051652380821225985233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10998735536507761634646977 8249051652380821225985233)
                  ·
                    refine ⟨6186788739285615919488925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8249051652380821225985233 6186788739285615919488925)
                    ·
                      refine ⟨2320045777232105969808347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6186788739285615919488925 2320045777232105969808347)
                      ·
                        rfl

theorem cell23_4518273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_4518273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518273 prefixEnd_4518273 := by exact prefixLift 4518273
  have htrace : WordTrace (prefixWord ++ tailWord_4518273) baseStart_4518273 baseEnd_4518273 := by
    simpa [prefixWord, tailWord_4518273, baseEnd_4518273] using wordTrace_append hprefix tailTrace_4518273
  have hstable : (prefixWord ++ tailWord_4518273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518273).length < 2 ^ (prefixWord ++ tailWord_4518273).sum := by decide
  have hdescent : baseEnd_4518273 < baseStart_4518273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518303 : List Nat := [1, 1, 2, 5, 1, 1, 1, 6, 1, 1, 3]
def baseStart_4518303 : Nat := 118140960795 + 4518303 * 2 ^ 59
def prefixEnd_4518303 : Nat := 4983230072969 + 3 ^ 40 * 4518303 * 2
def baseEnd_4518303 : Nat := 2320061181651740852433209

theorem tailTrace_4518303 : CollatzResearch.WordTrace tailWord_4518303 prefixEnd_4518303 2320061181651740852433209 := by
  unfold tailWord_4518303
  simp only [CollatzResearch.WordTrace]
  refine ⟨164796048949967370562143563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109864032633311580374762375 164796048949967370562143563)
  ·
    refine ⟨247194073424951055843215345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164796048949967370562143563 247194073424951055843215345)
    ·
      refine ⟨185395555068713291882411509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247194073424951055843215345 185395555068713291882411509)
      ·
        refine ⟨17380833287691871113976079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 185395555068713291882411509 17380833287691871113976079)
        ·
          refine ⟨26071249931537806670964119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17380833287691871113976079 26071249931537806670964119)
          ·
            refine ⟨39106874897306710006446179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26071249931537806670964119 39106874897306710006446179)
            ·
              refine ⟨58660312345960065009669269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39106874897306710006446179 58660312345960065009669269)
              ·
                refine ⟨2749702141216878047328247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58660312345960065009669269 2749702141216878047328247)
                ·
                  refine ⟨4124553211825317070992371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2749702141216878047328247 4124553211825317070992371)
                  ·
                    refine ⟨6186829817737975606488557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4124553211825317070992371 6186829817737975606488557)
                    ·
                      refine ⟨2320061181651740852433209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6186829817737975606488557 2320061181651740852433209)
                      ·
                        rfl

theorem cell23_4518303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_4518303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518303 prefixEnd_4518303 := by exact prefixLift 4518303
  have htrace : WordTrace (prefixWord ++ tailWord_4518303) baseStart_4518303 baseEnd_4518303 := by
    simpa [prefixWord, tailWord_4518303, baseEnd_4518303] using wordTrace_append hprefix tailTrace_4518303
  have hstable : (prefixWord ++ tailWord_4518303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518303).length < 2 ^ (prefixWord ++ tailWord_4518303).sum := by decide
  have hdescent : baseEnd_4518303 < baseStart_4518303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518346 : List Nat := [3, 1, 2, 1, 2, 2, 1, 5, 1, 2, 3]
def baseStart_4518346 : Nat := 118140960795 + 4518346 * 2 ^ 59
def prefixEnd_4518346 : Nat := 4983230072969 + 3 ^ 40 * 4518346 * 2
def baseEnd_4518346 : Nat := 2320083261319884184195511

theorem tailTrace_4518346 : CollatzResearch.WordTrace tailWord_4518346 prefixEnd_4518346 2320083261319884184195511 := by
  unfold tailWord_4518346
  simp only [CollatzResearch.WordTrace]
  refine ⟨41199404322202897226489723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109865078192541059270639261 41199404322202897226489723)
  ·
    refine ⟨61799106483304345839734585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41199404322202897226489723 61799106483304345839734585)
    ·
      refine ⟨46349329862478259379800939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61799106483304345839734585 46349329862478259379800939)
      ·
        refine ⟨69523994793717389069701409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46349329862478259379800939 69523994793717389069701409)
        ·
          refine ⟨52142996095288041802276057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69523994793717389069701409 52142996095288041802276057)
          ·
            refine ⟨39107247071466031351707043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52142996095288041802276057 39107247071466031351707043)
            ·
              refine ⟨58660870607199047027560565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39107247071466031351707043 58660870607199047027560565)
              ·
                refine ⟨5499456619424910658833803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58660870607199047027560565 5499456619424910658833803)
                ·
                  refine ⟨8249184929137365988250705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5499456619424910658833803 8249184929137365988250705)
                  ·
                    refine ⟨6186888696853024491188029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8249184929137365988250705 6186888696853024491188029)
                    ·
                      refine ⟨2320083261319884184195511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6186888696853024491188029 2320083261319884184195511)
                      ·
                        rfl

theorem cell23_4518346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_4518346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518346 prefixEnd_4518346 := by exact prefixLift 4518346
  have htrace : WordTrace (prefixWord ++ tailWord_4518346) baseStart_4518346 baseEnd_4518346 := by
    simpa [prefixWord, tailWord_4518346, baseEnd_4518346] using wordTrace_append hprefix tailTrace_4518346
  have hstable : (prefixWord ++ tailWord_4518346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518346).length < 2 ^ (prefixWord ++ tailWord_4518346).sum := by decide
  have hdescent : baseEnd_4518346 < baseStart_4518346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518352 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 6]
def baseStart_4518352 : Nat := 118140960795 + 4518352 * 2 ^ 59
def prefixEnd_4518352 : Nat := 4983230072969 + 3 ^ 40 * 4518352 * 2
def baseEnd_4518352 : Nat := 2320086342203811160720483

theorem tailTrace_4518352 : CollatzResearch.WordTrace tailWord_4518352 prefixEnd_4518352 2320086342203811160720483 := by
  unfold tailWord_4518352
  simp only [CollatzResearch.WordTrace]
  refine ⟨82398918063394925965338655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109865224084526567953784873 82398918063394925965338655)
  ·
    refine ⟨123598377095092388948007983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82398918063394925965338655 123598377095092388948007983)
    ·
      refine ⟨185397565642638583422011975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123598377095092388948007983 185397565642638583422011975)
      ·
        refine ⟨278096348463957875133017963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185397565642638583422011975 278096348463957875133017963)
        ·
          refine ⟨417144522695936812699526945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278096348463957875133017963 417144522695936812699526945)
          ·
            refine ⟨312858392021952609524645209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417144522695936812699526945 312858392021952609524645209)
            ·
              refine ⟨234643794016464457143483907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312858392021952609524645209 234643794016464457143483907)
              ·
                refine ⟨351965691024696685715225861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234643794016464457143483907 351965691024696685715225861)
                ·
                  refine ⟨65993567067130628571604849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 351965691024696685715225861 65993567067130628571604849)
                  ·
                    refine ⟨49495175300347971428703637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65993567067130628571604849 49495175300347971428703637)
                    ·
                      refine ⟨2320086342203811160720483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49495175300347971428703637 2320086342203811160720483)
                      ·
                        rfl

theorem cell23_4518352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_4518352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518352 prefixEnd_4518352 := by exact prefixLift 4518352
  have htrace : WordTrace (prefixWord ++ tailWord_4518352) baseStart_4518352 baseEnd_4518352 := by
    simpa [prefixWord, tailWord_4518352, baseEnd_4518352] using wordTrace_append hprefix tailTrace_4518352
  have hstable : (prefixWord ++ tailWord_4518352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518352).length < 2 ^ (prefixWord ++ tailWord_4518352).sum := by decide
  have hdescent : baseEnd_4518352 < baseStart_4518352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518354 : List Nat := [3, 2, 2, 4, 1, 1, 3, 2, 1, 1, 3]
def baseStart_4518354 : Nat := 118140960795 + 4518354 * 2 ^ 59
def prefixEnd_4518354 : Nat := 4983230072969 + 3 ^ 40 * 4518354 * 2
def baseEnd_4518354 : Nat := 2320087369165120152895475

theorem tailTrace_4518354 : CollatzResearch.WordTrace tailWord_4518354 prefixEnd_4518354 2320087369165120152895475 := by
  unfold tailWord_4518354
  simp only [CollatzResearch.WordTrace]
  refine ⟨41199477268195651568062529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109865272715188404181500077 41199477268195651568062529)
  ·
    refine ⟨30899607951146738676046897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41199477268195651568062529 30899607951146738676046897)
    ·
      refine ⟨23174705963360054007035173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30899607951146738676046897 23174705963360054007035173)
      ·
        refine ⟨4345257368130010126319095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23174705963360054007035173 4345257368130010126319095)
        ·
          refine ⟨6517886052195015189478643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4345257368130010126319095 6517886052195015189478643)
          ·
            refine ⟨9776829078292522784217965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6517886052195015189478643 9776829078292522784217965)
            ·
              refine ⟨3666310904359696044081737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9776829078292522784217965 3666310904359696044081737)
              ·
                refine ⟨2749733178269772033061303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3666310904359696044081737 2749733178269772033061303)
                ·
                  refine ⟨4124599767404658049591955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2749733178269772033061303 4124599767404658049591955)
                  ·
                    refine ⟨6186899651106987074387933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4124599767404658049591955 6186899651106987074387933)
                    ·
                      refine ⟨2320087369165120152895475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6186899651106987074387933 2320087369165120152895475)
                      ·
                        rfl

theorem cell23_4518354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_4518354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518354 prefixEnd_4518354 := by exact prefixLift 4518354
  have htrace : WordTrace (prefixWord ++ tailWord_4518354) baseStart_4518354 baseEnd_4518354 := by
    simpa [prefixWord, tailWord_4518354, baseEnd_4518354] using wordTrace_append hprefix tailTrace_4518354
  have hstable : (prefixWord ++ tailWord_4518354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518354).length < 2 ^ (prefixWord ++ tailWord_4518354).sum := by decide
  have hdescent : baseEnd_4518354 < baseStart_4518354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518413 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_4518413 : Nat := 118140960795 + 4518413 * 2 ^ 59
def prefixEnd_4518413 : Nat := 4983230072969 + 3 ^ 40 * 4518413 * 2
def baseEnd_4518413 : Nat := 773372554841245140685901

theorem tailTrace_4518413 : CollatzResearch.WordTrace tailWord_4518413 prefixEnd_4518413 773372554841245140685901 := by
  unfold tailWord_4518413
  simp only [CollatzResearch.WordTrace]
  refine ⟨164800060979568859348647893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109866707319712572899098595 164800060979568859348647893)
  ·
    refine ⟨3862501429208645140983935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 164800060979568859348647893 3862501429208645140983935)
    ·
      refine ⟨5793752143812967711475903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3862501429208645140983935 5793752143812967711475903)
      ·
        refine ⟨8690628215719451567213855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5793752143812967711475903 8690628215719451567213855)
        ·
          refine ⟨13035942323579177350820783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8690628215719451567213855 13035942323579177350820783)
          ·
            refine ⟨19553913485368766026231175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13035942323579177350820783 19553913485368766026231175)
            ·
              refine ⟨29330870228053149039346763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19553913485368766026231175 29330870228053149039346763)
              ·
                refine ⟨43996305342079723559020145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29330870228053149039346763 43996305342079723559020145)
                ·
                  refine ⟨32997229006559792669265109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43996305342079723559020145 32997229006559792669265109)
                  ·
                    refine ⟨773372554841245140685901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32997229006559792669265109 773372554841245140685901)
                    ·
                      rfl

theorem cell23_4518413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_4518413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518413 prefixEnd_4518413 := by exact prefixLift 4518413
  have htrace : WordTrace (prefixWord ++ tailWord_4518413) baseStart_4518413 baseEnd_4518413 := by
    simpa [prefixWord, tailWord_4518413, baseEnd_4518413] using wordTrace_append hprefix tailTrace_4518413
  have hstable : (prefixWord ++ tailWord_4518413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518413).length < 2 ^ (prefixWord ++ tailWord_4518413).sum := by decide
  have hdescent : baseEnd_4518413 < baseStart_4518413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518419 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 3]
def baseStart_4518419 : Nat := 118140960795 + 4518419 * 2 ^ 59
def prefixEnd_4518419 : Nat := 4983230072969 + 3 ^ 40 * 4518419 * 2
def baseEnd_4518419 : Nat := 2320120745407662398582675

theorem tailTrace_4518419 : CollatzResearch.WordTrace tailWord_4518419 prefixEnd_4518419 2320120745407662398582675 := by
  unfold tailWord_4518419
  simp only [CollatzResearch.WordTrace]
  refine ⟨164800279817547122373366311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109866853211698081582244207 164800279817547122373366311)
  ·
    refine ⟨247200419726320683560049467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164800279817547122373366311 247200419726320683560049467)
    ·
      refine ⟨370800629589481025340074201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247200419726320683560049467 370800629589481025340074201)
      ·
        refine ⟨278100472192110769005055651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370800629589481025340074201 278100472192110769005055651)
        ·
          refine ⟨417150708288166153507583477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278100472192110769005055651 417150708288166153507583477)
          ·
            refine ⟨39107878902015576891335951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 417150708288166153507583477 39107878902015576891335951)
            ·
              refine ⟨58661818353023365337003927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39107878902015576891335951 58661818353023365337003927)
              ·
                refine ⟨87992727529535048005505891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58661818353023365337003927 87992727529535048005505891)
                ·
                  refine ⟨131989091294302572008258837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87992727529535048005505891 131989091294302572008258837)
                  ·
                    refine ⟨6186988654420433062887133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 131989091294302572008258837 6186988654420433062887133)
                    ·
                      refine ⟨2320120745407662398582675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6186988654420433062887133 2320120745407662398582675)
                      ·
                        rfl

theorem cell23_4518419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 3].length) (baseStart_4518419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518419 prefixEnd_4518419 := by exact prefixLift 4518419
  have htrace : WordTrace (prefixWord ++ tailWord_4518419) baseStart_4518419 baseEnd_4518419 := by
    simpa [prefixWord, tailWord_4518419, baseEnd_4518419] using wordTrace_append hprefix tailTrace_4518419
  have hstable : (prefixWord ++ tailWord_4518419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518419).length < 2 ^ (prefixWord ++ tailWord_4518419).sum := by decide
  have hdescent : baseEnd_4518419 < baseStart_4518419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518420 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_4518420 : Nat := 118140960795 + 4518420 * 2 ^ 59
def prefixEnd_4518420 : Nat := 4983230072969 + 3 ^ 40 * 4518420 * 2
def baseEnd_4518420 : Nat := 2320121258888316894670171

theorem tailTrace_4518420 : CollatzResearch.WordTrace tailWord_4518420 prefixEnd_4518420 2320121258888316894670171 := by
  unfold tailWord_4518420
  simp only [CollatzResearch.WordTrace]
  refine ⟨82400158145271749772076357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109866877527028999696101809 82400158145271749772076357)
  ·
    refine ⟨15450029652238453082264317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82400158145271749772076357 15450029652238453082264317)
    ·
      refine ⟨5793761119589419905849119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15450029652238453082264317 5793761119589419905849119)
      ·
        refine ⟨8690641679384129858773679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5793761119589419905849119 8690641679384129858773679)
        ·
          refine ⟨13035962519076194788160519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8690641679384129858773679 13035962519076194788160519)
          ·
            refine ⟨19553943778614292182240779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13035962519076194788160519 19553943778614292182240779)
            ·
              refine ⟨29330915667921438273361169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19553943778614292182240779 29330915667921438273361169)
              ·
                refine ⟨21998186750941078705020877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29330915667921438273361169 21998186750941078705020877)
                ·
                  refine ⟨8249320031602904514382829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21998186750941078705020877 8249320031602904514382829)
                  ·
                    refine ⟨3093495011851089192893561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8249320031602904514382829 3093495011851089192893561)
                    ·
                      refine ⟨2320121258888316894670171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093495011851089192893561 2320121258888316894670171)
                      ·
                        rfl

theorem cell23_4518420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_4518420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518420 prefixEnd_4518420 := by exact prefixLift 4518420
  have htrace : WordTrace (prefixWord ++ tailWord_4518420) baseStart_4518420 baseEnd_4518420 := by
    simpa [prefixWord, tailWord_4518420, baseEnd_4518420] using wordTrace_append hprefix tailTrace_4518420
  have hstable : (prefixWord ++ tailWord_4518420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518420).length < 2 ^ (prefixWord ++ tailWord_4518420).sum := by decide
  have hdescent : baseEnd_4518420 < baseStart_4518420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518433 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 1, 4, 2]
def baseStart_4518433 : Nat := 118140960795 + 4518433 * 2 ^ 59
def prefixEnd_4518433 : Nat := 4983230072969 + 3 ^ 40 * 4518433 * 2
def baseEnd_4518433 : Nat := 2320127934136825343807611

theorem tailTrace_4518433 : CollatzResearch.WordTrace tailWord_4518433 prefixEnd_4518433 2320127934136825343807611 := by
  unfold tailWord_4518433
  simp only [CollatzResearch.WordTrace]
  refine ⟨164800790439496402764375953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109867193626330935176250635 164800790439496402764375953)
  ·
    refine ⟨123600592829622302073281965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164800790439496402764375953 123600592829622302073281965)
    ·
      refine ⟨46350222311108363277480737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123600592829622302073281965 46350222311108363277480737)
      ·
        refine ⟨34762666733331272458110553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46350222311108363277480737 34762666733331272458110553)
        ·
          refine ⟨26072000049998454343582915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34762666733331272458110553 26072000049998454343582915)
          ·
            refine ⟨39108000074997681515374373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26072000049998454343582915 39108000074997681515374373)
            ·
              refine ⟨7332750014062065284132695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39108000074997681515374373 7332750014062065284132695)
              ·
                refine ⟨10999125021093097926199043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7332750014062065284132695 10999125021093097926199043)
                ·
                  refine ⟨16498687531639646889298565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10999125021093097926199043 16498687531639646889298565)
                  ·
                    refine ⟨3093503912182433791743481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16498687531639646889298565 3093503912182433791743481)
                    ·
                      refine ⟨2320127934136825343807611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093503912182433791743481 2320127934136825343807611)
                      ·
                        rfl

theorem cell23_4518433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_4518433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518433 prefixEnd_4518433 := by exact prefixLift 4518433
  have htrace : WordTrace (prefixWord ++ tailWord_4518433) baseStart_4518433 baseEnd_4518433 := by
    simpa [prefixWord, tailWord_4518433, baseEnd_4518433] using wordTrace_append hprefix tailTrace_4518433
  have hstable : (prefixWord ++ tailWord_4518433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518433).length < 2 ^ (prefixWord ++ tailWord_4518433).sum := by decide
  have hdescent : baseEnd_4518433 < baseStart_4518433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518454 : List Nat := [5, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_4518454 : Nat := 118140960795 + 4518454 * 2 ^ 59
def prefixEnd_4518454 : Nat := 4983230072969 + 3 ^ 40 * 4518454 * 2
def baseEnd_4518454 : Nat := 2320138717230569761645015

theorem tailTrace_4518454 : CollatzResearch.WordTrace tailWord_4518454 prefixEnd_4518454 2320138717230569761645015 := by
  unfold tailWord_4518454
  simp only [CollatzResearch.WordTrace]
  refine ⟨10300097273276270209430651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109867704248280215567260277 10300097273276270209430651)
  ·
    refine ⟨15450145909914405314145977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10300097273276270209430651 15450145909914405314145977)
    ·
      refine ⟨11587609432435803985609483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15450145909914405314145977 11587609432435803985609483)
      ·
        refine ⟨17381414148653705978414225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11587609432435803985609483 17381414148653705978414225)
        ·
          refine ⟨13036060611490279483810669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17381414148653705978414225 13036060611490279483810669)
          ·
            refine ⟨4888522729308854806429001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13036060611490279483810669 4888522729308854806429001)
            ·
              refine ⟨3666392046981641104821751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4888522729308854806429001 3666392046981641104821751)
              ·
                refine ⟨5499588070472461657232627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3666392046981641104821751 5499588070472461657232627)
                ·
                  refine ⟨8249382105708692485848941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5499588070472461657232627 8249382105708692485848941)
                  ·
                    refine ⟨3093518289640759682193353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8249382105708692485848941 3093518289640759682193353)
                    ·
                      refine ⟨2320138717230569761645015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093518289640759682193353 2320138717230569761645015)
                      ·
                        rfl

theorem cell23_4518454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_4518454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518454 prefixEnd_4518454 := by exact prefixLift 4518454
  have htrace : WordTrace (prefixWord ++ tailWord_4518454) baseStart_4518454 baseEnd_4518454 := by
    simpa [prefixWord, tailWord_4518454, baseEnd_4518454] using wordTrace_append hprefix tailTrace_4518454
  have hstable : (prefixWord ++ tailWord_4518454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518454).length < 2 ^ (prefixWord ++ tailWord_4518454).sum := by decide
  have hdescent : baseEnd_4518454 < baseStart_4518454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518479 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 5]
def baseStart_4518479 : Nat := 118140960795 + 4518479 * 2 ^ 59
def prefixEnd_4518479 : Nat := 4983230072969 + 3 ^ 40 * 4518479 * 2
def baseEnd_4518479 : Nat := 2320151554246932163832399

theorem tailTrace_4518479 : CollatzResearch.WordTrace tailWord_4518479 prefixEnd_4518479 2320151554246932163832399 := by
  unfold tailWord_4518479
  simp only [CollatzResearch.WordTrace]
  refine ⟨164802468197329752620550491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109868312131553168413700327 164802468197329752620550491)
  ·
    refine ⟨247203702295994628930825737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164802468197329752620550491 247203702295994628930825737)
    ·
      refine ⟨185402776721995971698119303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247203702295994628930825737 185402776721995971698119303)
      ·
        refine ⟨278104165082993957547178955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185402776721995971698119303 278104165082993957547178955)
        ·
          refine ⟨417156247624490936320768433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278104165082993957547178955 417156247624490936320768433)
          ·
            refine ⟨312867185718368202240576325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417156247624490936320768433 312867185718368202240576325)
            ·
              refine ⟨58662597322194037920108061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 312867185718368202240576325 58662597322194037920108061)
              ·
                refine ⟨21998473995822764220040523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58662597322194037920108061 21998473995822764220040523)
                ·
                  refine ⟨32997710993734146330060785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21998473995822764220040523 32997710993734146330060785)
                  ·
                    refine ⟨24748283245300609747545589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32997710993734146330060785 24748283245300609747545589)
                    ·
                      refine ⟨2320151554246932163832399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24748283245300609747545589 2320151554246932163832399)
                      ·
                        rfl

theorem cell23_4518479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_4518479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518479 prefixEnd_4518479 := by exact prefixLift 4518479
  have htrace : WordTrace (prefixWord ++ tailWord_4518479) baseStart_4518479 baseEnd_4518479 := by
    simpa [prefixWord, tailWord_4518479, baseEnd_4518479] using wordTrace_append hprefix tailTrace_4518479
  have hstable : (prefixWord ++ tailWord_4518479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518479).length < 2 ^ (prefixWord ++ tailWord_4518479).sum := by decide
  have hdescent : baseEnd_4518479 < baseStart_4518479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518499 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 2, 8]
def baseStart_4518499 : Nat := 118140960795 + 4518499 * 2 ^ 59
def prefixEnd_4518499 : Nat := 4983230072969 + 3 ^ 40 * 4518499 * 2
def baseEnd_4518499 : Nat := 773387274620007361860769

theorem tailTrace_4518499 : CollatzResearch.WordTrace tailWord_4518499 prefixEnd_4518499 773387274620007361860769 := by
  unfold tailWord_4518499
  simp only [CollatzResearch.WordTrace]
  refine ⟨164803197657257296036278551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109868798438171530690852367 164803197657257296036278551)
  ·
    refine ⟨247204796485885944054417827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164803197657257296036278551 247204796485885944054417827)
    ·
      refine ⟨370807194728828916081626741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247204796485885944054417827 370807194728828916081626741)
      ·
        refine ⟨34763174505827710882652507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 370807194728828916081626741 34763174505827710882652507)
        ·
          refine ⟨52144761758741566323978761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34763174505827710882652507 52144761758741566323978761)
          ·
            refine ⟨39108571319056174742984071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52144761758741566323978761 39108571319056174742984071)
            ·
              refine ⟨58662856978584262114476107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39108571319056174742984071 58662856978584262114476107)
              ·
                refine ⟨87994285467876393171714161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58662856978584262114476107 87994285467876393171714161)
                ·
                  refine ⟨65995714100907294878785621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87994285467876393171714161 65995714100907294878785621)
                  ·
                    refine ⟨773387274620007361860769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65995714100907294878785621 773387274620007361860769)
                    ·
                      rfl

theorem cell23_4518499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 8].length) (baseStart_4518499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518499 prefixEnd_4518499 := by exact prefixLift 4518499
  have htrace : WordTrace (prefixWord ++ tailWord_4518499) baseStart_4518499 baseEnd_4518499 := by
    simpa [prefixWord, tailWord_4518499, baseEnd_4518499] using wordTrace_append hprefix tailTrace_4518499
  have hstable : (prefixWord ++ tailWord_4518499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518499).length < 2 ^ (prefixWord ++ tailWord_4518499).sum := by decide
  have hdescent : baseEnd_4518499 < baseStart_4518499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518506 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_4518506 : Nat := 118140960795 + 4518506 * 2 ^ 59
def prefixEnd_4518506 : Nat := 4983230072969 + 3 ^ 40 * 4518506 * 2
def baseEnd_4518506 : Nat := 2320165418224603558194775

theorem tailTrace_4518506 : CollatzResearch.WordTrace tailWord_4518506 prefixEnd_4518506 2320165418224603558194775 := by
  unfold tailWord_4518506
  simp only [CollatzResearch.WordTrace]
  refine ⟨41200863242057984057945843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109868968645487957487855581 41200863242057984057945843)
  ·
    refine ⟨61801294863086976086918765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41200863242057984057945843 61801294863086976086918765)
    ·
      refine ⟨23175485573657616032594537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61801294863086976086918765 23175485573657616032594537)
      ·
        refine ⟨17381614180243212024445903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23175485573657616032594537 17381614180243212024445903)
        ·
          refine ⟨26072421270364818036668855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17381614180243212024445903 26072421270364818036668855)
          ·
            refine ⟨39108631905547227055003283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26072421270364818036668855 39108631905547227055003283)
            ·
              refine ⟨58662947858320840582504925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39108631905547227055003283 58662947858320840582504925)
              ·
                refine ⟨21998605446870315218439347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58662947858320840582504925 21998605446870315218439347)
                ·
                  refine ⟨32997908170305472827659021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21998605446870315218439347 32997908170305472827659021)
                  ·
                    refine ⟨12374215563864552310372133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32997908170305472827659021 12374215563864552310372133)
                    ·
                      refine ⟨2320165418224603558194775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12374215563864552310372133 2320165418224603558194775)
                      ·
                        rfl

theorem cell23_4518506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_4518506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518506 prefixEnd_4518506 := by exact prefixLift 4518506
  have htrace : WordTrace (prefixWord ++ tailWord_4518506) baseStart_4518506 baseEnd_4518506 := by
    simpa [prefixWord, tailWord_4518506, baseEnd_4518506] using wordTrace_append hprefix tailTrace_4518506
  have hstable : (prefixWord ++ tailWord_4518506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518506).length < 2 ^ (prefixWord ++ tailWord_4518506).sum := by decide
  have hdescent : baseEnd_4518506 < baseStart_4518506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518519 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_4518519 : Nat := 118140960795 + 4518519 * 2 ^ 59
def prefixEnd_4518519 : Nat := 4983230072969 + 3 ^ 40 * 4518519 * 2
def baseEnd_4518519 : Nat := 2320172093473112007332215

theorem tailTrace_4518519 : CollatzResearch.WordTrace tailWord_4518519 prefixEnd_4518519 2320172093473112007332215 := by
  unfold tailWord_4518519
  simp only [CollatzResearch.WordTrace]
  refine ⟨164803927117184839452006611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109869284744789892968004407 164803927117184839452006611)
  ·
    refine ⟨247205890675777259178009917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164803927117184839452006611 247205890675777259178009917)
    ·
      refine ⟨92702209003416472191753719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247205890675777259178009917 92702209003416472191753719)
      ·
        refine ⟨139053313505124708287630579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92702209003416472191753719 139053313505124708287630579)
        ·
          refine ⟨208579970257687062431445869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139053313505124708287630579 208579970257687062431445869)
          ·
            refine ⟨78217488846632648411792201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208579970257687062431445869 78217488846632648411792201)
            ·
              refine ⟨58663116634974486308844151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78217488846632648411792201 58663116634974486308844151)
              ·
                refine ⟨87994674952461729463266227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58663116634974486308844151 87994674952461729463266227)
                ·
                  refine ⟨131992012428692594194899341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87994674952461729463266227 131992012428692594194899341)
                  ·
                    refine ⟨49497004660759722823087253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 131992012428692594194899341 49497004660759722823087253)
                    ·
                      refine ⟨2320172093473112007332215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49497004660759722823087253 2320172093473112007332215)
                      ·
                        rfl

theorem cell23_4518519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_4518519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518519 prefixEnd_4518519 := by exact prefixLift 4518519
  have htrace : WordTrace (prefixWord ++ tailWord_4518519) baseStart_4518519 baseEnd_4518519 := by
    simpa [prefixWord, tailWord_4518519, baseEnd_4518519] using wordTrace_append hprefix tailTrace_4518519
  have hstable : (prefixWord ++ tailWord_4518519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518519).length < 2 ^ (prefixWord ++ tailWord_4518519).sum := by decide
  have hdescent : baseEnd_4518519 < baseStart_4518519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518533 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 3, 4]
def baseStart_4518533 : Nat := 118140960795 + 4518533 * 2 ^ 59
def prefixEnd_4518533 : Nat := 4983230072969 + 3 ^ 40 * 4518533 * 2
def baseEnd_4518533 : Nat := 773393094067424984185717

theorem tailTrace_4518533 : CollatzResearch.WordTrace tailWord_4518533 prefixEnd_4518533 773393094067424984185717 := by
  unfold tailWord_4518533
  simp only [CollatzResearch.WordTrace]
  refine ⟨164804437739134119843016253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109869625159422746562010835 164804437739134119843016253)
  ·
    refine ⟨61801664152175294941131095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164804437739134119843016253 61801664152175294941131095)
    ·
      refine ⟨92702496228262942411696643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61801664152175294941131095 92702496228262942411696643)
      ·
        refine ⟨139053744342394413617544965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92702496228262942411696643 139053744342394413617544965)
        ·
          refine ⟨26072577064198952553289681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139053744342394413617544965 26072577064198952553289681)
          ·
            refine ⟨19554432798149214414967261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26072577064198952553289681 19554432798149214414967261)
            ·
              refine ⟨7332912299305955405612723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19554432798149214414967261 7332912299305955405612723)
              ·
                refine ⟨10999368448958933108419085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7332912299305955405612723 10999368448958933108419085)
                ·
                  refine ⟨4124763168359599915657157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10999368448958933108419085 4124763168359599915657157)
                  ·
                    refine ⟨773393094067424984185717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4124763168359599915657157 773393094067424984185717)
                    ·
                      rfl

theorem cell23_4518533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_4518533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518533 prefixEnd_4518533 := by exact prefixLift 4518533
  have htrace : WordTrace (prefixWord ++ tailWord_4518533) baseStart_4518533 baseEnd_4518533 := by
    simpa [prefixWord, tailWord_4518533, baseEnd_4518533] using wordTrace_append hprefix tailTrace_4518533
  have hstable : (prefixWord ++ tailWord_4518533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518533).length < 2 ^ (prefixWord ++ tailWord_4518533).sum := by decide
  have hdescent : baseEnd_4518533 < baseStart_4518533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518560 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 3]
def baseStart_4518560 : Nat := 118140960795 + 4518560 * 2 ^ 59
def prefixEnd_4518560 : Nat := 4983230072969 + 3 ^ 40 * 4518560 * 2
def baseEnd_4518560 : Nat := 2320193146179946346919527

theorem tailTrace_4518560 : CollatzResearch.WordTrace tailWord_4518560 prefixEnd_4518560 2320193146179946346919527 := by
  unfold tailWord_4518560
  simp only [CollatzResearch.WordTrace]
  refine ⟨82402711255018151727124567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109870281673357535636166089 82402711255018151727124567)
  ·
    refine ⟨123604066882527227590686851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82402711255018151727124567 123604066882527227590686851)
    ·
      refine ⟨185406100323790841386030277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123604066882527227590686851 185406100323790841386030277)
      ·
        refine ⟨34763643810710782759880677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185406100323790841386030277 34763643810710782759880677)
        ·
          refine ⟨6518183214508271767477627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34763643810710782759880677 6518183214508271767477627)
          ·
            refine ⟨9777274821762407651216441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6518183214508271767477627 9777274821762407651216441)
            ·
              refine ⟨7332956116321805738412331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9777274821762407651216441 7332956116321805738412331)
              ·
                refine ⟨10999434174482708607618497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7332956116321805738412331 10999434174482708607618497)
                ·
                  refine ⟨8249575630862031455713873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10999434174482708607618497 8249575630862031455713873)
                  ·
                    refine ⟨6187181723146523591785405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8249575630862031455713873 6187181723146523591785405)
                    ·
                      refine ⟨2320193146179946346919527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6187181723146523591785405 2320193146179946346919527)
                      ·
                        rfl

theorem cell23_4518560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_4518560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518560 prefixEnd_4518560 := by exact prefixLift 4518560
  have htrace : WordTrace (prefixWord ++ tailWord_4518560) baseStart_4518560 baseEnd_4518560 := by
    simpa [prefixWord, tailWord_4518560, baseEnd_4518560] using wordTrace_append hprefix tailTrace_4518560
  have hstable : (prefixWord ++ tailWord_4518560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518560).length < 2 ^ (prefixWord ++ tailWord_4518560).sum := by decide
  have hdescent : baseEnd_4518560 < baseStart_4518560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518590 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_4518590 : Nat := 118140960795 + 4518590 * 2 ^ 59
def prefixEnd_4518590 : Nat := 4983230072969 + 3 ^ 40 * 4518590 * 2
def baseEnd_4518590 : Nat := 2320208550599581229544389

theorem tailTrace_4518590 : CollatzResearch.WordTrace tailWord_4518590 prefixEnd_4518590 2320208550599581229544389 := by
  unfold tailWord_4518590
  simp only [CollatzResearch.WordTrace]
  refine ⟨20600814587490952322230153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109871011133285079051894149 20600814587490952322230153)
  ·
    refine ⟨15450610940618214241672615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20600814587490952322230153 15450610940618214241672615)
    ·
      refine ⟨23175916410927321362508923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15450610940618214241672615 23175916410927321362508923)
      ·
        refine ⟨34763874616390982043763385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23175916410927321362508923 34763874616390982043763385)
        ·
          refine ⟨26072905962293236532822539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34763874616390982043763385 26072905962293236532822539)
          ·
            refine ⟨39109358943439854799233809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26072905962293236532822539 39109358943439854799233809)
            ·
              refine ⟨29332019207579891099425357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39109358943439854799233809 29332019207579891099425357)
              ·
                refine ⟨10999507202842459162284509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29332019207579891099425357 10999507202842459162284509)
                ·
                  refine ⟨4124815201065922185856691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10999507202842459162284509 4124815201065922185856691)
                  ·
                    refine ⟨6187222801598883278785037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4124815201065922185856691 6187222801598883278785037)
                    ·
                      refine ⟨2320208550599581229544389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6187222801598883278785037 2320208550599581229544389)
                      ·
                        rfl

theorem cell23_4518590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_4518590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518590 prefixEnd_4518590 := by exact prefixLift 4518590
  have htrace : WordTrace (prefixWord ++ tailWord_4518590) baseStart_4518590 baseEnd_4518590 := by
    simpa [prefixWord, tailWord_4518590, baseEnd_4518590] using wordTrace_append hprefix tailTrace_4518590
  have hstable : (prefixWord ++ tailWord_4518590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518590).length < 2 ^ (prefixWord ++ tailWord_4518590).sum := by decide
  have hdescent : baseEnd_4518590 < baseStart_4518590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518627 : List Nat := [1, 1, 1, 7, 1, 3, 2, 1, 1, 5]
def baseStart_4518627 : Nat := 118140960795 + 4518627 * 2 ^ 59
def prefixEnd_4518627 : Nat := 4983230072969 + 3 ^ 40 * 4518627 * 2
def baseEnd_4518627 : Nat := 773409183127932528260573

theorem tailTrace_4518627 : CollatzResearch.WordTrace tailWord_4518627 prefixEnd_4518627 773409183127932528260573 := by
  unfold tailWord_4518627
  simp only [CollatzResearch.WordTrace]
  refine ⟨164807866200793573896938135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109871910800529049264625423 164807866200793573896938135)
  ·
    refine ⟨247211799301190360845407203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164807866200793573896938135 247211799301190360845407203)
    ·
      refine ⟨370817698951785541268110805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247211799301190360845407203 370817698951785541268110805)
      ·
        refine ⟨8691039819182473623471347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 370817698951785541268110805 8691039819182473623471347)
        ·
          refine ⟨13036559728773710435207021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8691039819182473623471347 13036559728773710435207021)
          ·
            refine ⟨4888709898290141413202633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13036559728773710435207021 4888709898290141413202633)
            ·
              refine ⟨3666532423717606059901975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4888709898290141413202633 3666532423717606059901975)
              ·
                refine ⟨5499798635576409089852963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3666532423717606059901975 5499798635576409089852963)
                ·
                  refine ⟨8249697953364613634779445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5499798635576409089852963 8249697953364613634779445)
                  ·
                    refine ⟨773409183127932528260573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8249697953364613634779445 773409183127932528260573)
                    ·
                      rfl

theorem cell23_4518627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 1, 5].length) (baseStart_4518627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518627 prefixEnd_4518627 := by exact prefixLift 4518627
  have htrace : WordTrace (prefixWord ++ tailWord_4518627) baseStart_4518627 baseEnd_4518627 := by
    simpa [prefixWord, tailWord_4518627, baseEnd_4518627] using wordTrace_append hprefix tailTrace_4518627
  have hstable : (prefixWord ++ tailWord_4518627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518627).length < 2 ^ (prefixWord ++ tailWord_4518627).sum := by decide
  have hdescent : baseEnd_4518627 < baseStart_4518627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518698 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4518698 : Nat := 118140960795 + 4518698 * 2 ^ 59
def prefixEnd_4518698 : Nat := 4983230072969 + 3 ^ 40 * 4518698 * 2
def baseEnd_4518698 : Nat := 2320264006510266806993893

theorem tailTrace_4518698 : CollatzResearch.WordTrace tailWord_4518698 prefixEnd_4518698 2320264006510266806993893 := by
  unfold tailWord_4518698
  simp only [CollatzResearch.WordTrace]
  refine ⟨41202613945884088255693187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109873637189024235348515165 41202613945884088255693187)
  ·
    refine ⟨61803920918826132383539781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41202613945884088255693187 61803920918826132383539781)
    ·
      refine ⟨11588235172279899821913709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61803920918826132383539781 11588235172279899821913709)
      ·
        refine ⟨4345588189604962433217641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11588235172279899821913709 4345588189604962433217641)
        ·
          refine ⟨3259191142203721824913231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4345588189604962433217641 3259191142203721824913231)
          ·
            refine ⟨4888786713305582737369847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3259191142203721824913231 4888786713305582737369847)
            ·
              refine ⟨7333180069958374106054771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4888786713305582737369847 7333180069958374106054771)
              ·
                refine ⟨10999770104937561159082157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7333180069958374106054771 10999770104937561159082157)
                ·
                  refine ⟨4124913789351585434655809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10999770104937561159082157 4124913789351585434655809)
                  ·
                    refine ⟨3093685342013689075991857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4124913789351585434655809 3093685342013689075991857)
                    ·
                      refine ⟨2320264006510266806993893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093685342013689075991857 2320264006510266806993893)
                      ·
                        rfl

theorem cell23_4518698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4518698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518698 prefixEnd_4518698 := by exact prefixLift 4518698
  have htrace : WordTrace (prefixWord ++ tailWord_4518698) baseStart_4518698 baseEnd_4518698 := by
    simpa [prefixWord, tailWord_4518698, baseEnd_4518698] using wordTrace_append hprefix tailTrace_4518698
  have hstable : (prefixWord ++ tailWord_4518698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518698).length < 2 ^ (prefixWord ++ tailWord_4518698).sum := by decide
  have hdescent : baseEnd_4518698 < baseStart_4518698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518703 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 2, 8, 2]
def baseStart_4518703 : Nat := 118140960795 + 4518703 * 2 ^ 59
def prefixEnd_4518703 : Nat := 4983230072969 + 3 ^ 40 * 4518703 * 2
def baseEnd_4518703 : Nat := 2320266573913539287431369

theorem tailTrace_4518703 : CollatzResearch.WordTrace tailWord_4518703 prefixEnd_4518703 2320266573913539287431369 := by
  unfold tailWord_4518703
  simp only [CollatzResearch.WordTrace]
  refine ⟨164810638148518238876704763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109873758765678825917803175 164810638148518238876704763)
  ·
    refine ⟨247215957222777358315057145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164810638148518238876704763 247215957222777358315057145)
    ·
      refine ⟨185411967917083018736292859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247215957222777358315057145 185411967917083018736292859)
      ·
        refine ⟨278117951875624528104439289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185411967917083018736292859 278117951875624528104439289)
        ·
          refine ⟨208588463906718396078329467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278117951875624528104439289 208588463906718396078329467)
          ·
            refine ⟨312882695860077594117494201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208588463906718396078329467 312882695860077594117494201)
            ·
              refine ⟨234662021895058195588120651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312882695860077594117494201 234662021895058195588120651)
              ·
                refine ⟨351993032842587293382180977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234662021895058195588120651 351993032842587293382180977)
                ·
                  refine ⟨263994774631940470036635733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351993032842587293382180977 263994774631940470036635733)
                  ·
                    refine ⟨3093688765218052383241825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 263994774631940470036635733 3093688765218052383241825)
                    ·
                      refine ⟨2320266573913539287431369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093688765218052383241825 2320266573913539287431369)
                      ·
                        rfl

theorem cell23_4518703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 8, 2].length) (baseStart_4518703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518703 prefixEnd_4518703 := by exact prefixLift 4518703
  have htrace : WordTrace (prefixWord ++ tailWord_4518703) baseStart_4518703 baseEnd_4518703 := by
    simpa [prefixWord, tailWord_4518703, baseEnd_4518703] using wordTrace_append hprefix tailTrace_4518703
  have hstable : (prefixWord ++ tailWord_4518703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518703).length < 2 ^ (prefixWord ++ tailWord_4518703).sum := by decide
  have hdescent : baseEnd_4518703 < baseStart_4518703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518737 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 1, 4, 2]
def baseStart_4518737 : Nat := 118140960795 + 4518737 * 2 ^ 59
def prefixEnd_4518737 : Nat := 4983230072969 + 3 ^ 40 * 4518737 * 2
def baseEnd_4518737 : Nat := 2320284032255792154406213

theorem tailTrace_4518737 : CollatzResearch.WordTrace tailWord_4518737 prefixEnd_4518737 2320284032255792154406213 := by
  unfold tailWord_4518737
  simp only [CollatzResearch.WordTrace]
  refine ⟨164811878230395062683442465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109874585486930041788961643 164811878230395062683442465)
  ·
    refine ⟨123608908672796297012581849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164811878230395062683442465 123608908672796297012581849)
    ·
      refine ⟨92706681504597222759436387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123608908672796297012581849 92706681504597222759436387)
      ·
        refine ⟨139060022256895834139154581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92706681504597222759436387 139060022256895834139154581)
        ·
          refine ⟨6518438543291992225272871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 139060022256895834139154581 6518438543291992225272871)
          ·
            refine ⟨9777657814937988337909307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6518438543291992225272871 9777657814937988337909307)
            ·
              refine ⟨14666486722406982506863961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9777657814937988337909307 14666486722406982506863961)
              ·
                refine ⟨10999865041805236880147971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14666486722406982506863961 10999865041805236880147971)
                ·
                  refine ⟨16499797562707855320221957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10999865041805236880147971 16499797562707855320221957)
                  ·
                    refine ⟨3093712043007722872541617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16499797562707855320221957 3093712043007722872541617)
                    ·
                      refine ⟨2320284032255792154406213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093712043007722872541617 2320284032255792154406213)
                      ·
                        rfl

theorem cell23_4518737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 4, 2].length) (baseStart_4518737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518737 prefixEnd_4518737 := by exact prefixLift 4518737
  have htrace : WordTrace (prefixWord ++ tailWord_4518737) baseStart_4518737 baseEnd_4518737 := by
    simpa [prefixWord, tailWord_4518737, baseEnd_4518737] using wordTrace_append hprefix tailTrace_4518737
  have hstable : (prefixWord ++ tailWord_4518737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518737).length < 2 ^ (prefixWord ++ tailWord_4518737).sum := by decide
  have hdescent : baseEnd_4518737 < baseStart_4518737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518897 : List Nat := [1, 2, 2, 2, 4, 1, 3, 2, 1, 5]
def baseStart_4518897 : Nat := 118140960795 + 4518897 * 2 ^ 59
def prefixEnd_4518897 : Nat := 4983230072969 + 3 ^ 40 * 4518897 * 2
def baseEnd_4518897 : Nat := 773455396386837176135159

theorem tailTrace_4518897 : CollatzResearch.WordTrace tailWord_4518897 prefixEnd_4518897 773455396386837176135159 := by
  unfold tailWord_4518897
  simp only [CollatzResearch.WordTrace]
  refine ⟨164817713909815410009266945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109878475939876940006177963 164817713909815410009266945)
  ·
    refine ⟨123613285432361557506950209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164817713909815410009266945 123613285432361557506950209)
    ·
      refine ⟨92709964074271168130212657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123613285432361557506950209 92709964074271168130212657)
      ·
        refine ⟨69532473055703376097659493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92709964074271168130212657 69532473055703376097659493)
        ·
          refine ⟨13037338697944383018311155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69532473055703376097659493 13037338697944383018311155)
          ·
            refine ⟨19556008046916574527466733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13037338697944383018311155 19556008046916574527466733)
            ·
              refine ⟨7333503017593715447800025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19556008046916574527466733 7333503017593715447800025)
              ·
                refine ⟨5500127263195286585850019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7333503017593715447800025 5500127263195286585850019)
                ·
                  refine ⟨8250190894792929878775029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5500127263195286585850019 8250190894792929878775029)
                  ·
                    refine ⟨773455396386837176135159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8250190894792929878775029 773455396386837176135159)
                    ·
                      rfl

theorem cell23_4518897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_4518897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518897 prefixEnd_4518897 := by exact prefixLift 4518897
  have htrace : WordTrace (prefixWord ++ tailWord_4518897) baseStart_4518897 baseEnd_4518897 := by
    simpa [prefixWord, tailWord_4518897, baseEnd_4518897] using wordTrace_append hprefix tailTrace_4518897
  have hstable : (prefixWord ++ tailWord_4518897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518897).length < 2 ^ (prefixWord ++ tailWord_4518897).sum := by decide
  have hdescent : baseEnd_4518897 < baseStart_4518897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518903 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_4518903 : Nat := 118140960795 + 4518903 * 2 ^ 59
def prefixEnd_4518903 : Nat := 4983230072969 + 3 ^ 40 * 4518903 * 2
def baseEnd_4518903 : Nat := 2320369270044438504930449

theorem tailTrace_4518903 : CollatzResearch.WordTrace tailWord_4518903 prefixEnd_4518903 2320369270044438504930449 := by
  unfold tailWord_4518903
  simp only [CollatzResearch.WordTrace]
  refine ⟨164817932747793673033985363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109878621831862448689323575 164817932747793673033985363)
  ·
    refine ⟨247226899121690509550978045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164817932747793673033985363 247226899121690509550978045)
    ·
      refine ⟨92710087170633941081616767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247226899121690509550978045 92710087170633941081616767)
      ·
        refine ⟨139065130755950911622425151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92710087170633941081616767 139065130755950911622425151)
        ·
          refine ⟨208597696133926367433637727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139065130755950911622425151 208597696133926367433637727)
          ·
            refine ⟨312896544200889551150456591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208597696133926367433637727 312896544200889551150456591)
            ·
              refine ⟨469344816301334326725684887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312896544200889551150456591 469344816301334326725684887)
              ·
                refine ⟨704017224452001490088527331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469344816301334326725684887 704017224452001490088527331)
                ·
                  refine ⟨1056025836678002235132790997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704017224452001490088527331 1056025836678002235132790997)
                  ·
                    refine ⟨24750605547140677385924789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1056025836678002235132790997 24750605547140677385924789)
                    ·
                      refine ⟨2320369270044438504930449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24750605547140677385924789 2320369270044438504930449)
                      ·
                        rfl

theorem cell23_4518903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_4518903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518903 prefixEnd_4518903 := by exact prefixLift 4518903
  have htrace : WordTrace (prefixWord ++ tailWord_4518903) baseStart_4518903 baseEnd_4518903 := by
    simpa [prefixWord, tailWord_4518903, baseEnd_4518903] using wordTrace_append hprefix tailTrace_4518903
  have hstable : (prefixWord ++ tailWord_4518903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518903).length < 2 ^ (prefixWord ++ tailWord_4518903).sum := by decide
  have hdescent : baseEnd_4518903 < baseStart_4518903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518923 : List Nat := [1, 1, 1, 1, 6, 13]
def baseStart_4518923 : Nat := 118140960795 + 4518923 * 2 ^ 59
def prefixEnd_4518923 : Nat := 4983230072969 + 3 ^ 40 * 4518923 * 2
def baseEnd_4518923 : Nat := 9548886994475425624199

theorem tailTrace_4518923 : CollatzResearch.WordTrace tailWord_4518923 prefixEnd_4518923 9548886994475425624199 := by
  unfold tailWord_4518923
  simp only [CollatzResearch.WordTrace]
  refine ⟨164818662207721216449713423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109879108138480810966475615 164818662207721216449713423)
  ·
    refine ⟨247227993311581824674570135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164818662207721216449713423 247227993311581824674570135)
    ·
      refine ⟨370841989967372737011855203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247227993311581824674570135 370841989967372737011855203)
      ·
        refine ⟨556262984951059105517782805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370841989967372737011855203 556262984951059105517782805)
        ·
          refine ⟨26074827419580895571146069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 556262984951059105517782805 26074827419580895571146069)
          ·
            refine ⟨9548886994475425624199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 26074827419580895571146069 9548886994475425624199)
            ·
              rfl

theorem cell23_4518923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 13].length) (baseStart_4518923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518923 prefixEnd_4518923 := by exact prefixLift 4518923
  have htrace : WordTrace (prefixWord ++ tailWord_4518923) baseStart_4518923 baseEnd_4518923 := by
    simpa [prefixWord, tailWord_4518923, baseEnd_4518923] using wordTrace_append hprefix tailTrace_4518923
  have hstable : (prefixWord ++ tailWord_4518923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518923).length < 2 ^ (prefixWord ++ tailWord_4518923).sum := by decide
  have hdescent : baseEnd_4518923 < baseStart_4518923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518944 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 1, 6]
def baseStart_4518944 : Nat := 118140960795 + 4518944 * 2 ^ 59
def prefixEnd_4518944 : Nat := 4983230072969 + 3 ^ 40 * 4518944 * 2
def baseEnd_4518944 : Nat := 773463440917090948172587

theorem tailTrace_4518944 : CollatzResearch.WordTrace tailWord_4518944 prefixEnd_4518944 773463440917090948172587 := by
  unfold tailWord_4518944
  simp only [CollatzResearch.WordTrace]
  refine ⟨82409714070322568518113943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109879618760430091357485257 82409714070322568518113943)
  ·
    refine ⟨123614571105483852777170915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82409714070322568518113943 123614571105483852777170915)
    ·
      refine ⟨185421856658225779165756373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123614571105483852777170915 185421856658225779165756373)
      ·
        refine ⟨4345824765427166699197415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 185421856658225779165756373 4345824765427166699197415)
        ·
          refine ⟨6518737148140750048796123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4345824765427166699197415 6518737148140750048796123)
          ·
            refine ⟨9778105722211125073194185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6518737148140750048796123 9778105722211125073194185)
            ·
              refine ⟨7333579291658343804895639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9778105722211125073194185 7333579291658343804895639)
              ·
                refine ⟨11000368937487515707343459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7333579291658343804895639 11000368937487515707343459)
                ·
                  refine ⟨16500553406231273561015189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11000368937487515707343459 16500553406231273561015189)
                  ·
                    refine ⟨773463440917090948172587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16500553406231273561015189 773463440917090948172587)
                    ·
                      rfl

theorem cell23_4518944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 1, 6].length) (baseStart_4518944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518944 prefixEnd_4518944 := by exact prefixLift 4518944
  have htrace : WordTrace (prefixWord ++ tailWord_4518944) baseStart_4518944 baseEnd_4518944 := by
    simpa [prefixWord, tailWord_4518944, baseEnd_4518944] using wordTrace_append hprefix tailTrace_4518944
  have hstable : (prefixWord ++ tailWord_4518944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518944).length < 2 ^ (prefixWord ++ tailWord_4518944).sum := by decide
  have hdescent : baseEnd_4518944 < baseStart_4518944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518947 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 4]
def baseStart_4518947 : Nat := 118140960795 + 4518947 * 2 ^ 59
def prefixEnd_4518947 : Nat := 4983230072969 + 3 ^ 40 * 4518947 * 2
def baseEnd_4518947 : Nat := 2320391863193236332780247

theorem tailTrace_4518947 : CollatzResearch.WordTrace tailWord_4518947 prefixEnd_4518947 2320391863193236332780247 := by
  unfold tailWord_4518947
  simp only [CollatzResearch.WordTrace]
  refine ⟨164819537559634268548587095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109879691706422845699058063 164819537559634268548587095)
  ·
    refine ⟨247229306339451402822880643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164819537559634268548587095 247229306339451402822880643)
    ·
      refine ⟨370843959509177104234320965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247229306339451402822880643 370843959509177104234320965)
      ·
        refine ⟨69533242407970707043935181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 370843959509177104234320965 69533242407970707043935181)
        ·
          refine ⟨26074965902989015141475693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69533242407970707043935181 26074965902989015141475693)
          ·
            refine ⟨9778112213620880678053385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26074965902989015141475693 9778112213620880678053385)
            ·
              refine ⟨7333584160215660508540039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9778112213620880678053385 7333584160215660508540039)
              ·
                refine ⟨11000376240323490762810059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7333584160215660508540039 11000376240323490762810059)
                ·
                  refine ⟨16500564360485236144215089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11000376240323490762810059 16500564360485236144215089)
                  ·
                    refine ⟨12375423270363927108161317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16500564360485236144215089 12375423270363927108161317)
                    ·
                      refine ⟨2320391863193236332780247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12375423270363927108161317 2320391863193236332780247)
                      ·
                        rfl

theorem cell23_4518947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_4518947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518947 prefixEnd_4518947 := by exact prefixLift 4518947
  have htrace : WordTrace (prefixWord ++ tailWord_4518947) baseStart_4518947 baseEnd_4518947 := by
    simpa [prefixWord, tailWord_4518947, baseEnd_4518947] using wordTrace_append hprefix tailTrace_4518947
  have hstable : (prefixWord ++ tailWord_4518947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518947).length < 2 ^ (prefixWord ++ tailWord_4518947).sum := by decide
  have hdescent : baseEnd_4518947 < baseStart_4518947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518951 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_4518951 : Nat := 118140960795 + 4518951 * 2 ^ 59
def prefixEnd_4518951 : Nat := 4983230072969 + 3 ^ 40 * 4518951 * 2
def baseEnd_4518951 : Nat := 2320393917115854317130229

theorem tailTrace_4518951 : CollatzResearch.WordTrace tailWord_4518951 prefixEnd_4518951 2320393917115854317130229 := by
  unfold tailWord_4518951
  simp only [CollatzResearch.WordTrace]
  refine ⟨164819683451619777231732707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109879788967746518154488471 164819683451619777231732707)
  ·
    refine ⟨247229525177429665847599061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164819683451619777231732707 247229525177429665847599061)
    ·
      refine ⟨5794441996346007793303103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 247229525177429665847599061 5794441996346007793303103)
      ·
        refine ⟨8691662994519011689954655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5794441996346007793303103 8691662994519011689954655)
        ·
          refine ⟨13037494491778517534931983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8691662994519011689954655 13037494491778517534931983)
          ·
            refine ⟨19556241737667776302397975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13037494491778517534931983 19556241737667776302397975)
            ·
              refine ⟨29334362606501664453596963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19556241737667776302397975 29334362606501664453596963)
              ·
                refine ⟨44001543909752496680395445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29334362606501664453596963 44001543909752496680395445)
                ·
                  refine ⟨4125144741539296563787073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44001543909752496680395445 4125144741539296563787073)
                  ·
                    refine ⟨3093858556154472422840305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4125144741539296563787073 3093858556154472422840305)
                    ·
                      refine ⟨2320393917115854317130229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093858556154472422840305 2320393917115854317130229)
                      ·
                        rfl

theorem cell23_4518951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_4518951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518951 prefixEnd_4518951 := by exact prefixLift 4518951
  have htrace : WordTrace (prefixWord ++ tailWord_4518951) baseStart_4518951 baseEnd_4518951 := by
    simpa [prefixWord, tailWord_4518951, baseEnd_4518951] using wordTrace_append hprefix tailTrace_4518951
  have hstable : (prefixWord ++ tailWord_4518951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518951).length < 2 ^ (prefixWord ++ tailWord_4518951).sum := by decide
  have hdescent : baseEnd_4518951 < baseStart_4518951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518964 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_4518964 : Nat := 118140960795 + 4518964 * 2 ^ 59
def prefixEnd_4518964 : Nat := 4983230072969 + 3 ^ 40 * 4518964 * 2
def baseEnd_4518964 : Nat := 2320400592364362766267669

theorem tailTrace_4518964 : CollatzResearch.WordTrace tailWord_4518964 prefixEnd_4518964 2320400592364362766267669 := by
  unfold tailWord_4518964
  simp only [CollatzResearch.WordTrace]
  refine ⟨82410078800286340225977973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109880105067048453634637297 82410078800286340225977973)
  ·
    refine ⟨7725944887526844396185435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82410078800286340225977973 7725944887526844396185435)
    ·
      refine ⟨11588917331290266594278153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7725944887526844396185435 11588917331290266594278153)
      ·
        refine ⟨8691687998467699945708615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11588917331290266594278153 8691687998467699945708615)
        ·
          refine ⟨13037531997701549918562923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8691687998467699945708615 13037531997701549918562923)
          ·
            refine ⟨19556297996552324877844385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13037531997701549918562923 19556297996552324877844385)
            ·
              refine ⟨14667223497414243658383289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19556297996552324877844385 14667223497414243658383289)
              ·
                refine ⟨11000417623060682743787467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14667223497414243658383289 11000417623060682743787467)
                ·
                  refine ⟨16500626434591024115681201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11000417623060682743787467 16500626434591024115681201)
                  ·
                    refine ⟨12375469825943268086760901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16500626434591024115681201 12375469825943268086760901)
                    ·
                      refine ⟨2320400592364362766267669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12375469825943268086760901 2320400592364362766267669)
                      ·
                        rfl

theorem cell23_4518964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_4518964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518964 prefixEnd_4518964 := by exact prefixLift 4518964
  have htrace : WordTrace (prefixWord ++ tailWord_4518964) baseStart_4518964 baseEnd_4518964 := by
    simpa [prefixWord, tailWord_4518964, baseEnd_4518964] using wordTrace_append hprefix tailTrace_4518964
  have hstable : (prefixWord ++ tailWord_4518964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518964).length < 2 ^ (prefixWord ++ tailWord_4518964).sum := by decide
  have hdescent : baseEnd_4518964 < baseStart_4518964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518967 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 4, 1, 3]
def baseStart_4518967 : Nat := 118140960795 + 4518967 * 2 ^ 59
def prefixEnd_4518967 : Nat := 4983230072969 + 3 ^ 40 * 4518967 * 2
def baseEnd_4518967 : Nat := 2320402132806326254530155

theorem tailTrace_4518967 : CollatzResearch.WordTrace tailWord_4518967 prefixEnd_4518967 2320402132806326254530155 := by
  unfold tailWord_4518967
  simp only [CollatzResearch.WordTrace]
  refine ⟨164820267019561811964315155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109880178013041207976210103 164820267019561811964315155)
  ·
    refine ⟨247230400529342717946472733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164820267019561811964315155 247230400529342717946472733)
    ·
      refine ⟨92711400198503519229927275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247230400529342717946472733 92711400198503519229927275)
      ·
        refine ⟨139067100297755278844890913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92711400198503519229927275 139067100297755278844890913)
        ·
          refine ⟨104300325223316459133668185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139067100297755278844890913 104300325223316459133668185)
          ·
            refine ⟨78225243917487344350251139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104300325223316459133668185 78225243917487344350251139)
            ·
              refine ⟨117337865876231016525376709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78225243917487344350251139 117337865876231016525376709)
              ·
                refine ⟨22000849851793315598508133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117337865876231016525376709 22000849851793315598508133)
                ·
                  refine ⟨4125159347211246674720275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22000849851793315598508133 4125159347211246674720275)
                  ·
                    refine ⟨6187739020816870012080413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4125159347211246674720275 6187739020816870012080413)
                    ·
                      refine ⟨2320402132806326254530155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6187739020816870012080413 2320402132806326254530155)
                      ·
                        rfl

theorem cell23_4518967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_4518967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518967 prefixEnd_4518967 := by exact prefixLift 4518967
  have htrace : WordTrace (prefixWord ++ tailWord_4518967) baseStart_4518967 baseEnd_4518967 := by
    simpa [prefixWord, tailWord_4518967, baseEnd_4518967] using wordTrace_append hprefix tailTrace_4518967
  have hstable : (prefixWord ++ tailWord_4518967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518967).length < 2 ^ (prefixWord ++ tailWord_4518967).sum := by decide
  have hdescent : baseEnd_4518967 < baseStart_4518967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518968 : List Nat := [2, 1, 2, 1, 5, 2, 2, 3, 1, 2, 2]
def baseStart_4518968 : Nat := 118140960795 + 4518968 * 2 ^ 59
def prefixEnd_4518968 : Nat := 4983230072969 + 3 ^ 40 * 4518968 * 2
def baseEnd_4518968 : Nat := 2320402646286980750617651

theorem tailTrace_4518968 : CollatzResearch.WordTrace tailWord_4518968 prefixEnd_4518968 2320402646286980750617651 := by
  unfold tailWord_4518968
  simp only [CollatzResearch.WordTrace]
  refine ⟨82410151746279094567550779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109880202328372126090067705 82410151746279094567550779)
  ·
    refine ⟨123615227619418641851326169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82410151746279094567550779 123615227619418641851326169)
    ·
      refine ⟨92711420714563981388494627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123615227619418641851326169 92711420714563981388494627)
      ·
        refine ⟨139067131071845972082741941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92711420714563981388494627 139067131071845972082741941)
        ·
          refine ⟨13037543537985559882757057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139067131071845972082741941 13037543537985559882757057)
          ·
            refine ⟨9778157653489169912067793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13037543537985559882757057 9778157653489169912067793)
            ·
              refine ⟨7333618240116877434050845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9778157653489169912067793 7333618240116877434050845)
              ·
                refine ⟨2750106840043829037769067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7333618240116877434050845 2750106840043829037769067)
                ·
                  refine ⟨4125160260065743556653601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2750106840043829037769067 4125160260065743556653601)
                  ·
                    refine ⟨3093870195049307667490201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4125160260065743556653601 3093870195049307667490201)
                    ·
                      refine ⟨2320402646286980750617651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093870195049307667490201 2320402646286980750617651)
                      ·
                        rfl

theorem cell23_4518968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 1, 2, 2].length) (baseStart_4518968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518968 prefixEnd_4518968 := by exact prefixLift 4518968
  have htrace : WordTrace (prefixWord ++ tailWord_4518968) baseStart_4518968 baseEnd_4518968 := by
    simpa [prefixWord, tailWord_4518968, baseEnd_4518968] using wordTrace_append hprefix tailTrace_4518968
  have hstable : (prefixWord ++ tailWord_4518968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518968).length < 2 ^ (prefixWord ++ tailWord_4518968).sum := by decide
  have hdescent : baseEnd_4518968 < baseStart_4518968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518998 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_4518998 : Nat := 118140960795 + 4518998 * 2 ^ 59
def prefixEnd_4518998 : Nat := 4983230072969 + 3 ^ 40 * 4518998 * 2
def baseEnd_4518998 : Nat := 2320418050706615633242513

theorem tailTrace_4518998 : CollatzResearch.WordTrace tailWord_4518998 prefixEnd_4518998 2320418050706615633242513 := by
  unfold tailWord_4518998
  simp only [CollatzResearch.WordTrace]
  refine ⟨10301337355153094016168353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109880931788299669505795765 10301337355153094016168353)
  ·
    refine ⟨7726003016364820512126265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10301337355153094016168353 7726003016364820512126265)
    ·
      refine ⟨5794502262273615384094699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7726003016364820512126265 5794502262273615384094699)
      ·
        refine ⟨8691753393410423076142049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5794502262273615384094699 8691753393410423076142049)
        ·
          refine ⟨6518815045057817307106537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8691753393410423076142049 6518815045057817307106537)
          ·
            refine ⟨4889111283793362980329903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6518815045057817307106537 4889111283793362980329903)
            ·
              refine ⟨7333666925690044470494855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4889111283793362980329903 7333666925690044470494855)
              ·
                refine ⟨11000500388535066705742283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7333666925690044470494855 11000500388535066705742283)
                ·
                  refine ⟨16500750582802600058613425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11000500388535066705742283 16500750582802600058613425)
                  ·
                    refine ⟨12375562937101950043960069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16500750582802600058613425 12375562937101950043960069)
                    ·
                      refine ⟨2320418050706615633242513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12375562937101950043960069 2320418050706615633242513)
                      ·
                        rfl

theorem cell23_4518998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_4518998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518998 prefixEnd_4518998 := by exact prefixLift 4518998
  have htrace : WordTrace (prefixWord ++ tailWord_4518998) baseStart_4518998 baseEnd_4518998 := by
    simpa [prefixWord, tailWord_4518998, baseEnd_4518998] using wordTrace_append hprefix tailTrace_4518998
  have hstable : (prefixWord ++ tailWord_4518998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518998).length < 2 ^ (prefixWord ++ tailWord_4518998).sum := by decide
  have hdescent : baseEnd_4518998 < baseStart_4518998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519000 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 2, 6]
def baseStart_4519000 : Nat := 118140960795 + 4519000 * 2 ^ 59
def prefixEnd_4519000 : Nat := 4983230072969 + 3 ^ 40 * 4519000 * 2
def baseEnd_4519000 : Nat := 773473025889308208472501

theorem tailTrace_4519000 : CollatzResearch.WordTrace tailWord_4519000 prefixEnd_4519000 773473025889308208472501 := by
  unfold tailWord_4519000
  simp only [CollatzResearch.WordTrace]
  refine ⟨82410735314221129300133227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109880980418961505733510969 82410735314221129300133227)
  ·
    refine ⟨123616102971331693950199841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82410735314221129300133227 123616102971331693950199841)
    ·
      refine ⟨92712077228498770462649881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123616102971331693950199841 92712077228498770462649881)
      ·
        refine ⟨69534057921374077846987411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92712077228498770462649881 69534057921374077846987411)
        ·
          refine ⟨104301086882061116770481117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69534057921374077846987411 104301086882061116770481117)
          ·
            refine ⟨39112907580772918788930419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104301086882061116770481117 39112907580772918788930419)
            ·
              refine ⟨58669361371159378183395629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39112907580772918788930419 58669361371159378183395629)
              ·
                refine ⟨22001010514184766818773361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58669361371159378183395629 22001010514184766818773361)
                ·
                  refine ⟨16500757885638575114080021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22001010514184766818773361 16500757885638575114080021)
                  ·
                    refine ⟨773473025889308208472501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16500757885638575114080021 773473025889308208472501)
                    ·
                      rfl

theorem cell23_4519000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_4519000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519000 prefixEnd_4519000 := by exact prefixLift 4519000
  have htrace : WordTrace (prefixWord ++ tailWord_4519000) baseStart_4519000 baseEnd_4519000 := by
    simpa [prefixWord, tailWord_4519000, baseEnd_4519000] using wordTrace_append hprefix tailTrace_4519000
  have hstable : (prefixWord ++ tailWord_4519000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519000).length < 2 ^ (prefixWord ++ tailWord_4519000).sum := by decide
  have hdescent : baseEnd_4519000 < baseStart_4519000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519024 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 6, 2, 2]
def baseStart_4519024 : Nat := 118140960795 + 4519024 * 2 ^ 59
def prefixEnd_4519024 : Nat := 4983230072969 + 3 ^ 40 * 4519024 * 2
def baseEnd_4519024 : Nat := 2320431401203632531517393

theorem tailTrace_4519024 : CollatzResearch.WordTrace tailWord_4519024 prefixEnd_4519024 2320431401203632531517393 := by
  unfold tailWord_4519024
  simp only [CollatzResearch.WordTrace]
  refine ⟨82411172990177655349570063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109881563986903540466093417 82411172990177655349570063)
  ·
    refine ⟨123616759485266483024355095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82411172990177655349570063 123616759485266483024355095)
    ·
      refine ⟨185425139227899724536532643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123616759485266483024355095 185425139227899724536532643)
      ·
        refine ⟨278137708841849586804798965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185425139227899724536532643 278137708841849586804798965)
        ·
          refine ⟨26075410203923398762949903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 278137708841849586804798965 26075410203923398762949903)
          ·
            refine ⟨39113115305885098144424855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26075410203923398762949903 39113115305885098144424855)
            ·
              refine ⟨58669672958827647216637283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39113115305885098144424855 58669672958827647216637283)
              ·
                refine ⟨88004509438241470824955925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58669672958827647216637283 88004509438241470824955925)
                ·
                  refine ⟨4125211379917568944919809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88004509438241470824955925 4125211379917568944919809)
                  ·
                    refine ⟨3093908534938176708689857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4125211379917568944919809 3093908534938176708689857)
                    ·
                      refine ⟨2320431401203632531517393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093908534938176708689857 2320431401203632531517393)
                      ·
                        rfl

theorem cell23_4519024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 6, 2, 2].length) (baseStart_4519024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519024 prefixEnd_4519024 := by exact prefixLift 4519024
  have htrace : WordTrace (prefixWord ++ tailWord_4519024) baseStart_4519024 baseEnd_4519024 := by
    simpa [prefixWord, tailWord_4519024, baseEnd_4519024] using wordTrace_append hprefix tailTrace_4519024
  have hstable : (prefixWord ++ tailWord_4519024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519024).length < 2 ^ (prefixWord ++ tailWord_4519024).sum := by decide
  have hdescent : baseEnd_4519024 < baseStart_4519024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519041 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_4519041 : Nat := 118140960795 + 4519041 * 2 ^ 59
def prefixEnd_4519041 : Nat := 4983230072969 + 3 ^ 40 * 4519041 * 2
def baseEnd_4519041 : Nat := 2320440130374758965004815

theorem tailTrace_4519041 : CollatzResearch.WordTrace tailWord_4519041 prefixEnd_4519041 2320440130374758965004815 := by
  unfold tailWord_4519041
  simp only [CollatzResearch.WordTrace]
  refine ⟨164822966021293722602508977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109881977347529148401672651 164822966021293722602508977)
  ·
    refine ⟨123617224515970291951881733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164822966021293722602508977 123617224515970291951881733)
    ·
      refine ⟨23178229596744429740977825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123617224515970291951881733 23178229596744429740977825)
      ·
        refine ⟨17383672197558322305733369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23178229596744429740977825 17383672197558322305733369)
        ·
          refine ⟨13037754148168741729300027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17383672197558322305733369 13037754148168741729300027)
          ·
            refine ⟨19556631222253112593950041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13037754148168741729300027 19556631222253112593950041)
            ·
              refine ⟨14667473416689834445462531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19556631222253112593950041 14667473416689834445462531)
              ·
                refine ⟨22001210125034751668193797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14667473416689834445462531 22001210125034751668193797)
                ·
                  refine ⟨4125226898444015937786337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22001210125034751668193797 4125226898444015937786337)
                  ·
                    refine ⟨3093920173833011953339753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4125226898444015937786337 3093920173833011953339753)
                    ·
                      refine ⟨2320440130374758965004815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093920173833011953339753 2320440130374758965004815)
                      ·
                        rfl

theorem cell23_4519041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_4519041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519041 prefixEnd_4519041 := by exact prefixLift 4519041
  have htrace : WordTrace (prefixWord ++ tailWord_4519041) baseStart_4519041 baseEnd_4519041 := by
    simpa [prefixWord, tailWord_4519041, baseEnd_4519041] using wordTrace_append hprefix tailTrace_4519041
  have hstable : (prefixWord ++ tailWord_4519041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519041).length < 2 ^ (prefixWord ++ tailWord_4519041).sum := by decide
  have hdescent : baseEnd_4519041 < baseStart_4519041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519058 : List Nat := [3, 2, 3, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_4519058 : Nat := 118140960795 + 4519058 * 2 ^ 59
def prefixEnd_4519058 : Nat := 4983230072969 + 3 ^ 40 * 4519058 * 2
def baseEnd_4519058 : Nat := 2320448859545885398492237

theorem tailTrace_4519058 : CollatzResearch.WordTrace tailWord_4519058 prefixEnd_4519058 2320448859545885398492237 := by
  unfold tailWord_4519058
  simp only [CollatzResearch.WordTrace]
  refine ⟨41205896515558033626469457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109882390708154756337251885 41205896515558033626469457)
  ·
    refine ⟨30904422386668525219852093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41205896515558033626469457 30904422386668525219852093)
    ·
      refine ⟨11589158395000696957444535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30904422386668525219852093 11589158395000696957444535)
      ·
        refine ⟨17383737592501045436166803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11589158395000696957444535 17383737592501045436166803)
        ·
          refine ⟨26075606388751568154250205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17383737592501045436166803 26075606388751568154250205)
          ·
            refine ⟨9778352395781838057843827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26075606388751568154250205 9778352395781838057843827)
            ·
              refine ⟨14667528593672757086765741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9778352395781838057843827 14667528593672757086765741)
              ·
                refine ⟨5500323222627283907537153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14667528593672757086765741 5500323222627283907537153)
                ·
                  refine ⟨4125242416970462930652865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5500323222627283907537153 4125242416970462930652865)
                  ·
                    refine ⟨3093931812727847197989649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4125242416970462930652865 3093931812727847197989649)
                    ·
                      refine ⟨2320448859545885398492237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093931812727847197989649 2320448859545885398492237)
                      ·
                        rfl

theorem cell23_4519058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_4519058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519058 prefixEnd_4519058 := by exact prefixLift 4519058
  have htrace : WordTrace (prefixWord ++ tailWord_4519058) baseStart_4519058 baseEnd_4519058 := by
    simpa [prefixWord, tailWord_4519058, baseEnd_4519058] using wordTrace_append hprefix tailTrace_4519058
  have hstable : (prefixWord ++ tailWord_4519058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519058).length < 2 ^ (prefixWord ++ tailWord_4519058).sum := by decide
  have hdescent : baseEnd_4519058 < baseStart_4519058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519077 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 2, 5]
def baseStart_4519077 : Nat := 118140960795 + 4519077 * 2 ^ 59
def prefixEnd_4519077 : Nat := 4983230072969 + 3 ^ 40 * 4519077 * 2
def baseEnd_4519077 : Nat := 773486205226106941384883

theorem tailTrace_4519077 : CollatzResearch.WordTrace tailWord_4519077 prefixEnd_4519077 773486205226106941384883 := by
  unfold tailWord_4519077
  simp only [CollatzResearch.WordTrace]
  refine ⟨164824279049163300750819485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109882852699442200500546323 164824279049163300750819485)
  ·
    refine ⟨61809104643436237781557307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164824279049163300750819485 61809104643436237781557307)
    ·
      refine ⟨92713656965154356672335961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61809104643436237781557307 92713656965154356672335961)
      ·
        refine ⟨69535242723865767504251971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92713656965154356672335961 69535242723865767504251971)
        ·
          refine ⟨104302864085798651256377957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69535242723865767504251971 104302864085798651256377957)
          ·
            refine ⟨19556787016087247110570867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104302864085798651256377957 19556787016087247110570867)
            ·
              refine ⟨29335180524130870665856301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19556787016087247110570867 29335180524130870665856301)
              ·
                refine ⟨11000692696549076499696113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29335180524130870665856301 11000692696549076499696113)
                ·
                  refine ⟨8250519522411807374772085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11000692696549076499696113 8250519522411807374772085)
                  ·
                    refine ⟨773486205226106941384883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8250519522411807374772085 773486205226106941384883)
                    ·
                      rfl

theorem cell23_4519077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_4519077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519077 prefixEnd_4519077 := by exact prefixLift 4519077
  have htrace : WordTrace (prefixWord ++ tailWord_4519077) baseStart_4519077 baseEnd_4519077 := by
    simpa [prefixWord, tailWord_4519077, baseEnd_4519077] using wordTrace_append hprefix tailTrace_4519077
  have hstable : (prefixWord ++ tailWord_4519077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519077).length < 2 ^ (prefixWord ++ tailWord_4519077).sum := by decide
  have hdescent : baseEnd_4519077 < baseStart_4519077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519114 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 1, 6, 2]
def baseStart_4519114 : Nat := 118140960795 + 4519114 * 2 ^ 59
def prefixEnd_4519114 : Nat := 4983230072969 + 3 ^ 40 * 4519114 * 2
def baseEnd_4519114 : Nat := 2320477614462537179391979

theorem tailTrace_4519114 : CollatzResearch.WordTrace tailWord_4519114 prefixEnd_4519114 2320477614462537179391979 := by
  unfold tailWord_4519114
  simp only [CollatzResearch.WordTrace]
  refine ⟨41206407137507314017479099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109883752366686170713277597 41206407137507314017479099)
  ·
    refine ⟨61809610706260971026218649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41206407137507314017479099 61809610706260971026218649)
    ·
      refine ⟨46357208029695728269663987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61809610706260971026218649 46357208029695728269663987)
      ·
        refine ⟨69535812044543592404495981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46357208029695728269663987 69535812044543592404495981)
        ·
          refine ⟨26075929516703847151685993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69535812044543592404495981 26075929516703847151685993)
          ·
            refine ⟨19556947137527885363764495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26075929516703847151685993 19556947137527885363764495)
            ·
              refine ⟨29335420706291828045646743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19556947137527885363764495 29335420706291828045646743)
              ·
                refine ⟨44003131059437742068470115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29335420706291828045646743 44003131059437742068470115)
                ·
                  refine ⟨66004696589156613102705173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44003131059437742068470115 66004696589156613102705173)
                  ·
                    refine ⟨3093970152616716239189305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66004696589156613102705173 3093970152616716239189305)
                    ·
                      refine ⟨2320477614462537179391979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093970152616716239189305 2320477614462537179391979)
                      ·
                        rfl

theorem cell23_4519114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_4519114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519114 prefixEnd_4519114 := by exact prefixLift 4519114
  have htrace : WordTrace (prefixWord ++ tailWord_4519114) baseStart_4519114 baseEnd_4519114 := by
    simpa [prefixWord, tailWord_4519114, baseEnd_4519114] using wordTrace_append hprefix tailTrace_4519114
  have hstable : (prefixWord ++ tailWord_4519114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519114).length < 2 ^ (prefixWord ++ tailWord_4519114).sum := by decide
  have hdescent : baseEnd_4519114 < baseStart_4519114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519154 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 8]
def baseStart_4519154 : Nat := 118140960795 + 4519154 * 2 ^ 59
def prefixEnd_4519154 : Nat := 4983230072969 + 3 ^ 40 * 4519154 * 2
def baseEnd_4519154 : Nat := 257833128187635224765755

theorem tailTrace_4519154 : CollatzResearch.WordTrace tailWord_4519154 prefixEnd_4519154 257833128187635224765755 := by
  unfold tailWord_4519154
  simp only [CollatzResearch.WordTrace]
  refine ⟨41206771867471085725343129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109884724979922895267581677 41206771867471085725343129)
  ·
    refine ⟨30905078900603314294007347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41206771867471085725343129 30905078900603314294007347)
    ·
      refine ⟨46357618350904971441011021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30905078900603314294007347 46357618350904971441011021)
      ·
        refine ⟨17384106881589364290379133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46357618350904971441011021 17384106881589364290379133)
        ·
          refine ⟨6519040080596011608892175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17384106881589364290379133 6519040080596011608892175)
          ·
            refine ⟨9778560120894017413338263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6519040080596011608892175 9778560120894017413338263)
            ·
              refine ⟨14667840181341026120007395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9778560120894017413338263 14667840181341026120007395)
              ·
                refine ⟨22001760272011539180011093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14667840181341026120007395 22001760272011539180011093)
                ·
                  refine ⟨257833128187635224765755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22001760272011539180011093 257833128187635224765755)
                  ·
                    rfl

theorem cell23_4519154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_4519154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519154 prefixEnd_4519154 := by exact prefixLift 4519154
  have htrace : WordTrace (prefixWord ++ tailWord_4519154) baseStart_4519154 baseEnd_4519154 := by
    simpa [prefixWord, tailWord_4519154, baseEnd_4519154] using wordTrace_append hprefix tailTrace_4519154
  have hstable : (prefixWord ++ tailWord_4519154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519154).length < 2 ^ (prefixWord ++ tailWord_4519154).sum := by decide
  have hdescent : baseEnd_4519154 < baseStart_4519154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519191 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 2, 3, 2]
def baseStart_4519191 : Nat := 118140960795 + 4519191 * 2 ^ 59
def prefixEnd_4519191 : Nat := 4983230072969 + 3 ^ 40 * 4519191 * 2
def baseEnd_4519191 : Nat := 2320517152472933378129125

theorem tailTrace_4519191 : CollatzResearch.WordTrace tailWord_4519191 prefixEnd_4519191 2320517152472933378129125 := by
  unfold tailWord_4519191
  simp only [CollatzResearch.WordTrace]
  refine ⟨164828436970750298220469427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109885624647166865480312951 164828436970750298220469427)
  ·
    refine ⟨247242655456125447330704141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164828436970750298220469427 247242655456125447330704141)
    ·
      refine ⟨92715995796047042749014053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247242655456125447330704141 92715995796047042749014053)
      ·
        refine ⟨17384249211758820515440135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92715995796047042749014053 17384249211758820515440135)
        ·
          refine ⟨26076373817638230773160203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17384249211758820515440135 26076373817638230773160203)
          ·
            refine ⟨39114560726457346159740305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26076373817638230773160203 39114560726457346159740305)
            ·
              refine ⟨29335920544843009619805229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39114560726457346159740305 29335920544843009619805229)
              ·
                refine ⟨11000970204316128607426961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29335920544843009619805229 11000970204316128607426961)
                ·
                  refine ⟨8250727653237096455570221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11000970204316128607426961 8250727653237096455570221)
                  ·
                    refine ⟨3094022869963911170838833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8250727653237096455570221 3094022869963911170838833)
                    ·
                      refine ⟨2320517152472933378129125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094022869963911170838833 2320517152472933378129125)
                      ·
                        rfl

theorem cell23_4519191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_4519191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519191 prefixEnd_4519191 := by exact prefixLift 4519191
  have htrace : WordTrace (prefixWord ++ tailWord_4519191) baseStart_4519191 baseEnd_4519191 := by
    simpa [prefixWord, tailWord_4519191, baseEnd_4519191] using wordTrace_append hprefix tailTrace_4519191
  have hstable : (prefixWord ++ tailWord_4519191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519191).length < 2 ^ (prefixWord ++ tailWord_4519191).sum := by decide
  have hdescent : baseEnd_4519191 < baseStart_4519191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519208 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_4519208 : Nat := 118140960795 + 4519208 * 2 ^ 59
def prefixEnd_4519208 : Nat := 4983230072969 + 3 ^ 40 * 4519208 * 2
def baseEnd_4519208 : Nat := 2320525881644059811616547

theorem tailTrace_4519208 : CollatzResearch.WordTrace tailWord_4519208 prefixEnd_4519208 2320525881644059811616547 := by
  unfold tailWord_4519208
  simp only [CollatzResearch.WordTrace]
  refine ⟨82414528505844355061919139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109886038007792473415892185 82414528505844355061919139)
  ·
    refine ⟨123621792758766532592878709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82414528505844355061919139 123621792758766532592878709)
    ·
      refine ⟨11589543071134362430582379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123621792758766532592878709 11589543071134362430582379)
      ·
        refine ⟨17384314606701543645873569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11589543071134362430582379 17384314606701543645873569)
        ·
          refine ⟨13038235955026157734405177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17384314606701543645873569 13038235955026157734405177)
          ·
            refine ⟨9778676966269618300803883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13038235955026157734405177 9778676966269618300803883)
            ·
              refine ⟨14668015449404427451205825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9778676966269618300803883 14668015449404427451205825)
              ·
                refine ⟨11001011587053320588404369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14668015449404427451205825 11001011587053320588404369)
                ·
                  refine ⟨8250758690289990441303277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11001011587053320588404369 8250758690289990441303277)
                  ·
                    refine ⟨3094034508858746415488729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8250758690289990441303277 3094034508858746415488729)
                    ·
                      refine ⟨2320525881644059811616547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094034508858746415488729 2320525881644059811616547)
                      ·
                        rfl

theorem cell23_4519208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_4519208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519208 prefixEnd_4519208 := by exact prefixLift 4519208
  have htrace : WordTrace (prefixWord ++ tailWord_4519208) baseStart_4519208 baseEnd_4519208 := by
    simpa [prefixWord, tailWord_4519208, baseEnd_4519208] using wordTrace_append hprefix tailTrace_4519208
  have hstable : (prefixWord ++ tailWord_4519208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519208).length < 2 ^ (prefixWord ++ tailWord_4519208).sum := by decide
  have hdescent : baseEnd_4519208 < baseStart_4519208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519222 : List Nat := [5, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_4519222 : Nat := 118140960795 + 4519222 * 2 ^ 59
def prefixEnd_4519222 : Nat := 4983230072969 + 3 ^ 40 * 4519222 * 2
def baseEnd_4519222 : Nat := 257837007819246972982387

theorem tailTrace_4519222 : CollatzResearch.WordTrace tailWord_4519222 prefixEnd_4519222 257837007819246972982387 := by
  unfold tailWord_4519222
  simp only [CollatzResearch.WordTrace]
  refine ⟨10301847977102374407177995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109886378422425327009898613 10301847977102374407177995)
  ·
    refine ⟨15452771965653561610766993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10301847977102374407177995 15452771965653561610766993)
    ·
      refine ⟨11589578974240171208075245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15452771965653561610766993 11589578974240171208075245)
      ·
        refine ⟨4346092115340064203028217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11589578974240171208075245 4346092115340064203028217)
        ·
          refine ⟨3259569086505048152271163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4346092115340064203028217 3259569086505048152271163)
          ·
            refine ⟨4889353629757572228406745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3259569086505048152271163 4889353629757572228406745)
            ·
              refine ⟨3667015222318179171305059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4889353629757572228406745 3667015222318179171305059)
              ·
                refine ⟨5500522833477268756957589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3667015222318179171305059 5500522833477268756957589)
                ·
                  refine ⟨257837007819246972982387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5500522833477268756957589 257837007819246972982387)
                  ·
                    rfl

theorem cell23_4519222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_4519222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519222 prefixEnd_4519222 := by exact prefixLift 4519222
  have htrace : WordTrace (prefixWord ++ tailWord_4519222) baseStart_4519222 baseEnd_4519222 := by
    simpa [prefixWord, tailWord_4519222, baseEnd_4519222] using wordTrace_append hprefix tailTrace_4519222
  have hstable : (prefixWord ++ tailWord_4519222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519222).length < 2 ^ (prefixWord ++ tailWord_4519222).sum := by decide
  have hdescent : baseEnd_4519222 < baseStart_4519222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519224 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 3, 2, 3]
def baseStart_4519224 : Nat := 118140960795 + 4519224 * 2 ^ 59
def prefixEnd_4519224 : Nat := 4983230072969 + 3 ^ 40 * 4519224 * 2
def baseEnd_4519224 : Nat := 2320534097334531749016473

theorem tailTrace_4519224 : CollatzResearch.WordTrace tailWord_4519224 prefixEnd_4519224 2320534097334531749016473 := by
  unfold tailWord_4519224
  simp only [CollatzResearch.WordTrace]
  refine ⟨82414820289815372428210363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109886427053087163237613817 82414820289815372428210363)
  ·
    refine ⟨123622230434723058642315545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82414820289815372428210363 123622230434723058642315545)
    ·
      refine ⟨92716672826042293981736659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123622230434723058642315545 92716672826042293981736659)
      ·
        refine ⟨139075009239063440972604989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92716672826042293981736659 139075009239063440972604989)
        ·
          refine ⟨52153128464648790364726871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139075009239063440972604989 52153128464648790364726871)
          ·
            refine ⟨78229692696973185547090307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52153128464648790364726871 78229692696973185547090307)
            ·
              refine ⟨117344539045459778320635461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78229692696973185547090307 117344539045459778320635461)
              ·
                refine ⟨22002101071023708435119149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117344539045459778320635461 22002101071023708435119149)
                ·
                  refine ⟨8250787901633890663169681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22002101071023708435119149 8250787901633890663169681)
                  ·
                    refine ⟨6188090926225417997377261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8250787901633890663169681 6188090926225417997377261)
                    ·
                      refine ⟨2320534097334531749016473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6188090926225417997377261 2320534097334531749016473)
                      ·
                        rfl

theorem cell23_4519224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_4519224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519224 prefixEnd_4519224 := by exact prefixLift 4519224
  have htrace : WordTrace (prefixWord ++ tailWord_4519224) baseStart_4519224 baseEnd_4519224 := by
    simpa [prefixWord, tailWord_4519224, baseEnd_4519224] using wordTrace_append hprefix tailTrace_4519224
  have hstable : (prefixWord ++ tailWord_4519224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519224).length < 2 ^ (prefixWord ++ tailWord_4519224).sum := by decide
  have hdescent : baseEnd_4519224 < baseStart_4519224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519231 : List Nat := [1, 1, 2, 2, 4, 3, 1, 3, 2, 4]
def baseStart_4519231 : Nat := 118140960795 + 4519231 * 2 ^ 59
def prefixEnd_4519231 : Nat := 4983230072969 + 3 ^ 40 * 4519231 * 2
def baseEnd_4519231 : Nat := 773512563899704407209647

theorem tailTrace_4519231 : CollatzResearch.WordTrace tailWord_4519231 prefixEnd_4519231 773512563899704407209647 := by
  unfold tailWord_4519231
  simp only [CollatzResearch.WordTrace]
  refine ⟨164829895890605385051925547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109886597260403590034617031 164829895890605385051925547)
  ·
    refine ⟨247244843835908077577888321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164829895890605385051925547 247244843835908077577888321)
    ·
      refine ⟨185433632876931058183416241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247244843835908077577888321 185433632876931058183416241)
      ·
        refine ⟨139075224657698293637562181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185433632876931058183416241 139075224657698293637562181)
        ·
          refine ⟨26076604623318430057042909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139075224657698293637562181 26076604623318430057042909)
          ·
            refine ⟨9778726733744411271391091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26076604623318430057042909 9778726733744411271391091)
            ·
              refine ⟨14668090100616616907086637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9778726733744411271391091 14668090100616616907086637)
              ·
                refine ⟨5500533787731231340157489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14668090100616616907086637 5500533787731231340157489)
                ·
                  refine ⟨4125400340798423505118117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5500533787731231340157489 4125400340798423505118117)
                  ·
                    refine ⟨773512563899704407209647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4125400340798423505118117 773512563899704407209647)
                    ·
                      rfl

theorem cell23_4519231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 4].length) (baseStart_4519231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519231 prefixEnd_4519231 := by exact prefixLift 4519231
  have htrace : WordTrace (prefixWord ++ tailWord_4519231) baseStart_4519231 baseEnd_4519231 := by
    simpa [prefixWord, tailWord_4519231, baseEnd_4519231] using wordTrace_append hprefix tailTrace_4519231
  have hstable : (prefixWord ++ tailWord_4519231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519231).length < 2 ^ (prefixWord ++ tailWord_4519231).sum := by decide
  have hdescent : baseEnd_4519231 < baseStart_4519231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519241 : List Nat := [1, 2, 1, 1, 2, 3, 5, 2, 1, 2, 3]
def baseStart_4519241 : Nat := 118140960795 + 4519241 * 2 ^ 59
def prefixEnd_4519241 : Nat := 4983230072969 + 3 ^ 40 * 4519241 * 2
def baseEnd_4519241 : Nat := 2320542826505658182503895

theorem tailTrace_4519241 : CollatzResearch.WordTrace tailWord_4519241 prefixEnd_4519241 2320542826505658182503895 := by
  unfold tailWord_4519241
  simp only [CollatzResearch.WordTrace]
  refine ⟨164830260620569156759789577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109886840413712771173193051 164830260620569156759789577)
  ·
    refine ⟨123622695465426867569842183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164830260620569156759789577 123622695465426867569842183)
    ·
      refine ⟨185434043198140301354763275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123622695465426867569842183 185434043198140301354763275)
      ·
        refine ⟨278151064797210452032144913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185434043198140301354763275 278151064797210452032144913)
        ·
          refine ⟨208613298597907839024108685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278151064797210452032144913 208613298597907839024108685)
          ·
            refine ⟨78229986974215439634040757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208613298597907839024108685 78229986974215439634040757)
            ·
              refine ⟨7334061278832697465691321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78229986974215439634040757 7334061278832697465691321)
              ·
                refine ⟨5500545959124523099268491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7334061278832697465691321 5500545959124523099268491)
                ·
                  refine ⟨8250818938686784648902737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5500545959124523099268491 8250818938686784648902737)
                  ·
                    refine ⟨6188114204015088486677053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8250818938686784648902737 6188114204015088486677053)
                    ·
                      refine ⟨2320542826505658182503895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6188114204015088486677053 2320542826505658182503895)
                      ·
                        rfl

theorem cell23_4519241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 2, 3].length) (baseStart_4519241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519241 prefixEnd_4519241 := by exact prefixLift 4519241
  have htrace : WordTrace (prefixWord ++ tailWord_4519241) baseStart_4519241 baseEnd_4519241 := by
    simpa [prefixWord, tailWord_4519241, baseEnd_4519241] using wordTrace_append hprefix tailTrace_4519241
  have hstable : (prefixWord ++ tailWord_4519241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519241).length < 2 ^ (prefixWord ++ tailWord_4519241).sum := by decide
  have hdescent : baseEnd_4519241 < baseStart_4519241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519261 : List Nat := [1, 4, 5, 1, 12]
def baseStart_4519261 : Nat := 118140960795 + 4519261 * 2 ^ 59
def prefixEnd_4519261 : Nat := 4983230072969 + 3 ^ 40 * 4519261 * 2
def baseEnd_4519261 : Nat := 3183200406198557070307

theorem tailTrace_4519261 : CollatzResearch.WordTrace tailWord_4519261 prefixEnd_4519261 3183200406198557070307 := by
  unfold tailWord_4519261
  simp only [CollatzResearch.WordTrace]
  refine ⟨164830990080496700175517637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109887326720331133450345091 164830990080496700175517637)
  ·
    refine ⟨30905810640093131282909557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164830990080496700175517637 30905810640093131282909557)
    ·
      refine ⟨2897419747508731057772771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30905810640093131282909557 2897419747508731057772771)
      ·
        refine ⟨4346129621263096586659157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2897419747508731057772771 4346129621263096586659157)
        ·
          refine ⟨3183200406198557070307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4346129621263096586659157 3183200406198557070307)
          ·
            rfl

theorem cell23_4519261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 12].length) (baseStart_4519261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519261 prefixEnd_4519261 := by exact prefixLift 4519261
  have htrace : WordTrace (prefixWord ++ tailWord_4519261) baseStart_4519261 baseEnd_4519261 := by
    simpa [prefixWord, tailWord_4519261, baseEnd_4519261] using wordTrace_append hprefix tailTrace_4519261
  have hstable : (prefixWord ++ tailWord_4519261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519261).length < 2 ^ (prefixWord ++ tailWord_4519261).sum := by decide
  have hdescent : baseEnd_4519261 < baseStart_4519261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519272 : List Nat := [2, 1, 4, 2, 3, 1, 1, 4, 1, 2, 2]
def baseStart_4519272 : Nat := 118140960795 + 4519272 * 2 ^ 59
def prefixEnd_4519272 : Nat := 4983230072969 + 3 ^ 40 * 4519272 * 2
def baseEnd_4519272 : Nat := 2320558744405947561216253

theorem tailTrace_4519272 : CollatzResearch.WordTrace tailWord_4519272 prefixEnd_4519272 2320558744405947561216253 := by
  unfold tailWord_4519272
  simp only [CollatzResearch.WordTrace]
  refine ⟨82415695641728424527084035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109887594188971232702778713 82415695641728424527084035)
  ·
    refine ⟨123623543462592636790626053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82415695641728424527084035 123623543462592636790626053)
    ·
      refine ⟨23179414399236119398242385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123623543462592636790626053 23179414399236119398242385)
      ·
        refine ⟨17384560799427089548681789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23179414399236119398242385 17384560799427089548681789)
        ·
          refine ⟨6519210299785158580755671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17384560799427089548681789 6519210299785158580755671)
          ·
            refine ⟨9778815449677737871133507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6519210299785158580755671 9778815449677737871133507)
            ·
              refine ⟨14668223174516606806700261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9778815449677737871133507 14668223174516606806700261)
              ·
                refine ⟨2750291845221863776256299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14668223174516606806700261 2750291845221863776256299)
                ·
                  refine ⟨4125437767832795664384449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2750291845221863776256299 4125437767832795664384449)
                  ·
                    refine ⟨3094078325874596748288337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4125437767832795664384449 3094078325874596748288337)
                    ·
                      refine ⟨2320558744405947561216253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094078325874596748288337 2320558744405947561216253)
                      ·
                        rfl

theorem cell23_4519272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_4519272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519272 prefixEnd_4519272 := by exact prefixLift 4519272
  have htrace : WordTrace (prefixWord ++ tailWord_4519272) baseStart_4519272 baseEnd_4519272 := by
    simpa [prefixWord, tailWord_4519272, baseEnd_4519272] using wordTrace_append hprefix tailTrace_4519272
  have hstable : (prefixWord ++ tailWord_4519272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519272).length < 2 ^ (prefixWord ++ tailWord_4519272).sum := by decide
  have hdescent : baseEnd_4519272 < baseStart_4519272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519278 : List Nat := [4, 1, 2, 4, 1, 2, 1, 8]
def baseStart_4519278 : Nat := 118140960795 + 4519278 * 2 ^ 59
def prefixEnd_4519278 : Nat := 4983230072969 + 3 ^ 40 * 4519278 * 2
def baseEnd_4519278 : Nat := 85946734269995353249675

theorem tailTrace_4519278 : CollatzResearch.WordTrace tailWord_4519278 prefixEnd_4519278 85946734269995353249675 := by
  unfold tailWord_4519278
  simp only [CollatzResearch.WordTrace]
  refine ⟨20603951265179389009860811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109887740080956741385924325 20603951265179389009860811)
  ·
    refine ⟨30905926897769083514791217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20603951265179389009860811 30905926897769083514791217)
    ·
      refine ⟨23179445173326812636093413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30905926897769083514791217 23179445173326812636093413)
      ·
        refine ⟨4346145969998777369267515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23179445173326812636093413 4346145969998777369267515)
        ·
          refine ⟨6519218954998166053901273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4346145969998777369267515 6519218954998166053901273)
          ·
            refine ⟨4889414216248624540425955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6519218954998166053901273 4889414216248624540425955)
            ·
              refine ⟨7334121324372936810638933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4889414216248624540425955 7334121324372936810638933)
              ·
                refine ⟨85946734269995353249675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7334121324372936810638933 85946734269995353249675)
                ·
                  rfl

theorem cell23_4519278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_4519278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519278 prefixEnd_4519278 := by exact prefixLift 4519278
  have htrace : WordTrace (prefixWord ++ tailWord_4519278) baseStart_4519278 baseEnd_4519278 := by
    simpa [prefixWord, tailWord_4519278, baseEnd_4519278] using wordTrace_append hprefix tailTrace_4519278
  have hstable : (prefixWord ++ tailWord_4519278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519278).length < 2 ^ (prefixWord ++ tailWord_4519278).sum := by decide
  have hdescent : baseEnd_4519278 < baseStart_4519278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519281 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 3, 3, 2]
def baseStart_4519281 : Nat := 118140960795 + 4519281 * 2 ^ 59
def prefixEnd_4519281 : Nat := 4983230072969 + 3 ^ 40 * 4519281 * 2
def baseEnd_4519281 : Nat := 2320563365731838026003711

theorem tailTrace_4519281 : CollatzResearch.WordTrace tailWord_4519281 prefixEnd_4519281 2320563365731838026003711 := by
  unfold tailWord_4519281
  simp only [CollatzResearch.WordTrace]
  refine ⟨164831719540424243591245697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109887813026949495727497131 164831719540424243591245697)
  ·
    refine ⟨123623789655318182693434273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164831719540424243591245697 123623789655318182693434273)
    ·
      refine ⟨92717842241488637020075705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123623789655318182693434273 92717842241488637020075705)
      ·
        refine ⟨69538381681116477765056779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92717842241488637020075705 69538381681116477765056779)
        ·
          refine ⟨104307572521674716647585169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69538381681116477765056779 104307572521674716647585169)
          ·
            refine ⟨78230679391256037485688877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104307572521674716647585169 78230679391256037485688877)
            ·
              refine ⟨29336504771721014057133329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78230679391256037485688877 29336504771721014057133329)
              ·
                refine ⟨22002378578790760542849997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29336504771721014057133329 22002378578790760542849997)
                ·
                  refine ⟨8250891967046535203568749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22002378578790760542849997 8250891967046535203568749)
                  ·
                    refine ⟨3094084487642450701338281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8250891967046535203568749 3094084487642450701338281)
                    ·
                      refine ⟨2320563365731838026003711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094084487642450701338281 2320563365731838026003711)
                      ·
                        rfl

theorem cell23_4519281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_4519281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519281 prefixEnd_4519281 := by exact prefixLift 4519281
  have htrace : WordTrace (prefixWord ++ tailWord_4519281) baseStart_4519281 baseEnd_4519281 := by
    simpa [prefixWord, tailWord_4519281, baseEnd_4519281] using wordTrace_append hprefix tailTrace_4519281
  have hstable : (prefixWord ++ tailWord_4519281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519281).length < 2 ^ (prefixWord ++ tailWord_4519281).sum := by decide
  have hdescent : baseEnd_4519281 < baseStart_4519281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519328 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 4, 2, 2]
def baseStart_4519328 : Nat := 118140960795 + 4519328 * 2 ^ 59
def prefixEnd_4519328 : Nat := 4983230072969 + 3 ^ 40 * 4519328 * 2
def baseEnd_4519328 : Nat := 2320587499322599342115995

theorem tailTrace_4519328 : CollatzResearch.WordTrace tailWord_4519328 prefixEnd_4519328 2320587499322599342115995 := by
  unfold tailWord_4519328
  simp only [CollatzResearch.WordTrace]
  refine ⟨82416716885626985309103319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109888955847502647078804425 82416716885626985309103319)
  ·
    refine ⟨123625075328440477963654979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82416716885626985309103319 123625075328440477963654979)
    ·
      refine ⟨185437612992660716945482469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123625075328440477963654979 185437612992660716945482469)
      ·
        refine ⟨34769552436123884427277963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185437612992660716945482469 34769552436123884427277963)
        ·
          refine ⟨52154328654185826640916945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34769552436123884427277963 52154328654185826640916945)
          ·
            refine ⟨39115746490639369980687709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52154328654185826640916945 39115746490639369980687709)
            ·
              refine ⟨14668404933989763742757891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39115746490639369980687709 14668404933989763742757891)
              ·
                refine ⟨22002607400984645614136837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14668404933989763742757891 22002607400984645614136837)
                ·
                  refine ⟨4125488887684621052650657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22002607400984645614136837 4125488887684621052650657)
                  ·
                    refine ⟨3094116665763465789487993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4125488887684621052650657 3094116665763465789487993)
                    ·
                      refine ⟨2320587499322599342115995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094116665763465789487993 2320587499322599342115995)
                      ·
                        rfl

theorem cell23_4519328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_4519328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519328 prefixEnd_4519328 := by exact prefixLift 4519328
  have htrace : WordTrace (prefixWord ++ tailWord_4519328) baseStart_4519328 baseEnd_4519328 := by
    simpa [prefixWord, tailWord_4519328, baseEnd_4519328] using wordTrace_append hprefix tailTrace_4519328
  have hstable : (prefixWord ++ tailWord_4519328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519328).length < 2 ^ (prefixWord ++ tailWord_4519328).sum := by decide
  have hdescent : baseEnd_4519328 < baseStart_4519328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519344 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 3]
def baseStart_4519344 : Nat := 118140960795 + 4519344 * 2 ^ 59
def prefixEnd_4519344 : Nat := 4983230072969 + 3 ^ 40 * 4519344 * 2
def baseEnd_4519344 : Nat := 2320595715013071279515921

theorem tailTrace_4519344 : CollatzResearch.WordTrace tailWord_4519344 prefixEnd_4519344 2320595715013071279515921 := by
  unfold tailWord_4519344
  simp only [CollatzResearch.WordTrace]
  refine ⟨82417008669598002675394543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109889344892797336900526057 82417008669598002675394543)
  ·
    refine ⟨123625513004397004013091815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82417008669598002675394543 123625513004397004013091815)
    ·
      refine ⟨185438269506595506019637723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123625513004397004013091815 185438269506595506019637723)
      ·
        refine ⟨278157404259893259029456585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185438269506595506019637723 278157404259893259029456585)
        ·
          refine ⟨208618053194919944272092439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278157404259893259029456585 208618053194919944272092439)
          ·
            refine ⟨312927079792379916408138659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208618053194919944272092439 312927079792379916408138659)
            ·
              refine ⟨469390619688569874612207989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312927079792379916408138659 469390619688569874612207989)
              ·
                refine ⟨44005370595803425744894499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 469390619688569874612207989 44005370595803425744894499)
                ·
                  refine ⟨66008055893705138617341749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44005370595803425744894499 66008055893705138617341749)
                  ·
                    refine ⟨6188255240034856745375789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66008055893705138617341749 6188255240034856745375789)
                    ·
                      refine ⟨2320595715013071279515921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6188255240034856745375789 2320595715013071279515921)
                      ·
                        rfl

theorem cell23_4519344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 3].length) (baseStart_4519344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519344 prefixEnd_4519344 := by exact prefixLift 4519344
  have htrace : WordTrace (prefixWord ++ tailWord_4519344) baseStart_4519344 baseEnd_4519344 := by
    simpa [prefixWord, tailWord_4519344, baseEnd_4519344] using wordTrace_append hprefix tailTrace_4519344
  have hstable : (prefixWord ++ tailWord_4519344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519344).length < 2 ^ (prefixWord ++ tailWord_4519344).sum := by decide
  have hdescent : baseEnd_4519344 < baseStart_4519344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519381 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 2, 5]
def baseStart_4519381 : Nat := 118140960795 + 4519381 * 2 ^ 59
def prefixEnd_4519381 : Nat := 4983230072969 + 3 ^ 40 * 4519381 * 2
def baseEnd_4519381 : Nat := 773538237932429211584417

theorem tailTrace_4519381 : CollatzResearch.WordTrace tailWord_4519381 prefixEnd_4519381 773538237932429211584417 := by
  unfold tailWord_4519381
  simp only [CollatzResearch.WordTrace]
  refine ⟨164835366840061960669885997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109890244560041307113257331 164835366840061960669885997)
  ·
    refine ⟨61813262565023235251207249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164835366840061960669885997 61813262565023235251207249)
    ·
      refine ⟨46359946923767426438405437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61813262565023235251207249 46359946923767426438405437)
      ·
        refine ⟨17384980096412784914402039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46359946923767426438405437 17384980096412784914402039)
        ·
          refine ⟨26077470144619177371603059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17384980096412784914402039 26077470144619177371603059)
          ·
            refine ⟨39116205216928766057404589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26077470144619177371603059 39116205216928766057404589)
            ·
              refine ⟨14668576956348287271526721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39116205216928766057404589 14668576956348287271526721)
              ·
                refine ⟨11001432717261215453645041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14668576956348287271526721 11001432717261215453645041)
                ·
                  refine ⟨8251074537945911590233781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11001432717261215453645041 8251074537945911590233781)
                  ·
                    refine ⟨773538237932429211584417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8251074537945911590233781 773538237932429211584417)
                    ·
                      rfl

theorem cell23_4519381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_4519381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519381 prefixEnd_4519381 := by exact prefixLift 4519381
  have htrace : WordTrace (prefixWord ++ tailWord_4519381) baseStart_4519381 baseEnd_4519381 := by
    simpa [prefixWord, tailWord_4519381, baseEnd_4519381] using wordTrace_append hprefix tailTrace_4519381
  have hstable : (prefixWord ++ tailWord_4519381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519381).length < 2 ^ (prefixWord ++ tailWord_4519381).sum := by decide
  have hdescent : baseEnd_4519381 < baseStart_4519381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519401 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 6, 4, 2]
def baseStart_4519401 : Nat := 118140960795 + 4519401 * 2 ^ 59
def prefixEnd_4519401 : Nat := 4983230072969 + 3 ^ 40 * 4519401 * 2
def baseEnd_4519401 : Nat := 2320624983410377556503159

theorem tailTrace_4519401 : CollatzResearch.WordTrace tailWord_4519401 prefixEnd_4519401 2320624983410377556503159 := by
  unfold tailWord_4519401
  simp only [CollatzResearch.WordTrace]
  refine ⟨164836096299989504085614057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109890730866659669390409371 164836096299989504085614057)
  ·
    refine ⟨123627072224992128064210543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164836096299989504085614057 123627072224992128064210543)
    ·
      refine ⟨185440608337488192096315815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123627072224992128064210543 185440608337488192096315815)
      ·
        refine ⟨278160912506232288144473723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185440608337488192096315815 278160912506232288144473723)
        ·
          refine ⟨417241368759348432216710585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278160912506232288144473723 417241368759348432216710585)
          ·
            refine ⟨312931026569511324162532939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417241368759348432216710585 312931026569511324162532939)
            ·
              refine ⟨469396539854266986243799409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312931026569511324162532939 469396539854266986243799409)
              ·
                refine ⟨352047404890700239682849557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469396539854266986243799409 352047404890700239682849557)
                ·
                  refine ⟨16502222104251573735133573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 352047404890700239682849557 16502222104251573735133573)
                  ·
                    refine ⟨3094166644547170075337545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16502222104251573735133573 3094166644547170075337545)
                    ·
                      refine ⟨2320624983410377556503159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094166644547170075337545 2320624983410377556503159)
                      ·
                        rfl

theorem cell23_4519401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 4, 2].length) (baseStart_4519401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519401 prefixEnd_4519401 := by exact prefixLift 4519401
  have htrace : WordTrace (prefixWord ++ tailWord_4519401) baseStart_4519401 baseEnd_4519401 := by
    simpa [prefixWord, tailWord_4519401, baseEnd_4519401] using wordTrace_append hprefix tailTrace_4519401
  have hstable : (prefixWord ++ tailWord_4519401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519401).length < 2 ^ (prefixWord ++ tailWord_4519401).sum := by decide
  have hdescent : baseEnd_4519401 < baseStart_4519401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519441 : List Nat := [1, 2, 2, 1, 1, 2, 6, 2, 6]
def baseStart_4519441 : Nat := 118140960795 + 4519441 * 2 ^ 59
def prefixEnd_4519441 : Nat := 4983230072969 + 3 ^ 40 * 4519441 * 2
def baseEnd_4519441 : Nat := 257849502515173044444775

theorem tailTrace_4519441 : CollatzResearch.WordTrace tailWord_4519441 prefixEnd_4519441 257849502515173044444775 := by
  unfold tailWord_4519441
  simp only [CollatzResearch.WordTrace]
  refine ⟨164837555219844590917070177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109891703479896393944713451 164837555219844590917070177)
  ·
    refine ⟨123628166414883443187802633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164837555219844590917070177 123628166414883443187802633)
    ·
      refine ⟨92721124811162582390851975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123628166414883443187802633 92721124811162582390851975)
      ·
        refine ⟨139081687216743873586277963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92721124811162582390851975 139081687216743873586277963)
        ·
          refine ⟨208622530825115810379416945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139081687216743873586277963 208622530825115810379416945)
          ·
            refine ⟨156466898118836857784562709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208622530825115810379416945 156466898118836857784562709)
            ·
              refine ⟨7334385849320477708651377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 156466898118836857784562709 7334385849320477708651377)
              ·
                refine ⟨5500789386990358281488533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7334385849320477708651377 5500789386990358281488533)
                ·
                  refine ⟨257849502515173044444775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5500789386990358281488533 257849502515173044444775)
                  ·
                    rfl

theorem cell23_4519441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 6].length) (baseStart_4519441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519441 prefixEnd_4519441 := by exact prefixLift 4519441
  have htrace : WordTrace (prefixWord ++ tailWord_4519441) baseStart_4519441 baseEnd_4519441 := by
    simpa [prefixWord, tailWord_4519441, baseEnd_4519441] using wordTrace_append hprefix tailTrace_4519441
  have hstable : (prefixWord ++ tailWord_4519441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519441).length < 2 ^ (prefixWord ++ tailWord_4519441).sum := by decide
  have hdescent : baseEnd_4519441 < baseStart_4519441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519445 : List Nat := [1, 3, 2, 1, 3, 3, 1, 4, 1, 4]
def baseStart_4519445 : Nat := 118140960795 + 4519445 * 2 ^ 59
def prefixEnd_4519445 : Nat := 4983230072969 + 3 ^ 40 * 4519445 * 2
def baseEnd_4519445 : Nat := 773549192186391794784319

theorem tailTrace_4519445 : CollatzResearch.WordTrace tailWord_4519445 prefixEnd_4519445 773549192186391794784319 := by
  unfold tailWord_4519445
  simp only [CollatzResearch.WordTrace]
  refine ⟨164837701111830099600215789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109891800741220066400143859 164837701111830099600215789)
  ·
    refine ⟨61814137916936287350080921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164837701111830099600215789 61814137916936287350080921)
    ·
      refine ⟨46360603437702215512560691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61814137916936287350080921 46360603437702215512560691)
      ·
        refine ⟨69540905156553323268841037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46360603437702215512560691 69540905156553323268841037)
        ·
          refine ⟨26077839433707496225815389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69540905156553323268841037 26077839433707496225815389)
          ·
            refine ⟨9779189787640311084680771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26077839433707496225815389 9779189787640311084680771)
            ·
              refine ⟨14668784681460466627021157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9779189787640311084680771 14668784681460466627021157)
              ·
                refine ⟨2750397127773837492566467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14668784681460466627021157 2750397127773837492566467)
                ·
                  refine ⟨4125595691660756238849701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2750397127773837492566467 4125595691660756238849701)
                  ·
                    refine ⟨773549192186391794784319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4125595691660756238849701 773549192186391794784319)
                    ·
                      rfl

theorem cell23_4519445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_4519445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519445 prefixEnd_4519445 := by exact prefixLift 4519445
  have htrace : WordTrace (prefixWord ++ tailWord_4519445) baseStart_4519445 baseEnd_4519445 := by
    simpa [prefixWord, tailWord_4519445, baseEnd_4519445] using wordTrace_append hprefix tailTrace_4519445
  have hstable : (prefixWord ++ tailWord_4519445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519445).length < 2 ^ (prefixWord ++ tailWord_4519445).sum := by decide
  have hdescent : baseEnd_4519445 < baseStart_4519445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519511 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_4519511 : Nat := 118140960795 + 4519511 * 2 ^ 59
def prefixEnd_4519511 : Nat := 4983230072969 + 3 ^ 40 * 4519511 * 2
def baseEnd_4519511 : Nat := 2320681466282372126127653

theorem tailTrace_4519511 : CollatzResearch.WordTrace tailWord_4519511 prefixEnd_4519511 2320681466282372126127653 := by
  unfold tailWord_4519511
  simp only [CollatzResearch.WordTrace]
  refine ⟨164840108329590992872118387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109893405553060661914745591 164840108329590992872118387)
  ·
    refine ⟨247260162494386489308177581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164840108329590992872118387 247260162494386489308177581)
    ·
      refine ⟨92722560935394933490566593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247260162494386489308177581 92722560935394933490566593)
      ·
        refine ⟨69541920701546200117924945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92722560935394933490566593 69541920701546200117924945)
        ·
          refine ⟨52156440526159650088443709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69541920701546200117924945 52156440526159650088443709)
          ·
            refine ⟨19558665197309868783166391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52156440526159650088443709 19558665197309868783166391)
            ·
              refine ⟨29337997795964803174749587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19558665197309868783166391 29337997795964803174749587)
              ·
                refine ⟨44006996693947204762124381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29337997795964803174749587 44006996693947204762124381)
                ·
                  refine ⟨16502623760230201785796643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44006996693947204762124381 16502623760230201785796643)
                  ·
                    refine ⟨24753935640345302678694965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16502623760230201785796643 24753935640345302678694965)
                    ·
                      refine ⟨2320681466282372126127653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24753935640345302678694965 2320681466282372126127653)
                      ·
                        rfl

theorem cell23_4519511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_4519511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519511 prefixEnd_4519511 := by exact prefixLift 4519511
  have htrace : WordTrace (prefixWord ++ tailWord_4519511) baseStart_4519511 baseEnd_4519511 := by
    simpa [prefixWord, tailWord_4519511, baseEnd_4519511] using wordTrace_append hprefix tailTrace_4519511
  have hstable : (prefixWord ++ tailWord_4519511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519511).length < 2 ^ (prefixWord ++ tailWord_4519511).sum := by decide
  have hdescent : baseEnd_4519511 < baseStart_4519511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519521 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_4519521 : Nat := 118140960795 + 4519521 * 2 ^ 59
def prefixEnd_4519521 : Nat := 4983230072969 + 3 ^ 40 * 4519521 * 2
def baseEnd_4519521 : Nat := 2320686601088917087002607

theorem tailTrace_4519521 : CollatzResearch.WordTrace tailWord_4519521 prefixEnd_4519521 2320686601088917087002607 := by
  unfold tailWord_4519521
  simp only [CollatzResearch.WordTrace]
  refine ⟨164840473059554764579982417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109893648706369843053321611 164840473059554764579982417)
  ·
    refine ⟨123630354794666073434986813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164840473059554764579982417 123630354794666073434986813)
    ·
      refine ⟨46361383047999777538120055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123630354794666073434986813 46361383047999777538120055)
      ·
        refine ⟨69542074571999666307180083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46361383047999777538120055 69542074571999666307180083)
        ·
          refine ⟨104313111857999499460770125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69542074571999666307180083 104313111857999499460770125)
          ·
            refine ⟨39117416946749812297788797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104313111857999499460770125 39117416946749812297788797)
            ·
              refine ⟨14669031355031179611670799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39117416946749812297788797 14669031355031179611670799)
              ·
                refine ⟨22003547032546769417506199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14669031355031179611670799 22003547032546769417506199)
                ·
                  refine ⟨33005320548820154126259299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22003547032546769417506199 33005320548820154126259299)
                  ·
                    refine ⟨49507980823230231189388949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33005320548820154126259299 49507980823230231189388949)
                    ·
                      refine ⟨2320686601088917087002607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49507980823230231189388949 2320686601088917087002607)
                      ·
                        rfl

theorem cell23_4519521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_4519521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519521 prefixEnd_4519521 := by exact prefixLift 4519521
  have htrace : WordTrace (prefixWord ++ tailWord_4519521) baseStart_4519521 baseEnd_4519521 := by
    simpa [prefixWord, tailWord_4519521, baseEnd_4519521] using wordTrace_append hprefix tailTrace_4519521
  have hstable : (prefixWord ++ tailWord_4519521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519521).length < 2 ^ (prefixWord ++ tailWord_4519521).sum := by decide
  have hdescent : baseEnd_4519521 < baseStart_4519521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519525 : List Nat := [1, 3, 1, 3, 3, 2, 2, 2, 1, 1, 4]
def baseStart_4519525 : Nat := 118140960795 + 4519525 * 2 ^ 59
def prefixEnd_4519525 : Nat := 4983230072969 + 3 ^ 40 * 4519525 * 2
def baseEnd_4519525 : Nat := 2320688655011535071352589

theorem tailTrace_4519525 : CollatzResearch.WordTrace tailWord_4519525 prefixEnd_4519525 2320688655011535071352589 := by
  unfold tailWord_4519525
  simp only [CollatzResearch.WordTrace]
  refine ⟨164840618951540273263128029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109893745967693515508752019 164840618951540273263128029)
  ·
    refine ⟨61815232106827602473673011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164840618951540273263128029 61815232106827602473673011)
    ·
      refine ⟨92722848160241403710509517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61815232106827602473673011 92722848160241403710509517)
      ·
        refine ⟨34771068060090526391441069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92722848160241403710509517 34771068060090526391441069)
        ·
          refine ⟨13039150522533947396790401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34771068060090526391441069 13039150522533947396790401)
          ·
            refine ⟨9779362891900460547592801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13039150522533947396790401 9779362891900460547592801)
            ·
              refine ⟨7334522168925345410694601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9779362891900460547592801 7334522168925345410694601)
              ·
                refine ⟨5500891626694009058020951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7334522168925345410694601 5500891626694009058020951)
                ·
                  refine ⟨8251337440041013587031427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5500891626694009058020951 8251337440041013587031427)
                  ·
                    refine ⟨12377006160061520380547141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8251337440041013587031427 12377006160061520380547141)
                    ·
                      refine ⟨2320688655011535071352589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12377006160061520380547141 2320688655011535071352589)
                      ·
                        rfl

theorem cell23_4519525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_4519525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519525 prefixEnd_4519525 := by exact prefixLift 4519525
  have htrace : WordTrace (prefixWord ++ tailWord_4519525) baseStart_4519525 baseEnd_4519525 := by
    simpa [prefixWord, tailWord_4519525, baseEnd_4519525] using wordTrace_append hprefix tailTrace_4519525
  have hstable : (prefixWord ++ tailWord_4519525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519525).length < 2 ^ (prefixWord ++ tailWord_4519525).sum := by decide
  have hdescent : baseEnd_4519525 < baseStart_4519525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519581 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_4519581 : Nat := 118140960795 + 4519581 * 2 ^ 59
def prefixEnd_4519581 : Nat := 4983230072969 + 3 ^ 40 * 4519581 * 2
def baseEnd_4519581 : Nat := 2320717409928186852252331

theorem tailTrace_4519581 : CollatzResearch.WordTrace tailWord_4519581 prefixEnd_4519581 2320717409928186852252331 := by
  unfold tailWord_4519581
  simp only [CollatzResearch.WordTrace]
  refine ⟨164842661439337394827166597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109895107626224929884777731 164842661439337394827166597)
  ·
    refine ⟨30907999019875761530093737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164842661439337394827166597 30907999019875761530093737)
    ·
      refine ⟨23180999264906821147570303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30907999019875761530093737 23180999264906821147570303)
      ·
        refine ⟨34771498897360231721355455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23180999264906821147570303 34771498897360231721355455)
        ·
          refine ⟨52157248346040347582033183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34771498897360231721355455 52157248346040347582033183)
          ·
            refine ⟨78235872519060521373049775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52157248346040347582033183 78235872519060521373049775)
            ·
              refine ⟨117353808778590782059574663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78235872519060521373049775 117353808778590782059574663)
              ·
                refine ⟨176030713167886173089361995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117353808778590782059574663 176030713167886173089361995)
                ·
                  refine ⟨264046069751829259634042993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176030713167886173089361995 264046069751829259634042993)
                  ·
                    refine ⟨198034552313871944725532245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 264046069751829259634042993 198034552313871944725532245)
                    ·
                      refine ⟨2320717409928186852252331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 198034552313871944725532245 2320717409928186852252331)
                      ·
                        rfl

theorem cell23_4519581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_4519581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519581 prefixEnd_4519581 := by exact prefixLift 4519581
  have htrace : WordTrace (prefixWord ++ tailWord_4519581) baseStart_4519581 baseEnd_4519581 := by
    simpa [prefixWord, tailWord_4519581, baseEnd_4519581] using wordTrace_append hprefix tailTrace_4519581
  have hstable : (prefixWord ++ tailWord_4519581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519581).length < 2 ^ (prefixWord ++ tailWord_4519581).sum := by decide
  have hdescent : baseEnd_4519581 < baseStart_4519581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519611 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 4]
def baseStart_4519611 : Nat := 118140960795 + 4519611 * 2 ^ 59
def prefixEnd_4519611 : Nat := 4983230072969 + 3 ^ 40 * 4519611 * 2
def baseEnd_4519611 : Nat := 2320732814347821734877193

theorem tailTrace_4519611 : CollatzResearch.WordTrace tailWord_4519611 prefixEnd_4519611 2320732814347821734877193 := by
  unfold tailWord_4519611
  simp only [CollatzResearch.WordTrace]
  refine ⟨164843755629228709950758687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109895837086152473300505791 164843755629228709950758687)
  ·
    refine ⟨247265633443843064926138031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164843755629228709950758687 247265633443843064926138031)
    ·
      refine ⟨370898450165764597389207047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247265633443843064926138031 370898450165764597389207047)
      ·
        refine ⟨556347675248646896083810571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370898450165764597389207047 556347675248646896083810571)
        ·
          refine ⟨834521512872970344125715857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556347675248646896083810571 834521512872970344125715857)
          ·
            refine ⟨625891134654727758094286893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 834521512872970344125715857 625891134654727758094286893)
            ·
              refine ⟨234709175495522909285357585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 625891134654727758094286893 234709175495522909285357585)
              ·
                refine ⟨176031881621642181964018189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234709175495522909285357585 176031881621642181964018189)
                ·
                  refine ⟨66011955608115818236506821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176031881621642181964018189 66011955608115818236506821)
                  ·
                    refine ⟨12377241676521715919345029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66011955608115818236506821 12377241676521715919345029)
                    ·
                      refine ⟨2320732814347821734877193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12377241676521715919345029 2320732814347821734877193)
                      ·
                        rfl

theorem cell23_4519611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 4].length) (baseStart_4519611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519611 prefixEnd_4519611 := by exact prefixLift 4519611
  have htrace : WordTrace (prefixWord ++ tailWord_4519611) baseStart_4519611 baseEnd_4519611 := by
    simpa [prefixWord, tailWord_4519611, baseEnd_4519611] using wordTrace_append hprefix tailTrace_4519611
  have hstable : (prefixWord ++ tailWord_4519611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519611).length < 2 ^ (prefixWord ++ tailWord_4519611).sum := by decide
  have hdescent : baseEnd_4519611 < baseStart_4519611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519688 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_4519688 : Nat := 118140960795 + 4519688 * 2 ^ 59
def prefixEnd_4519688 : Nat := 4983230072969 + 3 ^ 40 * 4519688 * 2
def baseEnd_4519688 : Nat := 2320772352358217933614339

theorem tailTrace_4519688 : CollatzResearch.WordTrace tailWord_4519688 prefixEnd_4519688 2320772352358217933614339 := by
  unfold tailWord_4519688
  simp only [CollatzResearch.WordTrace]
  refine ⟨82423282024974876050655859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109897709366633168067541145 82423282024974876050655859)
  ·
    refine ⟨123634923037462314075983789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82423282024974876050655859 123634923037462314075983789)
    ·
      refine ⟨46363096139048367778493921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123634923037462314075983789 46363096139048367778493921)
      ·
        refine ⟨34772322104286275833870441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46363096139048367778493921 34772322104286275833870441)
        ·
          refine ⟨26079241578214706875402831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34772322104286275833870441 26079241578214706875402831)
          ·
            refine ⟨39118862367322060313104247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26079241578214706875402831 39118862367322060313104247)
            ·
              refine ⟨58678293550983090469656371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39118862367322060313104247 58678293550983090469656371)
              ·
                refine ⟨88017440326474635704484557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58678293550983090469656371 88017440326474635704484557)
                ·
                  refine ⟨33006540122427988389181709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88017440326474635704484557 33006540122427988389181709)
                  ·
                    refine ⟨12377452545910495645943141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33006540122427988389181709 12377452545910495645943141)
                    ·
                      refine ⟨2320772352358217933614339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12377452545910495645943141 2320772352358217933614339)
                      ·
                        rfl

theorem cell23_4519688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_4519688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519688 prefixEnd_4519688 := by exact prefixLift 4519688
  have htrace : WordTrace (prefixWord ++ tailWord_4519688) baseStart_4519688 baseEnd_4519688 := by
    simpa [prefixWord, tailWord_4519688, baseEnd_4519688] using wordTrace_append hprefix tailTrace_4519688
  have hstable : (prefixWord ++ tailWord_4519688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519688).length < 2 ^ (prefixWord ++ tailWord_4519688).sum := by decide
  have hdescent : baseEnd_4519688 < baseStart_4519688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519795 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 2, 6, 2]
def baseStart_4519795 : Nat := 118140960795 + 4519795 * 2 ^ 59
def prefixEnd_4519795 : Nat := 4983230072969 + 3 ^ 40 * 4519795 * 2
def baseEnd_4519795 : Nat := 2320827294788249014976347

theorem tailTrace_4519795 : CollatzResearch.WordTrace tailWord_4519795 prefixEnd_4519795 2320827294788249014976347 := by
  unfold tailWord_4519795
  simp only [CollatzResearch.WordTrace]
  refine ⟨164850466660562109375456839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109900311107041406250304559 164850466660562109375456839)
  ·
    refine ⟨247275699990843164063185259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164850466660562109375456839 247275699990843164063185259)
    ·
      refine ⟨370913549986264746094777889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247275699990843164063185259 370913549986264746094777889)
      ·
        refine ⟨278185162489698559571083417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370913549986264746094777889 278185162489698559571083417)
        ·
          refine ⟨208638871867273919678312563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278185162489698559571083417 208638871867273919678312563)
          ·
            refine ⟨312958307800910879517468845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208638871867273919678312563 312958307800910879517468845)
            ·
              refine ⟨117359365425341579819050817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 312958307800910879517468845 117359365425341579819050817)
              ·
                refine ⟨88019524069006184864288113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117359365425341579819050817 88019524069006184864288113)
                ·
                  refine ⟨66014643051754638648216085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88019524069006184864288113 66014643051754638648216085)
                  ·
                    refine ⟨3094436393050998686635129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66014643051754638648216085 3094436393050998686635129)
                    ·
                      refine ⟨2320827294788249014976347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094436393050998686635129 2320827294788249014976347)
                      ·
                        rfl

theorem cell23_4519795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 6, 2].length) (baseStart_4519795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519795 prefixEnd_4519795 := by exact prefixLift 4519795
  have htrace : WordTrace (prefixWord ++ tailWord_4519795) baseStart_4519795 baseEnd_4519795 := by
    simpa [prefixWord, tailWord_4519795, baseEnd_4519795] using wordTrace_append hprefix tailTrace_4519795
  have hstable : (prefixWord ++ tailWord_4519795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519795).length < 2 ^ (prefixWord ++ tailWord_4519795).sum := by decide
  have hdescent : baseEnd_4519795 < baseStart_4519795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519805 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_4519805 : Nat := 118140960795 + 4519805 * 2 ^ 59
def prefixEnd_4519805 : Nat := 4983230072969 + 3 ^ 40 * 4519805 * 2
def baseEnd_4519805 : Nat := 773610809864931325283767

theorem tailTrace_4519805 : CollatzResearch.WordTrace tailWord_4519805 prefixEnd_4519805 773610809864931325283767 := by
  unfold tailWord_4519805
  simp only [CollatzResearch.WordTrace]
  refine ⟨164850831390525881083320869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109900554260350587388880579 164850831390525881083320869)
  ·
    refine ⟨30909530885723602703122663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164850831390525881083320869 30909530885723602703122663)
    ·
      refine ⟨46364296328585404054683995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30909530885723602703122663 46364296328585404054683995)
      ·
        refine ⟨69546444492878106082025993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46364296328585404054683995 69546444492878106082025993)
        ·
          refine ⟨52159833369658579561519495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69546444492878106082025993 52159833369658579561519495)
          ·
            refine ⟨78239750054487869342279243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52159833369658579561519495 78239750054487869342279243)
            ·
              refine ⟨117359625081731804013418865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78239750054487869342279243 117359625081731804013418865)
              ·
                refine ⟨88019718811298853010064149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117359625081731804013418865 88019718811298853010064149)
                ·
                  refine ⟨4125924319279633734846757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88019718811298853010064149 4125924319279633734846757)
                  ·
                    refine ⟨773610809864931325283767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4125924319279633734846757 773610809864931325283767)
                    ·
                      rfl

theorem cell23_4519805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_4519805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519805 prefixEnd_4519805 := by exact prefixLift 4519805
  have htrace : WordTrace (prefixWord ++ tailWord_4519805) baseStart_4519805 baseEnd_4519805 := by
    simpa [prefixWord, tailWord_4519805, baseEnd_4519805] using wordTrace_append hprefix tailTrace_4519805
  have hstable : (prefixWord ++ tailWord_4519805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519805).length < 2 ^ (prefixWord ++ tailWord_4519805).sum := by decide
  have hdescent : baseEnd_4519805 < baseStart_4519805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519806 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_4519806 : Nat := 118140960795 + 4519806 * 2 ^ 59
def prefixEnd_4519806 : Nat := 4983230072969 + 3 ^ 40 * 4519806 * 2
def baseEnd_4519806 : Nat := 2320832943075448471938797

theorem tailTrace_4519806 : CollatzResearch.WordTrace tailWord_4519806 prefixEnd_4519806 2320832943075448471938797 := by
  unfold tailWord_4519806
  simp only [CollatzResearch.WordTrace]
  refine ⟨20606358482940282281763409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109900578575681505502738181 20606358482940282281763409)
  ·
    refine ⟨15454768862205211711322557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20606358482940282281763409 15454768862205211711322557)
    ·
      refine ⟨5795538323326954391745959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15454768862205211711322557 5795538323326954391745959)
      ·
        refine ⟨8693307484990431587618939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5795538323326954391745959 8693307484990431587618939)
        ·
          refine ⟨13039961227485647381428409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8693307484990431587618939 13039961227485647381428409)
          ·
            refine ⟨9779970920614235536071307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13039961227485647381428409 9779970920614235536071307)
            ·
              refine ⟨14669956380921353304106961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9779970920614235536071307 14669956380921353304106961)
              ·
                refine ⟨11002467285691014978080221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14669956380921353304106961 11002467285691014978080221)
                ·
                  refine ⟨4125925232134130616780083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11002467285691014978080221 4125925232134130616780083)
                  ·
                    refine ⟨6188887848201195925170125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4125925232134130616780083 6188887848201195925170125)
                    ·
                      refine ⟨2320832943075448471938797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6188887848201195925170125 2320832943075448471938797)
                      ·
                        rfl

theorem cell23_4519806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_4519806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519806 prefixEnd_4519806 := by exact prefixLift 4519806
  have htrace : WordTrace (prefixWord ++ tailWord_4519806) baseStart_4519806 baseEnd_4519806 := by
    simpa [prefixWord, tailWord_4519806, baseEnd_4519806] using wordTrace_append hprefix tailTrace_4519806
  have hstable : (prefixWord ++ tailWord_4519806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519806).length < 2 ^ (prefixWord ++ tailWord_4519806).sum := by decide
  have hdescent : baseEnd_4519806 < baseStart_4519806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519816 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 2, 3, 2]
def baseStart_4519816 : Nat := 118140960795 + 4519816 * 2 ^ 59
def prefixEnd_4519816 : Nat := 4983230072969 + 3 ^ 40 * 4519816 * 2
def baseEnd_4519816 : Nat := 2320838077881993432813751

theorem tailTrace_4519816 : CollatzResearch.WordTrace tailWord_4519816 prefixEnd_4519816 2320838077881993432813751 := by
  unfold tailWord_4519816
  simp only [CollatzResearch.WordTrace]
  refine ⟨82425616296743014980985651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109900821728990686641314201 82425616296743014980985651)
  ·
    refine ⟨123638424445114522471478477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82425616296743014980985651 123638424445114522471478477)
    ·
      refine ⟨46364409166917945926804429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123638424445114522471478477 46364409166917945926804429)
      ·
        refine ⟨17386653437594229722551661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46364409166917945926804429 17386653437594229722551661)
        ·
          refine ⟨6519995039097836145956873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17386653437594229722551661 6519995039097836145956873)
          ·
            refine ⟨4889996279323377109467655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6519995039097836145956873 4889996279323377109467655)
            ·
              refine ⟨7334994418985065664201483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4889996279323377109467655 7334994418985065664201483)
              ·
                refine ⟨11002491628477598496302225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7334994418985065664201483 11002491628477598496302225)
                ·
                  refine ⟨8251868721358198872226669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11002491628477598496302225 8251868721358198872226669)
                  ·
                    refine ⟨3094450770509324577085001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8251868721358198872226669 3094450770509324577085001)
                    ·
                      refine ⟨2320838077881993432813751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094450770509324577085001 2320838077881993432813751)
                      ·
                        rfl

theorem cell23_4519816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_4519816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519816 prefixEnd_4519816 := by exact prefixLift 4519816
  have htrace : WordTrace (prefixWord ++ tailWord_4519816) baseStart_4519816 baseEnd_4519816 := by
    simpa [prefixWord, tailWord_4519816, baseEnd_4519816] using wordTrace_append hprefix tailTrace_4519816
  have hstable : (prefixWord ++ tailWord_4519816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519816).length < 2 ^ (prefixWord ++ tailWord_4519816).sum := by decide
  have hdescent : baseEnd_4519816 < baseStart_4519816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519825 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 4]
def baseStart_4519825 : Nat := 118140960795 + 4519825 * 2 ^ 59
def prefixEnd_4519825 : Nat := 4983230072969 + 3 ^ 40 * 4519825 * 2
def baseEnd_4519825 : Nat := 2320842699207883897601209

theorem tailTrace_4519825 : CollatzResearch.WordTrace tailWord_4519825 prefixEnd_4519825 2320842699207883897601209 := by
  unfold tailWord_4519825
  simp only [CollatzResearch.WordTrace]
  refine ⟨164851560850453424499048929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109901040566968949666032619 164851560850453424499048929)
  ·
    refine ⟨123638670637840068374286697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164851560850453424499048929 123638670637840068374286697)
    ·
      refine ⟨92729002978380051280715023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123638670637840068374286697 92729002978380051280715023)
      ·
        refine ⟨139093504467570076921072535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92729002978380051280715023 139093504467570076921072535)
        ·
          refine ⟨208640256701355115381608803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139093504467570076921072535 208640256701355115381608803)
          ·
            refine ⟨312960385052032673072413205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208640256701355115381608803 312960385052032673072413205)
            ·
              refine ⟨14670018049314031550269369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 312960385052032673072413205 14670018049314031550269369)
              ·
                refine ⟨11002513536985523662702027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14670018049314031550269369 11002513536985523662702027)
                ·
                  refine ⟨16503770305478285494053041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11002513536985523662702027 16503770305478285494053041)
                  ·
                    refine ⟨12377827729108714120539781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16503770305478285494053041 12377827729108714120539781)
                    ·
                      refine ⟨2320842699207883897601209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12377827729108714120539781 2320842699207883897601209)
                      ·
                        rfl

theorem cell23_4519825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_4519825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519825 prefixEnd_4519825 := by exact prefixLift 4519825
  have htrace : WordTrace (prefixWord ++ tailWord_4519825) baseStart_4519825 baseEnd_4519825 := by
    simpa [prefixWord, tailWord_4519825, baseEnd_4519825] using wordTrace_append hprefix tailTrace_4519825
  have hstable : (prefixWord ++ tailWord_4519825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519825).length < 2 ^ (prefixWord ++ tailWord_4519825).sum := by decide
  have hdescent : baseEnd_4519825 < baseStart_4519825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519826 : List Nat := [3, 2, 3, 2, 1, 3, 2, 1, 1, 5]
def baseStart_4519826 : Nat := 118140960795 + 4519826 * 2 ^ 59
def prefixEnd_4519826 : Nat := 4983230072969 + 3 ^ 40 * 4519826 * 2
def baseEnd_4519826 : Nat := 773614404229512797896235

theorem tailTrace_4519826 : CollatzResearch.WordTrace tailWord_4519826 prefixEnd_4519826 773614404229512797896235 := by
  unfold tailWord_4519826
  simp only [CollatzResearch.WordTrace]
  refine ⟨41212899330862450417458833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109901064882299867779890221 41212899330862450417458833)
  ·
    refine ⟨30909674498146837813094125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41212899330862450417458833 30909674498146837813094125)
    ·
      refine ⟨11591127936805064179910297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30909674498146837813094125 11591127936805064179910297)
      ·
        refine ⟨8693345952603798134932723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11591127936805064179910297 8693345952603798134932723)
        ·
          refine ⟨13040018928905697202399085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8693345952603798134932723 13040018928905697202399085)
          ·
            refine ⟨4890007098339636450899657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13040018928905697202399085 4890007098339636450899657)
            ·
              refine ⟨3667505323754727338174743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4890007098339636450899657 3667505323754727338174743)
              ·
                refine ⟨5501257985632091007262115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3667505323754727338174743 5501257985632091007262115)
                ·
                  refine ⟨8251886978448136510893173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5501257985632091007262115 8251886978448136510893173)
                  ·
                    refine ⟨773614404229512797896235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8251886978448136510893173 773614404229512797896235)
                    ·
                      rfl

theorem cell23_4519826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_4519826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519826 prefixEnd_4519826 := by exact prefixLift 4519826
  have htrace : WordTrace (prefixWord ++ tailWord_4519826) baseStart_4519826 baseEnd_4519826 := by
    simpa [prefixWord, tailWord_4519826, baseEnd_4519826] using wordTrace_append hprefix tailTrace_4519826
  have hstable : (prefixWord ++ tailWord_4519826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519826).length < 2 ^ (prefixWord ++ tailWord_4519826).sum := by decide
  have hdescent : baseEnd_4519826 < baseStart_4519826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519845 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 3, 3, 3]
def baseStart_4519845 : Nat := 118140960795 + 4519845 * 2 ^ 59
def prefixEnd_4519845 : Nat := 4983230072969 + 3 ^ 40 * 4519845 * 2
def baseEnd_4519845 : Nat := 2320852968820973819351117

theorem tailTrace_4519845 : CollatzResearch.WordTrace tailWord_4519845 prefixEnd_4519845 2320852968820973819351117 := by
  unfold tailWord_4519845
  simp only [CollatzResearch.WordTrace]
  refine ⟨164852290310380967914776989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109901526873587311943184659 164852290310380967914776989)
  ·
    refine ⟨61819608866392862968041371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164852290310380967914776989 61819608866392862968041371)
    ·
      refine ⟨92729413299589294452062057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61819608866392862968041371 92729413299589294452062057)
      ·
        refine ⟨69547059974691970839046543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92729413299589294452062057 69547059974691970839046543)
        ·
          refine ⟨104320589962037956258569815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69547059974691970839046543 104320589962037956258569815)
          ·
            refine ⟨156480884943056934387854723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104320589962037956258569815 156480884943056934387854723)
            ·
              refine ⟨234721327414585401581782085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156480884943056934387854723 234721327414585401581782085)
              ·
                refine ⟨44010248890234762796584141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234721327414585401581782085 44010248890234762796584141)
                ·
                  refine ⟨16503843333838036048719053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44010248890234762796584141 16503843333838036048719053)
                  ·
                    refine ⟨6188941250189263518269645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16503843333838036048719053 6188941250189263518269645)
                    ·
                      refine ⟨2320852968820973819351117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6188941250189263518269645 2320852968820973819351117)
                      ·
                        rfl

theorem cell23_4519845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_4519845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519845 prefixEnd_4519845 := by exact prefixLift 4519845
  have htrace : WordTrace (prefixWord ++ tailWord_4519845) baseStart_4519845 baseEnd_4519845 := by
    simpa [prefixWord, tailWord_4519845, baseEnd_4519845] using wordTrace_append hprefix tailTrace_4519845
  have hstable : (prefixWord ++ tailWord_4519845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519845).length < 2 ^ (prefixWord ++ tailWord_4519845).sum := by decide
  have hdescent : baseEnd_4519845 < baseStart_4519845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519915 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 4]
def baseStart_4519915 : Nat := 118140960795 + 4519915 * 2 ^ 59
def prefixEnd_4519915 : Nat := 4983230072969 + 3 ^ 40 * 4519915 * 2
def baseEnd_4519915 : Nat := 2320888912466788545475795

theorem tailTrace_4519915 : CollatzResearch.WordTrace tailWord_4519915 prefixEnd_4519915 2320888912466788545475795 := by
  unfold tailWord_4519915
  simp only [CollatzResearch.WordTrace]
  refine ⟨164854843420127369869825199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109903228946751579913216799 164854843420127369869825199)
  ·
    refine ⟨247282265130191054804737799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164854843420127369869825199 247282265130191054804737799)
    ·
      refine ⟨370923397695286582207106699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247282265130191054804737799 370923397695286582207106699)
      ·
        refine ⟨556385096542929873310660049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370923397695286582207106699 556385096542929873310660049)
        ·
          refine ⟨417288822407197404982995037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 556385096542929873310660049 417288822407197404982995037)
          ·
            refine ⟨156483308402699026868623139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 417288822407197404982995037 156483308402699026868623139)
            ·
              refine ⟨234724962604048540302934709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156483308402699026868623139 234724962604048540302934709)
              ·
                refine ⟨22005465244129550653400129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 234724962604048540302934709 22005465244129550653400129)
                ·
                  refine ⟨16504098933097162990050097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22005465244129550653400129 16504098933097162990050097)
                  ·
                    refine ⟨12378074199822872242537573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16504098933097162990050097 12378074199822872242537573)
                    ·
                      refine ⟨2320888912466788545475795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12378074199822872242537573 2320888912466788545475795)
                      ·
                        rfl

theorem cell23_4519915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 4].length) (baseStart_4519915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519915 prefixEnd_4519915 := by exact prefixLift 4519915
  have htrace : WordTrace (prefixWord ++ tailWord_4519915) baseStart_4519915 baseEnd_4519915 := by
    simpa [prefixWord, tailWord_4519915, baseEnd_4519915] using wordTrace_append hprefix tailTrace_4519915
  have hstable : (prefixWord ++ tailWord_4519915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519915).length < 2 ^ (prefixWord ++ tailWord_4519915).sum := by decide
  have hdescent : baseEnd_4519915 < baseStart_4519915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519940 : List Nat := [2, 3, 2, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4519940 : Nat := 118140960795 + 4519940 * 2 ^ 59
def prefixEnd_4519940 : Nat := 4983230072969 + 3 ^ 40 * 4519940 * 2
def baseEnd_4519940 : Nat := 2320901749483150947663181

theorem tailTrace_4519940 : CollatzResearch.WordTrace tailWord_4519940 prefixEnd_4519940 2320901749483150947663181 := by
  unfold tailWord_4519940
  simp only [CollatzResearch.WordTrace]
  refine ⟨82427877622518399569742637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109903836830024532759656849 82427877622518399569742637)
  ·
    refine ⟨30910454108444399838653489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82427877622518399569742637 30910454108444399838653489)
    ·
      refine ⟨23182840581333299878990117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30910454108444399838653489 23182840581333299878990117)
      ·
        refine ⟨4346782608999993727310647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23182840581333299878990117 4346782608999993727310647)
        ·
          refine ⟨6520173913499990590965971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4346782608999993727310647 6520173913499990590965971)
          ·
            refine ⟨9780260870249985886448957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6520173913499990590965971 9780260870249985886448957)
            ·
              refine ⟨3667597826343744707418359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9780260870249985886448957 3667597826343744707418359)
              ·
                refine ⟨5501396739515617061127539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3667597826343744707418359 5501396739515617061127539)
                ·
                  refine ⟨8252095109273425591691309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5501396739515617061127539 8252095109273425591691309)
                  ·
                    refine ⟨3094535665977534596884241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8252095109273425591691309 3094535665977534596884241)
                    ·
                      refine ⟨2320901749483150947663181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094535665977534596884241 2320901749483150947663181)
                      ·
                        rfl

theorem cell23_4519940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4519940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519940 prefixEnd_4519940 := by exact prefixLift 4519940
  have htrace : WordTrace (prefixWord ++ tailWord_4519940) baseStart_4519940 baseEnd_4519940 := by
    simpa [prefixWord, tailWord_4519940, baseEnd_4519940] using wordTrace_append hprefix tailTrace_4519940
  have hstable : (prefixWord ++ tailWord_4519940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519940).length < 2 ^ (prefixWord ++ tailWord_4519940).sum := by decide
  have hdescent : baseEnd_4519940 < baseStart_4519940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4519969 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_4519969 : Nat := 118140960795 + 4519969 * 2 ^ 59
def prefixEnd_4519969 : Nat := 4983230072969 + 3 ^ 40 * 4519969 * 2
def baseEnd_4519969 : Nat := 2320916640422131334200547

theorem tailTrace_4519969 : CollatzResearch.WordTrace tailWord_4519969 prefixEnd_4519969 2320916640422131334200547 := by
  unfold tailWord_4519969
  simp only [CollatzResearch.WordTrace]
  refine ⟨164856812961931737092290961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109904541974621158061527307 164856812961931737092290961)
  ·
    refine ⟨123642609721448802819218221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164856812961931737092290961 123642609721448802819218221)
    ·
      refine ⟨46365978645543301057206833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123642609721448802819218221 46365978645543301057206833)
      ·
        refine ⟨34774483984157475792905125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46365978645543301057206833 34774483984157475792905125)
        ·
          refine ⟨6520215747029526711169711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34774483984157475792905125 6520215747029526711169711)
          ·
            refine ⟨9780323620544290066754567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6520215747029526711169711 9780323620544290066754567)
            ·
              refine ⟨14670485430816435100131851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9780323620544290066754567 14670485430816435100131851)
              ·
                refine ⟨22005728146224652650197777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14670485430816435100131851 22005728146224652650197777)
                ·
                  refine ⟨16504296109668489487648333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22005728146224652650197777 16504296109668489487648333)
                  ·
                    refine ⟨6189111041125683557868125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16504296109668489487648333 6189111041125683557868125)
                    ·
                      refine ⟨2320916640422131334200547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6189111041125683557868125 2320916640422131334200547)
                      ·
                        rfl

theorem cell23_4519969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_4519969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4519969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4519969 prefixEnd_4519969 := by exact prefixLift 4519969
  have htrace : WordTrace (prefixWord ++ tailWord_4519969) baseStart_4519969 baseEnd_4519969 := by
    simpa [prefixWord, tailWord_4519969, baseEnd_4519969] using wordTrace_append hprefix tailTrace_4519969
  have hstable : (prefixWord ++ tailWord_4519969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4519969).length < 2 ^ (prefixWord ++ tailWord_4519969).sum := by decide
  have hdescent : baseEnd_4519969 < baseStart_4519969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4519969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520015 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 8]
def baseStart_4520015 : Nat := 118140960795 + 4520015 * 2 ^ 59
def prefixEnd_4520015 : Nat := 4983230072969 + 3 ^ 40 * 4520015 * 2
def baseEnd_4520015 : Nat := 257882251170248683802815

theorem tailTrace_4520015 : CollatzResearch.WordTrace tailWord_4520015 prefixEnd_4520015 257882251170248683802815 := by
  unfold tailWord_4520015
  simp only [CollatzResearch.WordTrace]
  refine ⟨164858490719765086948465499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109905660479843391298976999 164858490719765086948465499)
  ·
    refine ⟨247287736079647630422698249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164858490719765086948465499 247287736079647630422698249)
    ·
      refine ⟨185465802059735722817023687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247287736079647630422698249 185465802059735722817023687)
      ·
        refine ⟨278198703089603584225535531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185465802059735722817023687 278198703089603584225535531)
        ·
          refine ⟨417298054634405376338303297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278198703089603584225535531 417298054634405376338303297)
          ·
            refine ⟨312973540975804032253727473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417298054634405376338303297 312973540975804032253727473)
            ·
              refine ⟨234730155731853024190295605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312973540975804032253727473 234730155731853024190295605)
              ·
                refine ⟨22005952099861221017840213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 234730155731853024190295605 22005952099861221017840213)
                ·
                  refine ⟨257882251170248683802815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22005952099861221017840213 257882251170248683802815)
                  ·
                    rfl

theorem cell23_4520015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 8].length) (baseStart_4520015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520015 prefixEnd_4520015 := by exact prefixLift 4520015
  have htrace : WordTrace (prefixWord ++ tailWord_4520015) baseStart_4520015 baseEnd_4520015 := by
    simpa [prefixWord, tailWord_4520015, baseEnd_4520015] using wordTrace_append hprefix tailTrace_4520015
  have hstable : (prefixWord ++ tailWord_4520015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520015).length < 2 ^ (prefixWord ++ tailWord_4520015).sum := by decide
  have hdescent : baseEnd_4520015 < baseStart_4520015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520096 : List Nat := [2, 1, 1, 4, 2, 4, 1, 2, 1, 5]
def baseStart_4520096 : Nat := 118140960795 + 4520096 * 2 ^ 59
def prefixEnd_4520096 : Nat := 4983230072969 + 3 ^ 40 * 4520096 * 2
def baseEnd_4520096 : Nat := 773660617488417445770821

theorem tailTrace_4520096 : CollatzResearch.WordTrace tailWord_4520096 prefixEnd_4520096 773660617488417445770821 := by
  unfold tailWord_4520096
  simp only [CollatzResearch.WordTrace]
  refine ⟨82430722516235818891082071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109907630021647758521442761 82430722516235818891082071)
  ·
    refine ⟨123646083774353728336623107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82430722516235818891082071 123646083774353728336623107)
    ·
      refine ⟨185469125661530592504934661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123646083774353728336623107 185469125661530592504934661)
      ·
        refine ⟨34775461061536986094675249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185469125661530592504934661 34775461061536986094675249)
        ·
          refine ⟨26081595796152739571006437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34775461061536986094675249 26081595796152739571006437)
          ·
            refine ⟨4890299211778638669563707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26081595796152739571006437 4890299211778638669563707)
            ·
              refine ⟨7335448817667958004345561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4890299211778638669563707 7335448817667958004345561)
              ·
                refine ⟨5501586613250968503259171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7335448817667958004345561 5501586613250968503259171)
                ·
                  refine ⟨8252379919876452754888757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5501586613250968503259171 8252379919876452754888757)
                  ·
                    refine ⟨773660617488417445770821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8252379919876452754888757 773660617488417445770821)
                    ·
                      rfl

theorem cell23_4520096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 1, 5].length) (baseStart_4520096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520096 prefixEnd_4520096 := by exact prefixLift 4520096
  have htrace : WordTrace (prefixWord ++ tailWord_4520096) baseStart_4520096 baseEnd_4520096 := by
    simpa [prefixWord, tailWord_4520096, baseEnd_4520096] using wordTrace_append hprefix tailTrace_4520096
  have hstable : (prefixWord ++ tailWord_4520096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520096).length < 2 ^ (prefixWord ++ tailWord_4520096).sum := by decide
  have hdescent : baseEnd_4520096 < baseStart_4520096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520109 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_4520109 : Nat := 118140960795 + 4520109 * 2 ^ 59
def prefixEnd_4520109 : Nat := 4983230072969 + 3 ^ 40 * 4520109 * 2
def baseEnd_4520109 : Nat := 773662842571253595483301

theorem tailTrace_4520109 : CollatzResearch.WordTrace tailWord_4520109 prefixEnd_4520109 773662842571253595483301 := by
  unfold tailWord_4520109
  simp only [CollatzResearch.WordTrace]
  refine ⟨164861919181424541002387381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109907946120949694001591587 164861919181424541002387381)
  ·
    refine ⟨15455804923258550718973817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164861919181424541002387381 15455804923258550718973817)
    ·
      refine ⟨11591853692443913039230363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15455804923258550718973817 11591853692443913039230363)
      ·
        refine ⟨17387780538665869558845545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11591853692443913039230363 17387780538665869558845545)
        ·
          refine ⟨13040835403999402169134159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17387780538665869558845545 13040835403999402169134159)
          ·
            refine ⟨19561253105999103253701239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13040835403999402169134159 19561253105999103253701239)
            ·
              refine ⟨29341879658998654880551859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19561253105999103253701239 29341879658998654880551859)
              ·
                refine ⟨44012819488497982320827789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29341879658998654880551859 44012819488497982320827789)
                ·
                  refine ⟨16504807308186743370310421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44012819488497982320827789 16504807308186743370310421)
                  ·
                    refine ⟨773662842571253595483301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16504807308186743370310421 773662842571253595483301)
                    ·
                      rfl

theorem cell23_4520109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_4520109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520109 prefixEnd_4520109 := by exact prefixLift 4520109
  have htrace : WordTrace (prefixWord ++ tailWord_4520109) baseStart_4520109 baseEnd_4520109 := by
    simpa [prefixWord, tailWord_4520109, baseEnd_4520109] using wordTrace_append hprefix tailTrace_4520109
  have hstable : (prefixWord ++ tailWord_4520109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520109).length < 2 ^ (prefixWord ++ tailWord_4520109).sum := by decide
  have hdescent : baseEnd_4520109 < baseStart_4520109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520113 : List Nat := [1, 2, 2, 5, 2, 1, 3, 1, 1, 5]
def baseStart_4520113 : Nat := 118140960795 + 4520113 * 2 ^ 59
def prefixEnd_4520113 : Nat := 4983230072969 + 3 ^ 40 * 4520113 * 2
def baseEnd_4520113 : Nat := 773663527212126256933295

theorem tailTrace_4520113 : CollatzResearch.WordTrace tailWord_4520113 prefixEnd_4520113 773663527212126256933295 := by
  unfold tailWord_4520113
  simp only [CollatzResearch.WordTrace]
  refine ⟨164862065073410049685532993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109908043382273366457021995 164862065073410049685532993)
  ·
    refine ⟨123646548805057537264149745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164862065073410049685532993 123646548805057537264149745)
    ·
      refine ⟨92734911603793152948112309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123646548805057537264149745 92734911603793152948112309)
      ·
        refine ⟨8693897962855608088885529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92734911603793152948112309 8693897962855608088885529)
        ·
          refine ⟨6520423472141706066664147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8693897962855608088885529 6520423472141706066664147)
          ·
            refine ⟨9780635208212559099996221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6520423472141706066664147 9780635208212559099996221)
            ·
              refine ⟨3667738203079709662498583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9780635208212559099996221 3667738203079709662498583)
              ·
                refine ⟨5501607304619564493747875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3667738203079709662498583 5501607304619564493747875)
                ·
                  refine ⟨8252410956929346740621813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5501607304619564493747875 8252410956929346740621813)
                  ·
                    refine ⟨773663527212126256933295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8252410956929346740621813 773663527212126256933295)
                    ·
                      rfl

theorem cell23_4520113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_4520113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520113 prefixEnd_4520113 := by exact prefixLift 4520113
  have htrace : WordTrace (prefixWord ++ tailWord_4520113) baseStart_4520113 baseEnd_4520113 := by
    simpa [prefixWord, tailWord_4520113, baseEnd_4520113] using wordTrace_append hprefix tailTrace_4520113
  have hstable : (prefixWord ++ tailWord_4520113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520113).length < 2 ^ (prefixWord ++ tailWord_4520113).sum := by decide
  have hdescent : baseEnd_4520113 < baseStart_4520113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520119 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 5]
def baseStart_4520119 : Nat := 118140960795 + 4520119 * 2 ^ 59
def prefixEnd_4520119 : Nat := 4983230072969 + 3 ^ 40 * 4520119 * 2
def baseEnd_4520119 : Nat := 2320993662520305747324857

theorem tailTrace_4520119 : CollatzResearch.WordTrace tailWord_4520119 prefixEnd_4520119 2320993662520305747324857 := by
  unfold tailWord_4520119
  simp only [CollatzResearch.WordTrace]
  refine ⟨164862283911388312710251411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109908189274258875140167607 164862283911388312710251411)
  ·
    refine ⟨247293425867082469065377117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164862283911388312710251411 247293425867082469065377117)
    ·
      refine ⟨92735034700155925899516419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247293425867082469065377117 92735034700155925899516419)
      ·
        refine ⟨139102552050233888849274629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92735034700155925899516419 139102552050233888849274629)
        ·
          refine ⟨26081728509418854159238993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139102552050233888849274629 26081728509418854159238993)
          ·
            refine ⟨19561296382064140619429245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26081728509418854159238993 19561296382064140619429245)
            ·
              refine ⟨7335486143274052732285967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19561296382064140619429245 7335486143274052732285967)
              ·
                refine ⟨11003229214911079098428951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7335486143274052732285967 11003229214911079098428951)
                ·
                  refine ⟨16504843822366618647643427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11003229214911079098428951 16504843822366618647643427)
                  ·
                    refine ⟨24757265733549927971465141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16504843822366618647643427 24757265733549927971465141)
                    ·
                      refine ⟨2320993662520305747324857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24757265733549927971465141 2320993662520305747324857)
                      ·
                        rfl

theorem cell23_4520119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_4520119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520119 prefixEnd_4520119 := by exact prefixLift 4520119
  have htrace : WordTrace (prefixWord ++ tailWord_4520119) baseStart_4520119 baseEnd_4520119 := by
    simpa [prefixWord, tailWord_4520119, baseEnd_4520119] using wordTrace_append hprefix tailTrace_4520119
  have hstable : (prefixWord ++ tailWord_4520119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520119).length < 2 ^ (prefixWord ++ tailWord_4520119).sum := by decide
  have hdescent : baseEnd_4520119 < baseStart_4520119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520146 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_4520146 : Nat := 118140960795 + 4520146 * 2 ^ 59
def prefixEnd_4520146 : Nat := 4983230072969 + 3 ^ 40 * 4520146 * 2
def baseEnd_4520146 : Nat := 2321007526497977141687233

theorem tailTrace_4520146 : CollatzResearch.WordTrace tailWord_4520146 prefixEnd_4520146 2321007526497977141687233 := by
  unfold tailWord_4520146
  simp only [CollatzResearch.WordTrace]
  refine ⟨41215817170572624080371073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109908845788193664214322861 41215817170572624080371073)
  ·
    refine ⟨30911862877929468060278305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41215817170572624080371073 30911862877929468060278305)
    ·
      refine ⟨23183897158447101045208729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30911862877929468060278305 23183897158447101045208729)
      ·
        refine ⟨17387922868835325783906547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23183897158447101045208729 17387922868835325783906547)
        ·
          refine ⟨26081884303252988675859821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17387922868835325783906547 26081884303252988675859821)
          ·
            refine ⟨9780706613719870753447433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26081884303252988675859821 9780706613719870753447433)
            ·
              refine ⟨7335529960289903065085575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9780706613719870753447433 7335529960289903065085575)
              ·
                refine ⟨11003294940434854597628363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7335529960289903065085575 11003294940434854597628363)
                ·
                  refine ⟨16504942410652281896442545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11003294940434854597628363 16504942410652281896442545)
                  ·
                    refine ⟨12378706807989211422331909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16504942410652281896442545 12378706807989211422331909)
                    ·
                      refine ⟨2321007526497977141687233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12378706807989211422331909 2321007526497977141687233)
                      ·
                        rfl

theorem cell23_4520146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_4520146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520146 prefixEnd_4520146 := by exact prefixLift 4520146
  have htrace : WordTrace (prefixWord ++ tailWord_4520146) baseStart_4520146 baseEnd_4520146 := by
    simpa [prefixWord, tailWord_4520146, baseEnd_4520146] using wordTrace_append hprefix tailTrace_4520146
  have hstable : (prefixWord ++ tailWord_4520146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520146).length < 2 ^ (prefixWord ++ tailWord_4520146).sum := by decide
  have hdescent : baseEnd_4520146 < baseStart_4520146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520150 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_4520150 : Nat := 118140960795 + 4520150 * 2 ^ 59
def prefixEnd_4520150 : Nat := 4983230072969 + 3 ^ 40 * 4520150 * 2
def baseEnd_4520150 : Nat := 2321009580420595126037215

theorem tailTrace_4520150 : CollatzResearch.WordTrace tailWord_4520150 prefixEnd_4520150 2321009580420595126037215 := by
  unfold tailWord_4520150
  simp only [CollatzResearch.WordTrace]
  refine ⟨10303963410892250312789369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109908943049517336669753269 10303963410892250312789369)
  ·
    refine ⟨7727972558169187734592027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10303963410892250312789369 7727972558169187734592027)
    ·
      refine ⟨11591958837253781601888041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7727972558169187734592027 11591958837253781601888041)
      ·
        refine ⟨8693969127940336201416031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11591958837253781601888041 8693969127940336201416031)
        ·
          refine ⟨13040953691910504302124047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8693969127940336201416031 13040953691910504302124047)
          ·
            refine ⟨19561430537865756453186071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13040953691910504302124047 19561430537865756453186071)
            ·
              refine ⟨29342145806798634679779107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19561430537865756453186071 29342145806798634679779107)
              ·
                refine ⟨44013218710197952019668661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29342145806798634679779107 44013218710197952019668661)
                ·
                  refine ⟨4126239254081058001843937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44013218710197952019668661 4126239254081058001843937)
                  ·
                    refine ⟨3094679440560793501382953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4126239254081058001843937 3094679440560793501382953)
                    ·
                      refine ⟨2321009580420595126037215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094679440560793501382953 2321009580420595126037215)
                      ·
                        rfl

theorem cell23_4520150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_4520150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520150 prefixEnd_4520150 := by exact prefixLift 4520150
  have htrace : WordTrace (prefixWord ++ tailWord_4520150) baseStart_4520150 baseEnd_4520150 := by
    simpa [prefixWord, tailWord_4520150, baseEnd_4520150] using wordTrace_append hprefix tailTrace_4520150
  have hstable : (prefixWord ++ tailWord_4520150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520150).length < 2 ^ (prefixWord ++ tailWord_4520150).sum := by decide
  have hdescent : baseEnd_4520150 < baseStart_4520150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520167 : List Nat := [1, 1, 5, 3, 1, 2, 2, 3, 1, 2, 2]
def baseStart_4520167 : Nat := 118140960795 + 4520167 * 2 ^ 59
def prefixEnd_4520167 : Nat := 4983230072969 + 3 ^ 40 * 4520167 * 2
def baseEnd_4520167 : Nat := 2321018309591721559524637

theorem tailTrace_4520167 : CollatzResearch.WordTrace tailWord_4520167 prefixEnd_4520167 2321018309591721559524637 := by
  unfold tailWord_4520167
  simp only [CollatzResearch.WordTrace]
  refine ⟨164864034615214416907998755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109909356410142944605332503 164864034615214416907998755)
  ·
    refine ⟨247296051922821625361998133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164864034615214416907998755 247296051922821625361998133)
    ·
      refine ⟨23184004867764527377687325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 247296051922821625361998133 23184004867764527377687325)
      ·
        refine ⟨8694001825411697766632747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23184004867764527377687325 8694001825411697766632747)
        ·
          refine ⟨13041002738117546649949121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8694001825411697766632747 13041002738117546649949121)
          ·
            refine ⟨9780752053588159987461841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13041002738117546649949121 9780752053588159987461841)
            ·
              refine ⟨7335564040191119990596381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9780752053588159987461841 7335564040191119990596381)
              ·
                refine ⟨2750836515071669996473643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7335564040191119990596381 2750836515071669996473643)
                ·
                  refine ⟨4126254772607504994710465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2750836515071669996473643 4126254772607504994710465)
                  ·
                    refine ⟨3094691079455628746032849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4126254772607504994710465 3094691079455628746032849)
                    ·
                      refine ⟨2321018309591721559524637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094691079455628746032849 2321018309591721559524637)
                      ·
                        rfl

theorem cell23_4520167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_4520167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520167 prefixEnd_4520167 := by exact prefixLift 4520167
  have htrace : WordTrace (prefixWord ++ tailWord_4520167) baseStart_4520167 baseEnd_4520167 := by
    simpa [prefixWord, tailWord_4520167, baseEnd_4520167] using wordTrace_append hprefix tailTrace_4520167
  have hstable : (prefixWord ++ tailWord_4520167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520167).length < 2 ^ (prefixWord ++ tailWord_4520167).sum := by decide
  have hdescent : baseEnd_4520167 < baseStart_4520167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520200 : List Nat := [2, 1, 3, 2, 3, 2, 3, 1, 2, 1, 3]
def baseStart_4520200 : Nat := 118140960795 + 4520200 * 2 ^ 59
def prefixEnd_4520200 : Nat := 4983230072969 + 3 ^ 40 * 4520200 * 2
def baseEnd_4520200 : Nat := 2321035254453319930411985

theorem tailTrace_4520200 : CollatzResearch.WordTrace tailWord_4520200 prefixEnd_4520200 2321035254453319930411985 := by
  unfold tailWord_4520200
  simp only [CollatzResearch.WordTrace]
  refine ⟨82432619112047431771975027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109910158816063242362633369 82432619112047431771975027)
  ·
    refine ⟨123648928668071147657962541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82432619112047431771975027 123648928668071147657962541)
    ·
      refine ⟨46368348250526680371735953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123648928668071147657962541 46368348250526680371735953)
      ·
        refine ⟨34776261187895010278801965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46368348250526680371735953 34776261187895010278801965)
        ·
          refine ⟨13041097945460628854550737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34776261187895010278801965 13041097945460628854550737)
          ·
            refine ⟨9780823459095471640913053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13041097945460628854550737 9780823459095471640913053)
            ·
              refine ⟨3667808797160801865342395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9780823459095471640913053 3667808797160801865342395)
              ·
                refine ⟨5501713195741202798013593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3667808797160801865342395 5501713195741202798013593)
                ·
                  refine ⟨4126284896805902098510195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5501713195741202798013593 4126284896805902098510195)
                  ·
                    refine ⟨6189427345208853147765293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4126284896805902098510195 6189427345208853147765293)
                    ·
                      refine ⟨2321035254453319930411985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6189427345208853147765293 2321035254453319930411985)
                      ·
                        rfl

theorem cell23_4520200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_4520200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520200 prefixEnd_4520200 := by exact prefixLift 4520200
  have htrace : WordTrace (prefixWord ++ tailWord_4520200) baseStart_4520200 baseEnd_4520200 := by
    simpa [prefixWord, tailWord_4520200, baseEnd_4520200] using wordTrace_append hprefix tailTrace_4520200
  have hstable : (prefixWord ++ tailWord_4520200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520200).length < 2 ^ (prefixWord ++ tailWord_4520200).sum := by decide
  have hdescent : baseEnd_4520200 < baseStart_4520200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520223 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 4, 2, 2]
def baseStart_4520223 : Nat := 118140960795 + 4520223 * 2 ^ 59
def prefixEnd_4520223 : Nat := 4983230072969 + 3 ^ 40 * 4520223 * 2
def baseEnd_4520223 : Nat := 2321047064508373340424379

theorem tailTrace_4520223 : CollatzResearch.WordTrace tailWord_4520223 prefixEnd_4520223 2321047064508373340424379 := by
  unfold tailWord_4520223
  simp only [CollatzResearch.WordTrace]
  refine ⟨164866077103011538472037323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109910718068674358981358215 164866077103011538472037323)
  ·
    refine ⟨247299115654517307708055985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164866077103011538472037323 247299115654517307708055985)
    ·
      refine ⟨185474336740887980781041989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247299115654517307708055985 185474336740887980781041989)
      ·
        refine ⟨34776438138916496396445373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185474336740887980781041989 34776438138916496396445373)
        ·
          refine ⟨13041164302093686148667015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34776438138916496396445373 13041164302093686148667015)
          ·
            refine ⟨19561746453140529223000523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13041164302093686148667015 19561746453140529223000523)
            ·
              refine ⟨29342619679710793834500785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19561746453140529223000523 29342619679710793834500785)
              ·
                refine ⟨22006964759783095375875589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29342619679710793834500785 22006964759783095375875589)
                ·
                  refine ⟨4126305892459330382976673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22006964759783095375875589 4126305892459330382976673)
                  ·
                    refine ⟨3094729419344497787232505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4126305892459330382976673 3094729419344497787232505)
                    ·
                      refine ⟨2321047064508373340424379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094729419344497787232505 2321047064508373340424379)
                      ·
                        rfl

theorem cell23_4520223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_4520223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520223 prefixEnd_4520223 := by exact prefixLift 4520223
  have htrace : WordTrace (prefixWord ++ tailWord_4520223) baseStart_4520223 baseEnd_4520223 := by
    simpa [prefixWord, tailWord_4520223, baseEnd_4520223] using wordTrace_append hprefix tailTrace_4520223
  have hstable : (prefixWord ++ tailWord_4520223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520223).length < 2 ^ (prefixWord ++ tailWord_4520223).sum := by decide
  have hdescent : baseEnd_4520223 < baseStart_4520223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520226 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_4520226 : Nat := 118140960795 + 4520226 * 2 ^ 59
def prefixEnd_4520226 : Nat := 4983230072969 + 3 ^ 40 * 4520226 * 2
def baseEnd_4520226 : Nat := 2321048604950336828686865

theorem tailTrace_4520226 : CollatzResearch.WordTrace tailWord_4520226 prefixEnd_4520226 2321048604950336828686865 := by
  unfold tailWord_4520226
  simp only [CollatzResearch.WordTrace]
  refine ⟨41216546630500167496099133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109910791014667113322931021 41216546630500167496099133)
  ·
    refine ⟨15456204986437562811037175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41216546630500167496099133 15456204986437562811037175)
    ·
      refine ⟨23184307479656344216555763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15456204986437562811037175 23184307479656344216555763)
      ·
        refine ⟨34776461219484516324833645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23184307479656344216555763 34776461219484516324833645)
        ·
          refine ⟨13041172957306693621812617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34776461219484516324833645 13041172957306693621812617)
          ·
            refine ⟨9780879717980020216359463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13041172957306693621812617 9780879717980020216359463)
            ·
              refine ⟨14671319576970030324539195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9780879717980020216359463 14671319576970030324539195)
              ·
                refine ⟨22006979365455045486808793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14671319576970030324539195 22006979365455045486808793)
                ·
                  refine ⟨16505234524091284115106595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22006979365455045486808793 16505234524091284115106595)
                  ·
                    refine ⟨24757851786136926172659893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16505234524091284115106595 24757851786136926172659893)
                    ·
                      refine ⟨2321048604950336828686865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24757851786136926172659893 2321048604950336828686865)
                      ·
                        rfl

theorem cell23_4520226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_4520226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520226 prefixEnd_4520226 := by exact prefixLift 4520226
  have htrace : WordTrace (prefixWord ++ tailWord_4520226) baseStart_4520226 baseEnd_4520226 := by
    simpa [prefixWord, tailWord_4520226, baseEnd_4520226] using wordTrace_append hprefix tailTrace_4520226
  have hstable : (prefixWord ++ tailWord_4520226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520226).length < 2 ^ (prefixWord ++ tailWord_4520226).sum := by decide
  have hdescent : baseEnd_4520226 < baseStart_4520226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520239 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 3]
def baseStart_4520239 : Nat := 118140960795 + 4520239 * 2 ^ 59
def prefixEnd_4520239 : Nat := 4983230072969 + 3 ^ 40 * 4520239 * 2
def baseEnd_4520239 : Nat := 2321055280198845277824305

theorem tailTrace_4520239 : CollatzResearch.WordTrace tailWord_4520239 prefixEnd_4520239 2321055280198845277824305 := by
  unfold tailWord_4520239
  simp only [CollatzResearch.WordTrace]
  refine ⟨164866660670953573204619771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109911107113969048803079847 164866660670953573204619771)
  ·
    refine ⟨247299991006430359806929657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164866660670953573204619771 247299991006430359806929657)
    ·
      refine ⟨185474993254822769855197243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247299991006430359806929657 185474993254822769855197243)
      ·
        refine ⟨278212489882234154782795865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185474993254822769855197243 278212489882234154782795865)
        ·
          refine ⟨208659367411675616087096899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278212489882234154782795865 208659367411675616087096899)
          ·
            refine ⟨312989051117513424130645349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208659367411675616087096899 312989051117513424130645349)
            ·
              refine ⟨58685447084533767024496003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 312989051117513424130645349 58685447084533767024496003)
              ·
                refine ⟨88028170626800650536744005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58685447084533767024496003 88028170626800650536744005)
                ·
                  refine ⟨16505281992525121975639501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88028170626800650536744005 16505281992525121975639501)
                  ·
                    refine ⟨6189480747196920740864813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16505281992525121975639501 6189480747196920740864813)
                    ·
                      refine ⟨2321055280198845277824305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6189480747196920740864813 2321055280198845277824305)
                      ·
                        rfl

theorem cell23_4520239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 3].length) (baseStart_4520239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520239 prefixEnd_4520239 := by exact prefixLift 4520239
  have htrace : WordTrace (prefixWord ++ tailWord_4520239) baseStart_4520239 baseEnd_4520239 := by
    simpa [prefixWord, tailWord_4520239, baseEnd_4520239] using wordTrace_append hprefix tailTrace_4520239
  have hstable : (prefixWord ++ tailWord_4520239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520239).length < 2 ^ (prefixWord ++ tailWord_4520239).sum := by decide
  have hdescent : baseEnd_4520239 < baseStart_4520239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520257 : List Nat := [1, 2, 5, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_4520257 : Nat := 118140960795 + 4520257 * 2 ^ 59
def prefixEnd_4520257 : Nat := 4983230072969 + 3 ^ 40 * 4520257 * 2
def baseEnd_4520257 : Nat := 2321064522850626207399223

theorem tailTrace_4520257 : CollatzResearch.WordTrace tailWord_4520257 prefixEnd_4520257 2321064522850626207399223 := by
  unfold tailWord_4520257
  simp only [CollatzResearch.WordTrace]
  refine ⟨164867317184888362278775025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109911544789925574852516683 164867317184888362278775025)
  ·
    refine ⟨123650487888666271709081269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164867317184888362278775025 123650487888666271709081269)
    ·
      refine ⟨11592233239562462972726369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123650487888666271709081269 11592233239562462972726369)
      ·
        refine ⟨8694174929671847229544777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11592233239562462972726369 8694174929671847229544777)
        ·
          refine ⟨6520631197253885422158583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8694174929671847229544777 6520631197253885422158583)
          ·
            refine ⟨9780946795880828133237875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6520631197253885422158583 9780946795880828133237875)
            ·
              refine ⟨14671420193821242199856813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9780946795880828133237875 14671420193821242199856813)
              ·
                refine ⟨5501782572682965824946305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14671420193821242199856813 5501782572682965824946305)
                ·
                  refine ⟨4126336929512224368709729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5501782572682965824946305 4126336929512224368709729)
                  ·
                    refine ⟨3094752697134168276532297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4126336929512224368709729 3094752697134168276532297)
                    ·
                      refine ⟨2321064522850626207399223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094752697134168276532297 2321064522850626207399223)
                      ·
                        rfl

theorem cell23_4520257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_4520257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520257 prefixEnd_4520257 := by exact prefixLift 4520257
  have htrace : WordTrace (prefixWord ++ tailWord_4520257) baseStart_4520257 baseEnd_4520257 := by
    simpa [prefixWord, tailWord_4520257, baseEnd_4520257] using wordTrace_append hprefix tailTrace_4520257
  have hstable : (prefixWord ++ tailWord_4520257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520257).length < 2 ^ (prefixWord ++ tailWord_4520257).sum := by decide
  have hdescent : baseEnd_4520257 < baseStart_4520257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520276 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_4520276 : Nat := 118140960795 + 4520276 * 2 ^ 59
def prefixEnd_4520276 : Nat := 4983230072969 + 3 ^ 40 * 4520276 * 2
def baseEnd_4520276 : Nat := 773691426327687211020545

theorem tailTrace_4520276 : CollatzResearch.WordTrace tailWord_4520276 prefixEnd_4520276 773691426327687211020545 := by
  unfold tailWord_4520276
  simp only [CollatzResearch.WordTrace]
  refine ⟨82434005085909764261858341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109912006781213019015811121 82434005085909764261858341)
  ·
    refine ⟨15456375953608080799098439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82434005085909764261858341 15456375953608080799098439)
    ·
      refine ⟨23184563930412121198647659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15456375953608080799098439 23184563930412121198647659)
      ·
        refine ⟨34776845895618181797971489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23184563930412121198647659 34776845895618181797971489)
        ·
          refine ⟨26082634421713636348478617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34776845895618181797971489 26082634421713636348478617)
          ·
            refine ⟨19561975816285227261358963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26082634421713636348478617 19561975816285227261358963)
            ·
              refine ⟨29342963724427840892038445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19561975816285227261358963 29342963724427840892038445)
              ·
                refine ⟨11003611396660440334514417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29342963724427840892038445 11003611396660440334514417)
                ·
                  refine ⟨8252708547495330250885813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11003611396660440334514417 8252708547495330250885813)
                  ·
                    refine ⟨773691426327687211020545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8252708547495330250885813 773691426327687211020545)
                    ·
                      rfl

theorem cell23_4520276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_4520276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520276 prefixEnd_4520276 := by exact prefixLift 4520276
  have htrace : WordTrace (prefixWord ++ tailWord_4520276) baseStart_4520276 baseEnd_4520276 := by
    simpa [prefixWord, tailWord_4520276, baseEnd_4520276] using wordTrace_append hprefix tailTrace_4520276
  have hstable : (prefixWord ++ tailWord_4520276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520276).length < 2 ^ (prefixWord ++ tailWord_4520276).sum := by decide
  have hdescent : baseEnd_4520276 < baseStart_4520276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520323 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 3, 4]
def baseStart_4520323 : Nat := 118140960795 + 4520323 * 2 ^ 59
def prefixEnd_4520323 : Nat := 4983230072969 + 3 ^ 40 * 4520323 * 2
def baseEnd_4520323 : Nat := 773699470857940983057973

theorem tailTrace_4520323 : CollatzResearch.WordTrace tailWord_4520323 prefixEnd_4520323 773699470857940983057973 := by
  unfold tailWord_4520323
  simp only [CollatzResearch.WordTrace]
  refine ⟨164869724402649255550677623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109913149601766170367118415 164869724402649255550677623)
  ·
    refine ⟨247304586603973883326016435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164869724402649255550677623 247304586603973883326016435)
    ·
      refine ⟨370956879905960824989024653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247304586603973883326016435 370956879905960824989024653)
      ·
        refine ⟨139108829964735309370884245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 370956879905960824989024653 139108829964735309370884245)
        ·
          refine ⟨6520726404596967626760199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 139108829964735309370884245 6520726404596967626760199)
          ·
            refine ⟨9781089606895451440140299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6520726404596967626760199 9781089606895451440140299)
            ·
              refine ⟨14671634410343177160210449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9781089606895451440140299 14671634410343177160210449)
              ·
                refine ⟨11003725807757382870157837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14671634410343177160210449 11003725807757382870157837)
                ·
                  refine ⟨4126397177909018576309189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11003725807757382870157837 4126397177909018576309189)
                  ·
                    refine ⟨773699470857940983057973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4126397177909018576309189 773699470857940983057973)
                    ·
                      rfl

theorem cell23_4520323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 4].length) (baseStart_4520323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520323 prefixEnd_4520323 := by exact prefixLift 4520323
  have htrace : WordTrace (prefixWord ++ tailWord_4520323) baseStart_4520323 baseEnd_4520323 := by
    simpa [prefixWord, tailWord_4520323, baseEnd_4520323] using wordTrace_append hprefix tailTrace_4520323
  have hstable : (prefixWord ++ tailWord_4520323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520323).length < 2 ^ (prefixWord ++ tailWord_4520323).sum := by decide
  have hdescent : baseEnd_4520323 < baseStart_4520323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520353 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 8]
def baseStart_4520353 : Nat := 118140960795 + 4520353 * 2 ^ 59
def prefixEnd_4520353 : Nat := 4983230072969 + 3 ^ 40 * 4520353 * 2
def baseEnd_4520353 : Nat := 257901535221495314644309

theorem tailTrace_4520353 : CollatzResearch.WordTrace tailWord_4520353 prefixEnd_4520353 257901535221495314644309 := by
  unfold tailWord_4520353
  simp only [CollatzResearch.WordTrace]
  refine ⟨164870818592540570674269713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109913879061693713782846475 164870818592540570674269713)
  ·
    refine ⟨123653113944405428005702285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164870818592540570674269713 123653113944405428005702285)
    ·
      refine ⟨46369917729152035502138357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123653113944405428005702285 46369917729152035502138357)
      ·
        refine ⟨4347179787108003328325471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46369917729152035502138357 4347179787108003328325471)
        ·
          refine ⟨6520769680662004992488207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4347179787108003328325471 6520769680662004992488207)
          ·
            refine ⟨9781154520993007488732311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6520769680662004992488207 9781154520993007488732311)
            ·
              refine ⟨14671731781489511233098467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9781154520993007488732311 14671731781489511233098467)
              ·
                refine ⟨22007597672234266849647701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14671731781489511233098467 22007597672234266849647701)
                ·
                  refine ⟨257901535221495314644309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22007597672234266849647701 257901535221495314644309)
                  ·
                    rfl

theorem cell23_4520353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 8].length) (baseStart_4520353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520353 prefixEnd_4520353 := by exact prefixLift 4520353
  have htrace : WordTrace (prefixWord ++ tailWord_4520353) baseStart_4520353 baseEnd_4520353 := by
    simpa [prefixWord, tailWord_4520353, baseEnd_4520353] using wordTrace_append hprefix tailTrace_4520353
  have hstable : (prefixWord ++ tailWord_4520353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520353).length < 2 ^ (prefixWord ++ tailWord_4520353).sum := by decide
  have hdescent : baseEnd_4520353 < baseStart_4520353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520379 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 7, 6]
def baseStart_4520379 : Nat := 118140960795 + 4520379 * 2 ^ 59
def prefixEnd_4520379 : Nat := 4983230072969 + 3 ^ 40 * 4520379 * 2
def baseEnd_4520379 : Nat := 773709055830158243357887

theorem tailTrace_4520379 : CollatzResearch.WordTrace tailWord_4520379 prefixEnd_4520379 773709055830158243357887 := by
  unfold tailWord_4520379
  simp only [CollatzResearch.WordTrace]
  refine ⟨164871766890446377114716191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109914511260297584743144127 164871766890446377114716191)
  ·
    refine ⟨247307650335669565672074287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164871766890446377114716191 247307650335669565672074287)
    ·
      refine ⟨370961475503504348508111431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247307650335669565672074287 370961475503504348508111431)
      ·
        refine ⟨556442213255256522762167147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370961475503504348508111431 556442213255256522762167147)
        ·
          refine ⟨834663319882884784143250721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556442213255256522762167147 834663319882884784143250721)
          ·
            refine ⟨625997489912163588107438041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 834663319882884784143250721 625997489912163588107438041)
            ·
              refine ⟨469498117434122691080578531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625997489912163588107438041 469498117434122691080578531)
              ·
                refine ⟨704247176151184036620867797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469498117434122691080578531 704247176151184036620867797)
                ·
                  refine ⟨16505793191043375858301589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 704247176151184036620867797 16505793191043375858301589)
                  ·
                    refine ⟨773709055830158243357887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16505793191043375858301589 773709055830158243357887)
                    ·
                      rfl

theorem cell23_4520379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 6].length) (baseStart_4520379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520379 prefixEnd_4520379 := by exact prefixLift 4520379
  have htrace : WordTrace (prefixWord ++ tailWord_4520379) baseStart_4520379 baseEnd_4520379 := by
    simpa [prefixWord, tailWord_4520379, baseEnd_4520379] using wordTrace_append hprefix tailTrace_4520379
  have hstable : (prefixWord ++ tailWord_4520379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520379).length < 2 ^ (prefixWord ++ tailWord_4520379).sum := by decide
  have hdescent : baseEnd_4520379 < baseStart_4520379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520380 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 3, 1, 3]
def baseStart_4520380 : Nat := 118140960795 + 4520380 * 2 ^ 59
def prefixEnd_4520380 : Nat := 4983230072969 + 3 ^ 40 * 4520380 * 2
def baseEnd_4520380 : Nat := 2321127680971129226161157

theorem tailTrace_4520380 : CollatzResearch.WordTrace tailWord_4520380 prefixEnd_4520380 2321127680971129226161157 := by
  unfold tailWord_4520380
  simp only [CollatzResearch.WordTrace]
  refine ⟨82435901681721377142751297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109914535575628502857001729 82435901681721377142751297)
  ·
    refine ⟨61826926261291032857063473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82435901681721377142751297 61826926261291032857063473)
    ·
      refine ⟨46370194695968274642797605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61826926261291032857063473 46370194695968274642797605)
      ·
        refine ⟨8694411505494051495524551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46370194695968274642797605 8694411505494051495524551)
        ·
          refine ⟨13041617258241077243286827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8694411505494051495524551 13041617258241077243286827)
          ·
            refine ⟨19562425887361615864930241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13041617258241077243286827 19562425887361615864930241)
            ·
              refine ⟨14671819415521211898697681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19562425887361615864930241 14671819415521211898697681)
              ·
                refine ⟨11003864561640908924023261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14671819415521211898697681 11003864561640908924023261)
                ·
                  refine ⟨4126449210615340846508723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11003864561640908924023261 4126449210615340846508723)
                  ·
                    refine ⟨6189673815923011269763085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4126449210615340846508723 6189673815923011269763085)
                    ·
                      refine ⟨2321127680971129226161157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6189673815923011269763085 2321127680971129226161157)
                      ·
                        rfl

theorem cell23_4520380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_4520380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520380 prefixEnd_4520380 := by exact prefixLift 4520380
  have htrace : WordTrace (prefixWord ++ tailWord_4520380) baseStart_4520380 baseEnd_4520380 := by
    simpa [prefixWord, tailWord_4520380, baseEnd_4520380] using wordTrace_append hprefix tailTrace_4520380
  have hstable : (prefixWord ++ tailWord_4520380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520380).length < 2 ^ (prefixWord ++ tailWord_4520380).sum := by decide
  have hdescent : baseEnd_4520380 < baseStart_4520380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520413 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_4520413 : Nat := 118140960795 + 4520413 * 2 ^ 59
def prefixEnd_4520413 : Nat := 4983230072969 + 3 ^ 40 * 4520413 * 2
def baseEnd_4520413 : Nat := 773714875277575865682835

theorem tailTrace_4520413 : CollatzResearch.WordTrace tailWord_4520413 prefixEnd_4520413 773714875277575865682835 := by
  unfold tailWord_4520413
  simp only [CollatzResearch.WordTrace]
  refine ⟨164873006972323200921453893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109915337981548800614302595 164873006972323200921453893)
  ·
    refine ⟨30913688807310600172772605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164873006972323200921453893 30913688807310600172772605)
    ·
      refine ⟨11592633302741475064789727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30913688807310600172772605 11592633302741475064789727)
      ·
        refine ⟨17388949954112212597184591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11592633302741475064789727 17388949954112212597184591)
        ·
          refine ⟨26083424931168318895776887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17388949954112212597184591 26083424931168318895776887)
          ·
            refine ⟨39125137396752478343665331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26083424931168318895776887 39125137396752478343665331)
            ·
              refine ⟨58687706095128717515497997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39125137396752478343665331 58687706095128717515497997)
              ·
                refine ⟨22007889785673269068311749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58687706095128717515497997 22007889785673269068311749)
                ·
                  refine ⟨4126479334813737950308453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22007889785673269068311749 4126479334813737950308453)
                  ·
                    refine ⟨773714875277575865682835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4126479334813737950308453 773714875277575865682835)
                    ·
                      rfl

theorem cell23_4520413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_4520413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520413 prefixEnd_4520413 := by exact prefixLift 4520413
  have htrace : WordTrace (prefixWord ++ tailWord_4520413) baseStart_4520413 baseEnd_4520413 := by
    simpa [prefixWord, tailWord_4520413, baseEnd_4520413] using wordTrace_append hprefix tailTrace_4520413
  have hstable : (prefixWord ++ tailWord_4520413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520413).length < 2 ^ (prefixWord ++ tailWord_4520413).sum := by decide
  have hdescent : baseEnd_4520413 < baseStart_4520413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520423 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_4520423 : Nat := 118140960795 + 4520423 * 2 ^ 59
def prefixEnd_4520423 : Nat := 4983230072969 + 3 ^ 40 * 4520423 * 2
def baseEnd_4520423 : Nat := 2321149760639272557923459

theorem tailTrace_4520423 : CollatzResearch.WordTrace tailWord_4520423 prefixEnd_4520423 2321149760639272557923459 := by
  unfold tailWord_4520423
  simp only [CollatzResearch.WordTrace]
  refine ⟨164873371702286972629317923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109915581134857981752878615 164873371702286972629317923)
  ·
    refine ⟨247310057553430458943976885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164873371702286972629317923 247310057553430458943976885)
    ·
      refine ⟨23185317895634105525997833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 247310057553430458943976885 23185317895634105525997833)
      ·
        refine ⟨17388988421725579144498375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23185317895634105525997833 17388988421725579144498375)
        ·
          refine ⟨26083482632588368716747563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17388988421725579144498375 26083482632588368716747563)
          ·
            refine ⟨39125223948882553075121345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26083482632588368716747563 39125223948882553075121345)
            ·
              refine ⟨29343917961661914806341009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39125223948882553075121345 29343917961661914806341009)
              ·
                refine ⟨22007938471246436104755757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29343917961661914806341009 22007938471246436104755757)
                ·
                  refine ⟨8252976926717413539283409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22007938471246436104755757 8252976926717413539283409)
                  ·
                    refine ⟨6189732695038060154462557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8252976926717413539283409 6189732695038060154462557)
                    ·
                      refine ⟨2321149760639272557923459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6189732695038060154462557 2321149760639272557923459)
                      ·
                        rfl

theorem cell23_4520423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_4520423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520423 prefixEnd_4520423 := by exact prefixLift 4520423
  have htrace : WordTrace (prefixWord ++ tailWord_4520423) baseStart_4520423 baseEnd_4520423 := by
    simpa [prefixWord, tailWord_4520423, baseEnd_4520423] using wordTrace_append hprefix tailTrace_4520423
  have hstable : (prefixWord ++ tailWord_4520423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520423).length < 2 ^ (prefixWord ++ tailWord_4520423).sum := by decide
  have hdescent : baseEnd_4520423 < baseStart_4520423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520426 : List Nat := [3, 1, 3, 1, 3, 1, 1, 10]
def baseStart_4520426 : Nat := 118140960795 + 4520426 * 2 ^ 59
def prefixEnd_4520426 : Nat := 4983230072969 + 3 ^ 40 * 4520426 * 2
def baseEnd_4520426 : Nat := 85968566706712446155035

theorem tailTrace_4520426 : CollatzResearch.WordTrace tailWord_4520426 prefixEnd_4520426 85968566706712446155035 := by
  unfold tailWord_4520426
  simp only [CollatzResearch.WordTrace]
  refine ⟨41218370280319026035419283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109915654080850736094451421 41218370280319026035419283)
  ·
    refine ⟨61827555420478539053128925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41218370280319026035419283 61827555420478539053128925)
    ·
      refine ⟨23185333282679452144923347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61827555420478539053128925 23185333282679452144923347)
      ·
        refine ⟨34777999924019178217385021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23185333282679452144923347 34777999924019178217385021)
        ·
          refine ⟨13041749971507191831519383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34777999924019178217385021 13041749971507191831519383)
          ·
            refine ⟨19562624957260787747279075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13041749971507191831519383 19562624957260787747279075)
            ·
              refine ⟨29343937435891181620918613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19562624957260787747279075 29343937435891181620918613)
              ·
                refine ⟨85968566706712446155035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29343937435891181620918613 85968566706712446155035)
                ·
                  rfl

theorem cell23_4520426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 10].length) (baseStart_4520426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520426 prefixEnd_4520426 := by exact prefixLift 4520426
  have htrace : WordTrace (prefixWord ++ tailWord_4520426) baseStart_4520426 baseEnd_4520426 := by
    simpa [prefixWord, tailWord_4520426, baseEnd_4520426] using wordTrace_append hprefix tailTrace_4520426
  have hstable : (prefixWord ++ tailWord_4520426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520426).length < 2 ^ (prefixWord ++ tailWord_4520426).sum := by decide
  have hdescent : baseEnd_4520426 < baseStart_4520426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520430 : List Nat := [4, 1, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_4520430 : Nat := 118140960795 + 4520430 * 2 ^ 59
def prefixEnd_4520430 : Nat := 4983230072969 + 3 ^ 40 * 4520430 * 2
def baseEnd_4520430 : Nat := 773717785001284676845309

theorem tailTrace_4520430 : CollatzResearch.WordTrace tailWord_4520430 prefixEnd_4520430 773717785001284676845309 := by
  unfold tailWord_4520430
  simp only [CollatzResearch.WordTrace]
  refine ⟨20609203376657701603102843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109915751342174408549881829 20609203376657701603102843)
  ·
    refine ⟨30913805064986552404654265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20609203376657701603102843 30913805064986552404654265)
    ·
      refine ⟨23185353798739914303490699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30913805064986552404654265 23185353798739914303490699)
      ·
        refine ⟨34778030698109871455236049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23185353798739914303490699 34778030698109871455236049)
        ·
          refine ⟨26083523023582403591427037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34778030698109871455236049 26083523023582403591427037)
          ·
            refine ⟨9781321133843401346785139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26083523023582403591427037 9781321133843401346785139)
            ·
              refine ⟨14671981700765102020177709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9781321133843401346785139 14671981700765102020177709)
              ·
                refine ⟨5501993137786913257566641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14671981700765102020177709 5501993137786913257566641)
                ·
                  refine ⟨4126494853340184943174981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5501993137786913257566641 4126494853340184943174981)
                  ·
                    refine ⟨773717785001284676845309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4126494853340184943174981 773717785001284676845309)
                    ·
                      rfl

theorem cell23_4520430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_4520430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520430 prefixEnd_4520430 := by exact prefixLift 4520430
  have htrace : WordTrace (prefixWord ++ tailWord_4520430) baseStart_4520430 baseEnd_4520430 := by
    simpa [prefixWord, tailWord_4520430, baseEnd_4520430] using wordTrace_append hprefix tailTrace_4520430
  have hstable : (prefixWord ++ tailWord_4520430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520430).length < 2 ^ (prefixWord ++ tailWord_4520430).sum := by decide
  have hdescent : baseEnd_4520430 < baseStart_4520430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520453 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 6, 1, 3]
def baseStart_4520453 : Nat := 118140960795 + 4520453 * 2 ^ 59
def prefixEnd_4520453 : Nat := 4983230072969 + 3 ^ 40 * 4520453 * 2
def baseEnd_4520453 : Nat := 2321165165058907440548321

theorem tailTrace_4520453 : CollatzResearch.WordTrace tailWord_4520453 prefixEnd_4520453 2321165165058907440548321 := by
  unfold tailWord_4520453
  simp only [CollatzResearch.WordTrace]
  refine ⟨164874465892178287752910013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109916310594785525168606675 164874465892178287752910013)
  ·
    refine ⟨61827924709566857907341255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164874465892178287752910013 61827924709566857907341255)
    ·
      refine ⟨92741887064350286861011883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61827924709566857907341255 92741887064350286861011883)
      ·
        refine ⟨139112830596525430291517825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92741887064350286861011883 139112830596525430291517825)
        ·
          refine ⟨104334622947394072718638369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139112830596525430291517825 104334622947394072718638369)
          ·
            refine ⟨78250967210545554538978777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104334622947394072718638369 78250967210545554538978777)
            ·
              refine ⟨58688225407909165904234083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78250967210545554538978777 58688225407909165904234083)
              ·
                refine ⟨88032338111863748856351125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58688225407909165904234083 88032338111863748856351125)
                ·
                  refine ⟨4126515848993613227641459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88032338111863748856351125 4126515848993613227641459)
                  ·
                    refine ⟨6189773773490419841462189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4126515848993613227641459 6189773773490419841462189)
                    ·
                      refine ⟨2321165165058907440548321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6189773773490419841462189 2321165165058907440548321)
                      ·
                        rfl

theorem cell23_4520453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_4520453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520453 prefixEnd_4520453 := by exact prefixLift 4520453
  have htrace : WordTrace (prefixWord ++ tailWord_4520453) baseStart_4520453 baseEnd_4520453 := by
    simpa [prefixWord, tailWord_4520453, baseEnd_4520453] using wordTrace_append hprefix tailTrace_4520453
  have hstable : (prefixWord ++ tailWord_4520453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520453).length < 2 ^ (prefixWord ++ tailWord_4520453).sum := by decide
  have hdescent : baseEnd_4520453 < baseStart_4520453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520463 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 5, 3, 2]
def baseStart_4520463 : Nat := 118140960795 + 4520463 * 2 ^ 59
def prefixEnd_4520463 : Nat := 4983230072969 + 3 ^ 40 * 4520463 * 2
def baseEnd_4520463 : Nat := 2321170299865452401423275

theorem tailTrace_4520463 : CollatzResearch.WordTrace tailWord_4520463 prefixEnd_4520463 2321170299865452401423275 := by
  unfold tailWord_4520463
  simp only [CollatzResearch.WordTrace]
  refine ⟨164874830622142059460774043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109916553748094706307182695 164874830622142059460774043)
  ·
    refine ⟨247312245933213089191161065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164874830622142059460774043 247312245933213089191161065)
    ·
      refine ⟨185484184449909816893370799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247312245933213089191161065 185484184449909816893370799)
      ·
        refine ⟨278226276674864725340056199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185484184449909816893370799 278226276674864725340056199)
        ·
          refine ⟨417339415012297088010084299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278226276674864725340056199 417339415012297088010084299)
          ·
            refine ⟨626009122518445632015126449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417339415012297088010084299 626009122518445632015126449)
            ·
              refine ⟨469506841888834224011344837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626009122518445632015126449 469506841888834224011344837)
              ·
                refine ⟨88032532854156417002127157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 469506841888834224011344837 88032532854156417002127157)
                ·
                  refine ⟨8253049955077164093949421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88032532854156417002127157 8253049955077164093949421)
                  ·
                    refine ⟨3094893733153936535231033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8253049955077164093949421 3094893733153936535231033)
                    ·
                      refine ⟨2321170299865452401423275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094893733153936535231033 2321170299865452401423275)
                      ·
                        rfl

theorem cell23_4520463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 3, 2].length) (baseStart_4520463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520463 prefixEnd_4520463 := by exact prefixLift 4520463
  have htrace : WordTrace (prefixWord ++ tailWord_4520463) baseStart_4520463 baseEnd_4520463 := by
    simpa [prefixWord, tailWord_4520463, baseEnd_4520463] using wordTrace_append hprefix tailTrace_4520463
  have hstable : (prefixWord ++ tailWord_4520463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520463).length < 2 ^ (prefixWord ++ tailWord_4520463).sum := by decide
  have hdescent : baseEnd_4520463 < baseStart_4520463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520471 : List Nat := [1, 1, 3, 6, 1, 1, 1, 4, 1, 2, 2]
def baseStart_4520471 : Nat := 118140960795 + 4520471 * 2 ^ 59
def prefixEnd_4520471 : Nat := 4983230072969 + 3 ^ 40 * 4520471 * 2
def baseEnd_4520471 : Nat := 2321174407710688370123239

theorem tailTrace_4520471 : CollatzResearch.WordTrace tailWord_4520471 prefixEnd_4520471 2321174407710688370123239 := by
  unfold tailWord_4520471
  simp only [CollatzResearch.WordTrace]
  refine ⟨164875122406113076827065267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109916748270742051218043511 164875122406113076827065267)
  ·
    refine ⟨247312683609169615240597901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164875122406113076827065267 247312683609169615240597901)
    ·
      refine ⟨92742256353438605715224213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247312683609169615240597901 92742256353438605715224213)
      ·
        refine ⟨4347293266567434642901135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92742256353438605715224213 4347293266567434642901135)
        ·
          refine ⟨6520939899851151964351703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4347293266567434642901135 6520939899851151964351703)
          ·
            refine ⟨9781409849776727946527555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6520939899851151964351703 9781409849776727946527555)
            ·
              refine ⟨14672114774665091919791333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9781409849776727946527555 14672114774665091919791333)
              ·
                refine ⟨2751021520249704734960875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14672114774665091919791333 2751021520249704734960875)
                ·
                  refine ⟨4126532280374557102441313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2751021520249704734960875 4126532280374557102441313)
                  ·
                    refine ⟨3094899210280917826830985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4126532280374557102441313 3094899210280917826830985)
                    ·
                      refine ⟨2321174407710688370123239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094899210280917826830985 2321174407710688370123239)
                      ·
                        rfl

theorem cell23_4520471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_4520471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520471 prefixEnd_4520471 := by exact prefixLift 4520471
  have htrace : WordTrace (prefixWord ++ tailWord_4520471) baseStart_4520471 baseEnd_4520471 := by
    simpa [prefixWord, tailWord_4520471, baseEnd_4520471] using wordTrace_append hprefix tailTrace_4520471
  have hstable : (prefixWord ++ tailWord_4520471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520471).length < 2 ^ (prefixWord ++ tailWord_4520471).sum := by decide
  have hdescent : baseEnd_4520471 < baseStart_4520471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520496 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 5]
def baseStart_4520496 : Nat := 118140960795 + 4520496 * 2 ^ 59
def prefixEnd_4520496 : Nat := 4983230072969 + 3 ^ 40 * 4520496 * 2
def baseEnd_4520496 : Nat := 2321187244727050772310623

theorem tailTrace_4520496 : CollatzResearch.WordTrace tailWord_4520496 prefixEnd_4520496 2321187244727050772310623 := by
  unfold tailWord_4520496
  simp only [CollatzResearch.WordTrace]
  refine ⟨82438017115511253048362671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109917356154015004064483561 82438017115511253048362671)
  ·
    refine ⟨123657025673266879572544007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82438017115511253048362671 123657025673266879572544007)
    ·
      refine ⟨185485538509900319358816011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123657025673266879572544007 185485538509900319358816011)
      ·
        refine ⟨278228307764850479038224017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185485538509900319358816011 278228307764850479038224017)
        ·
          refine ⟨208671230823637859278668013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278228307764850479038224017 208671230823637859278668013)
          ·
            refine ⟨78251711558864197229500505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208671230823637859278668013 78251711558864197229500505)
            ·
              refine ⟨58688783669148147922125379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78251711558864197229500505 58688783669148147922125379)
              ·
                refine ⟨88033175503722221883188069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58688783669148147922125379 88033175503722221883188069)
                ·
                  refine ⟨16506220406947916603097763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88033175503722221883188069 16506220406947916603097763)
                  ·
                    refine ⟨24759330610421874904646645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16506220406947916603097763 24759330610421874904646645)
                    ·
                      refine ⟨2321187244727050772310623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24759330610421874904646645 2321187244727050772310623)
                      ·
                        rfl

theorem cell23_4520496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_4520496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520496 prefixEnd_4520496 := by exact prefixLift 4520496
  have htrace : WordTrace (prefixWord ++ tailWord_4520496) baseStart_4520496 baseEnd_4520496 := by
    simpa [prefixWord, tailWord_4520496, baseEnd_4520496] using wordTrace_append hprefix tailTrace_4520496
  have hstable : (prefixWord ++ tailWord_4520496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520496).length < 2 ^ (prefixWord ++ tailWord_4520496).sum := by decide
  have hdescent : baseEnd_4520496 < baseStart_4520496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520527 : List Nat := [1, 1, 2, 1, 1, 2, 7, 2, 2, 2, 2]
def baseStart_4520527 : Nat := 118140960795 + 4520527 * 2 ^ 59
def prefixEnd_4520527 : Nat := 4983230072969 + 3 ^ 40 * 4520527 * 2
def baseEnd_4520527 : Nat := 2321203162627340151022981

theorem tailTrace_4520527 : CollatzResearch.WordTrace tailWord_4520527 prefixEnd_4520527 2321203162627340151022981 := by
  unfold tailWord_4520527
  simp only [CollatzResearch.WordTrace]
  refine ⟨164877164893910198391103835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109918109929273465594069223 164877164893910198391103835)
  ·
    refine ⟨247315747340865297586655753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164877164893910198391103835 247315747340865297586655753)
    ·
      refine ⟨185486810505648973189991815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247315747340865297586655753 185486810505648973189991815)
      ·
        refine ⟨278230215758473459784987723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185486810505648973189991815 278230215758473459784987723)
        ·
          refine ⟨417345323637710189677481585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278230215758473459784987723 417345323637710189677481585)
          ·
            refine ⟨313008992728282642258111189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417345323637710189677481585 313008992728282642258111189)
            ·
              refine ⟨7336148267069124427924481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 313008992728282642258111189 7336148267069124427924481)
              ·
                refine ⟨5502111200301843320943361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7336148267069124427924481 5502111200301843320943361)
                ·
                  refine ⟨4126583400226382490707521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5502111200301843320943361 4126583400226382490707521)
                  ·
                    refine ⟨3094937550169786868030641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4126583400226382490707521 3094937550169786868030641)
                    ·
                      refine ⟨2321203162627340151022981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094937550169786868030641 2321203162627340151022981)
                      ·
                        rfl

theorem cell23_4520527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 2, 2].length) (baseStart_4520527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520527 prefixEnd_4520527 := by exact prefixLift 4520527
  have htrace : WordTrace (prefixWord ++ tailWord_4520527) baseStart_4520527 baseEnd_4520527 := by
    simpa [prefixWord, tailWord_4520527, baseEnd_4520527] using wordTrace_append hprefix tailTrace_4520527
  have hstable : (prefixWord ++ tailWord_4520527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520527).length < 2 ^ (prefixWord ++ tailWord_4520527).sum := by decide
  have hdescent : baseEnd_4520527 < baseStart_4520527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520580 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_4520580 : Nat := 118140960795 + 4520580 * 2 ^ 59
def prefixEnd_4520580 : Nat := 4983230072969 + 3 ^ 40 * 4520580 * 2
def baseEnd_4520580 : Nat := 773743459034009481220079

theorem tailTrace_4520580 : CollatzResearch.WordTrace tailWord_4520580 prefixEnd_4520580 773743459034009481220079 := by
  unfold tailWord_4520580
  simp only [CollatzResearch.WordTrace]
  refine ⟨82439548981359094221391597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109919398641812125628522129 82439548981359094221391597)
  ·
    refine ⟨30914830868009660333021849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82439548981359094221391597 30914830868009660333021849)
    ·
      refine ⟨23186123151007245249766387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30914830868009660333021849 23186123151007245249766387)
      ·
        refine ⟨34779184726510867874649581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23186123151007245249766387 34779184726510867874649581)
        ·
          refine ⟨13042194272441575452993593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34779184726510867874649581 13042194272441575452993593)
          ·
            refine ⟨9781645704331181589745195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13042194272441575452993593 9781645704331181589745195)
            ·
              refine ⟨14672468556496772384617793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9781645704331181589745195 14672468556496772384617793)
              ·
                refine ⟨11004351417372579288463345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14672468556496772384617793 11004351417372579288463345)
                ·
                  refine ⟨8253263563029434466347509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11004351417372579288463345 8253263563029434466347509)
                  ·
                    refine ⟨773743459034009481220079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8253263563029434466347509 773743459034009481220079)
                    ·
                      rfl

theorem cell23_4520580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_4520580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520580 prefixEnd_4520580 := by exact prefixLift 4520580
  have htrace : WordTrace (prefixWord ++ tailWord_4520580) baseStart_4520580 baseEnd_4520580 := by
    simpa [prefixWord, tailWord_4520580, baseEnd_4520580] using wordTrace_append hprefix tailTrace_4520580
  have hstable : (prefixWord ++ tailWord_4520580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520580).length < 2 ^ (prefixWord ++ tailWord_4520580).sum := by decide
  have hdescent : baseEnd_4520580 < baseStart_4520580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520600 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 1, 6, 2]
def baseStart_4520600 : Nat := 118140960795 + 4520600 * 2 ^ 59
def prefixEnd_4520600 : Nat := 4983230072969 + 3 ^ 40 * 4520600 * 2
def baseEnd_4520600 : Nat := 2321240646715118365410145

theorem tailTrace_4520600 : CollatzResearch.WordTrace tailWord_4520600 prefixEnd_4520600 2321240646715118365410145 := by
  unfold tailWord_4520600
  simp only [CollatzResearch.WordTrace]
  refine ⟨82439913711322865929255627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109919884948430487905674169 82439913711322865929255627)
  ·
    refine ⟨123659870566984298893883441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82439913711322865929255627 123659870566984298893883441)
    ·
      refine ⟨92744902925238224170412581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123659870566984298893883441 92744902925238224170412581)
      ·
        refine ⟨17389669298482167031952359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92744902925238224170412581 17389669298482167031952359)
        ·
          refine ⟨26084503947723250547928539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17389669298482167031952359 26084503947723250547928539)
          ·
            refine ⟨39126755921584875821892809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26084503947723250547928539 39126755921584875821892809)
            ·
              refine ⟨29345066941188656866419607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39126755921584875821892809 29345066941188656866419607)
              ·
                refine ⟨44017600411782985299629411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29345066941188656866419607 44017600411782985299629411)
                ·
                  refine ⟨66026400617674477949444117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44017600411782985299629411 66026400617674477949444117)
                  ·
                    refine ⟨3094987528953491153880193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66026400617674477949444117 3094987528953491153880193)
                    ·
                      refine ⟨2321240646715118365410145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3094987528953491153880193 2321240646715118365410145)
                      ·
                        rfl

theorem cell23_4520600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_4520600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520600 prefixEnd_4520600 := by exact prefixLift 4520600
  have htrace : WordTrace (prefixWord ++ tailWord_4520600) baseStart_4520600 baseEnd_4520600 := by
    simpa [prefixWord, tailWord_4520600, baseEnd_4520600] using wordTrace_append hprefix tailTrace_4520600
  have hstable : (prefixWord ++ tailWord_4520600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520600).length < 2 ^ (prefixWord ++ tailWord_4520600).sum := by decide
  have hdescent : baseEnd_4520600 < baseStart_4520600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520640 : List Nat := [2, 1, 1, 2, 4, 3, 2, 2, 6]
def baseStart_4520640 : Nat := 118140960795 + 4520640 * 2 ^ 59
def prefixEnd_4520640 : Nat := 4983230072969 + 3 ^ 40 * 4520640 * 2
def baseEnd_4520640 : Nat := 257917909549033134323329

theorem tailTrace_4520640 : CollatzResearch.WordTrace tailWord_4520640 prefixEnd_4520640 257917909549033134323329 := by
  unfold tailWord_4520640
  simp only [CollatzResearch.WordTrace]
  refine ⟨82440643171250409344983687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109920857561667212459978249 82440643171250409344983687)
  ·
    refine ⟨123660964756875614017475531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82440643171250409344983687 123660964756875614017475531)
    ·
      refine ⟨185491447135313421026213297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123660964756875614017475531 185491447135313421026213297)
      ·
        refine ⟨139118585351485065769659973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185491447135313421026213297 139118585351485065769659973)
        ·
          refine ⟨26084734753403449831811245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139118585351485065769659973 26084734753403449831811245)
          ·
            refine ⟨9781775532526293686929217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26084734753403449831811245 9781775532526293686929217)
            ·
              refine ⟨7336331649394720265196913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9781775532526293686929217 7336331649394720265196913)
              ·
                refine ⟨5502248737046040198897685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7336331649394720265196913 5502248737046040198897685)
                ·
                  refine ⟨257917909549033134323329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5502248737046040198897685 257917909549033134323329)
                  ·
                    rfl

theorem cell23_4520640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 6].length) (baseStart_4520640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520640 prefixEnd_4520640 := by exact prefixLift 4520640
  have htrace : WordTrace (prefixWord ++ tailWord_4520640) baseStart_4520640 baseEnd_4520640 := by
    simpa [prefixWord, tailWord_4520640, baseEnd_4520640] using wordTrace_append hprefix tailTrace_4520640
  have hstable : (prefixWord ++ tailWord_4520640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520640).length < 2 ^ (prefixWord ++ tailWord_4520640).sum := by decide
  have hdescent : baseEnd_4520640 < baseStart_4520640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520644 : List Nat := [2, 3, 3, 1, 1, 3, 1, 4, 1, 4]
def baseStart_4520644 : Nat := 118140960795 + 4520644 * 2 ^ 59
def prefixEnd_4520644 : Nat := 4983230072969 + 3 ^ 40 * 4520644 * 2
def baseEnd_4520644 : Nat := 773754413287972064419981

theorem tailTrace_4520644 : CollatzResearch.WordTrace tailWord_4520644 prefixEnd_4520644 773754413287972064419981 := by
  unfold tailWord_4520644
  simp only [CollatzResearch.WordTrace]
  refine ⟨82440716117243163686556493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109920954822990884915408657 82440716117243163686556493)
  ·
    refine ⟨30915268543966186382458685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82440716117243163686556493 30915268543966186382458685)
    ·
      refine ⟨11593225703987319893422007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30915268543966186382458685 11593225703987319893422007)
      ·
        refine ⟨17389838555980979840133011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11593225703987319893422007 17389838555980979840133011)
        ·
          refine ⟨26084757833971469760199517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17389838555980979840133011 26084757833971469760199517)
          ·
            refine ⟨9781784187739301160074819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26084757833971469760199517 9781784187739301160074819)
            ·
              refine ⟨14672676281608951740112229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9781784187739301160074819 14672676281608951740112229)
              ·
                refine ⟨2751126802801678451271043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14672676281608951740112229 2751126802801678451271043)
                ·
                  refine ⟨4126690204202517676906565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2751126802801678451271043 4126690204202517676906565)
                  ·
                    refine ⟨773754413287972064419981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4126690204202517676906565 773754413287972064419981)
                    ·
                      rfl

theorem cell23_4520644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_4520644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520644 prefixEnd_4520644 := by exact prefixLift 4520644
  have htrace : WordTrace (prefixWord ++ tailWord_4520644) baseStart_4520644 baseEnd_4520644 := by
    simpa [prefixWord, tailWord_4520644, baseEnd_4520644] using wordTrace_append hprefix tailTrace_4520644
  have hstable : (prefixWord ++ tailWord_4520644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520644).length < 2 ^ (prefixWord ++ tailWord_4520644).sum := by decide
  have hdescent : baseEnd_4520644 < baseStart_4520644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520677 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 1, 5, 2]
def baseStart_4520677 : Nat := 118140960795 + 4520677 * 2 ^ 59
def prefixEnd_4520677 : Nat := 4983230072969 + 3 ^ 40 * 4520677 * 2
def baseEnd_4520677 : Nat := 2321280184725514564147291

theorem tailTrace_4520677 : CollatzResearch.WordTrace tailWord_4520677 prefixEnd_4520677 2321280184725514564147291 := by
  unfold tailWord_4520677
  simp only [CollatzResearch.WordTrace]
  refine ⟨164882635843366774009064285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109921757228911182672709523 164882635843366774009064285)
  ·
    refine ⟨61830988441262540253399107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164882635843366774009064285 61830988441262540253399107)
    ·
      refine ⟨92746482661893810380098661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61830988441262540253399107 92746482661893810380098661)
      ·
        refine ⟨17389965499105089446268499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92746482661893810380098661 17389965499105089446268499)
        ·
          refine ⟨26084948248657634169402749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17389965499105089446268499 26084948248657634169402749)
          ·
            refine ⟨9781855593246612813526031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26084948248657634169402749 9781855593246612813526031)
            ·
              refine ⟨14672783389869919220289047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9781855593246612813526031 14672783389869919220289047)
              ·
                refine ⟨22009175084804878830433571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14672783389869919220289047 22009175084804878830433571)
                ·
                  refine ⟨33013762627207318245650357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22009175084804878830433571 33013762627207318245650357)
                  ·
                    refine ⟨3095040246300686085529721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33013762627207318245650357 3095040246300686085529721)
                    ·
                      refine ⟨2321280184725514564147291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3095040246300686085529721 2321280184725514564147291)
                      ·
                        rfl

theorem cell23_4520677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_4520677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520677 prefixEnd_4520677 := by exact prefixLift 4520677
  have htrace : WordTrace (prefixWord ++ tailWord_4520677) baseStart_4520677 baseEnd_4520677 := by
    simpa [prefixWord, tailWord_4520677, baseEnd_4520677] using wordTrace_append hprefix tailTrace_4520677
  have hstable : (prefixWord ++ tailWord_4520677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520677).length < 2 ^ (prefixWord ++ tailWord_4520677).sum := by decide
  have hdescent : baseEnd_4520677 < baseStart_4520677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520687 : List Nat := [1, 1, 2, 1, 5, 2, 4, 1, 1, 5]
def baseStart_4520687 : Nat := 118140960795 + 4520687 * 2 ^ 59
def prefixEnd_4520687 : Nat := 4983230072969 + 3 ^ 40 * 4520687 * 2
def baseEnd_4520687 : Nat := 773761773177353175007415

theorem tailTrace_4520687 : CollatzResearch.WordTrace tailWord_4520687 prefixEnd_4520687 773761773177353175007415 := by
  unfold tailWord_4520687
  simp only [CollatzResearch.WordTrace]
  refine ⟨164883000573330545716928315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109922000382220363811285543 164883000573330545716928315)
  ·
    refine ⟨247324500859995818575392473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164883000573330545716928315 247324500859995818575392473)
    ·
      refine ⟨185493375644996863931544355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247324500859995818575392473 185493375644996863931544355)
      ·
        refine ⟨278240063467495295897316533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185493375644996863931544355 278240063467495295897316533)
        ·
          refine ⟨26085005950077683990373425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 278240063467495295897316533 26085005950077683990373425)
          ·
            refine ⟨19563754462558262992780069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26085005950077683990373425 19563754462558262992780069)
            ·
              refine ⟨3668203961729674311146263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19563754462558262992780069 3668203961729674311146263)
              ·
                refine ⟨5502305942594511466719395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3668203961729674311146263 5502305942594511466719395)
                ·
                  refine ⟨8253458913891767200079093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5502305942594511466719395 8253458913891767200079093)
                  ·
                    refine ⟨773761773177353175007415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8253458913891767200079093 773761773177353175007415)
                    ·
                      rfl

theorem cell23_4520687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 1, 5].length) (baseStart_4520687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520687 prefixEnd_4520687 := by exact prefixLift 4520687
  have htrace : WordTrace (prefixWord ++ tailWord_4520687) baseStart_4520687 baseEnd_4520687 := by
    simpa [prefixWord, tailWord_4520687, baseEnd_4520687] using wordTrace_append hprefix tailTrace_4520687
  have hstable : (prefixWord ++ tailWord_4520687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520687).length < 2 ^ (prefixWord ++ tailWord_4520687).sum := by decide
  have hdescent : baseEnd_4520687 < baseStart_4520687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520703 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 6]
def baseStart_4520703 : Nat := 118140960795 + 4520703 * 2 ^ 59
def prefixEnd_4520703 : Nat := 4983230072969 + 3 ^ 40 * 4520703 * 2
def baseEnd_4520703 : Nat := 2321293535222531462422171

theorem tailTrace_4520703 : CollatzResearch.WordTrace tailWord_4520703 prefixEnd_4520703 2321293535222531462422171 := by
  unfold tailWord_4520703
  simp only [CollatzResearch.WordTrace]
  refine ⟨164883584141272580449510763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109922389427515053633007175 164883584141272580449510763)
  ·
    refine ⟨247325376211908870674266145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164883584141272580449510763 247325376211908870674266145)
    ·
      refine ⟨185494032158931653005699609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247325376211908870674266145 185494032158931653005699609)
      ·
        refine ⟨139120524119198739754274707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185494032158931653005699609 139120524119198739754274707)
        ·
          refine ⟨208680786178798109631412061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139120524119198739754274707 208680786178798109631412061)
          ·
            refine ⟨78255294817049291111779523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208680786178798109631412061 78255294817049291111779523)
            ·
              refine ⟨117382942225573936667669285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78255294817049291111779523 117382942225573936667669285)
              ·
                refine ⟨22009301667295113125187991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117382942225573936667669285 22009301667295113125187991)
                ·
                  refine ⟨33013952500942669687781987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22009301667295113125187991 33013952500942669687781987)
                  ·
                    refine ⟨49520928751414004531672981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33013952500942669687781987 49520928751414004531672981)
                    ·
                      refine ⟨2321293535222531462422171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49520928751414004531672981 2321293535222531462422171)
                      ·
                        rfl

theorem cell23_4520703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_4520703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520703 prefixEnd_4520703 := by exact prefixLift 4520703
  have htrace : WordTrace (prefixWord ++ tailWord_4520703) baseStart_4520703 baseEnd_4520703 := by
    simpa [prefixWord, tailWord_4520703, baseEnd_4520703] using wordTrace_append hprefix tailTrace_4520703
  have hstable : (prefixWord ++ tailWord_4520703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520703).length < 2 ^ (prefixWord ++ tailWord_4520703).sum := by decide
  have hdescent : baseEnd_4520703 < baseStart_4520703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520783 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 9]
def baseStart_4520783 : Nat := 118140960795 + 4520783 * 2 ^ 59
def prefixEnd_4520783 : Nat := 4983230072969 + 3 ^ 40 * 4520783 * 2
def baseEnd_4520783 : Nat := 2321334613674891149421803

theorem tailTrace_4520783 : CollatzResearch.WordTrace tailWord_4520783 prefixEnd_4520783 2321334613674891149421803 := by
  unfold tailWord_4520783
  simp only [CollatzResearch.WordTrace]
  refine ⟨164886501980982754112423003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109924334653988502741615335 164886501980982754112423003)
  ·
    refine ⟨247329752971474131168634505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164886501980982754112423003 247329752971474131168634505)
    ·
      refine ⟨185497314728605598376475879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247329752971474131168634505 185497314728605598376475879)
      ·
        refine ⟨278245972092908397564713819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185497314728605598376475879 278245972092908397564713819)
        ·
          refine ⟨417368958139362596347070729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278245972092908397564713819 417368958139362596347070729)
          ·
            refine ⟨313026718604521947260303047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417368958139362596347070729 313026718604521947260303047)
            ·
              refine ⟨469540077906782920890454571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313026718604521947260303047 469540077906782920890454571)
              ·
                refine ⟨704310116860174381335681857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469540077906782920890454571 704310116860174381335681857)
                ·
                  refine ⟨528232587645130786001761393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 704310116860174381335681857 528232587645130786001761393)
                  ·
                    refine ⟨396174440733848089501321045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 528232587645130786001761393 396174440733848089501321045)
                    ·
                      refine ⟨2321334613674891149421803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 396174440733848089501321045 2321334613674891149421803)
                      ·
                        rfl

theorem cell23_4520783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_4520783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520783 prefixEnd_4520783 := by exact prefixLift 4520783
  have htrace : WordTrace (prefixWord ++ tailWord_4520783) baseStart_4520783 baseEnd_4520783 := by
    simpa [prefixWord, tailWord_4520783, baseEnd_4520783] using wordTrace_append hprefix tailTrace_4520783
  have hstable : (prefixWord ++ tailWord_4520783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520783).length < 2 ^ (prefixWord ++ tailWord_4520783).sum := by decide
  have hdescent : baseEnd_4520783 < baseStart_4520783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520784 : List Nat := [2, 1, 1, 1, 1, 4, 5, 2, 1, 3, 2]
def baseStart_4520784 : Nat := 118140960795 + 4520784 * 2 ^ 59
def prefixEnd_4520784 : Nat := 4983230072969 + 3 ^ 40 * 4520784 * 2
def baseEnd_4520784 : Nat := 2321335127155545645509299

theorem tailTrace_4520784 : CollatzResearch.WordTrace tailWord_4520784 prefixEnd_4520784 2321335127155545645509299 := by
  unfold tailWord_4520784
  simp only [CollatzResearch.WordTrace]
  refine ⟨82443269226989565641604703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109924358969319420855472937 82443269226989565641604703)
  ·
    refine ⟨123664903840484348462407055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82443269226989565641604703 123664903840484348462407055)
    ·
      refine ⟨185497355760726522693610583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123664903840484348462407055 185497355760726522693610583)
      ·
        refine ⟨278246033641089784040415875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185497355760726522693610583 278246033641089784040415875)
        ·
          refine ⟨417369050461634676060623813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278246033641089784040415875 417369050461634676060623813)
          ·
            refine ⟨78256696961556501761366965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 417369050461634676060623813 78256696961556501761366965)
            ·
              refine ⟨7336565340145922040128153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78256696961556501761366965 7336565340145922040128153)
              ·
                refine ⟨5502424005109441530096115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7336565340145922040128153 5502424005109441530096115)
                ·
                  refine ⟨8253636007664162295144173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5502424005109441530096115 8253636007664162295144173)
                  ·
                    refine ⟨3095113502874060860679065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8253636007664162295144173 3095113502874060860679065)
                    ·
                      refine ⟨2321335127155545645509299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3095113502874060860679065 2321335127155545645509299)
                      ·
                        rfl

theorem cell23_4520784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 1, 3, 2].length) (baseStart_4520784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520784 prefixEnd_4520784 := by exact prefixLift 4520784
  have htrace : WordTrace (prefixWord ++ tailWord_4520784) baseStart_4520784 baseEnd_4520784 := by
    simpa [prefixWord, tailWord_4520784, baseEnd_4520784] using wordTrace_append hprefix tailTrace_4520784
  have hstable : (prefixWord ++ tailWord_4520784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520784).length < 2 ^ (prefixWord ++ tailWord_4520784).sum := by decide
  have hdescent : baseEnd_4520784 < baseStart_4520784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520800 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 5]
def baseStart_4520800 : Nat := 118140960795 + 4520800 * 2 ^ 59
def prefixEnd_4520800 : Nat := 4983230072969 + 3 ^ 40 * 4520800 * 2
def baseEnd_4520800 : Nat := 2321343342846017582909225

theorem tailTrace_4520800 : CollatzResearch.WordTrace tailWord_4520800 prefixEnd_4520800 2321343342846017582909225 := by
  unfold tailWord_4520800
  simp only [CollatzResearch.WordTrace]
  refine ⟨82443561010960583007895927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109924748014614110677194569 82443561010960583007895927)
  ·
    refine ⟨123665341516440874511843891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82443561010960583007895927 123665341516440874511843891)
    ·
      refine ⟨185498012274661311767765837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123665341516440874511843891 185498012274661311767765837)
      ·
        refine ⟨69561754602997991912912189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185498012274661311767765837 69561754602997991912912189)
        ·
          refine ⟨26085657976124246967342071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69561754602997991912912189 26085657976124246967342071)
          ·
            refine ⟨39128486964186370451013107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26085657976124246967342071 39128486964186370451013107)
            ·
              refine ⟨58692730446279555676519661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39128486964186370451013107 58692730446279555676519661)
              ·
                refine ⟨22009773917354833378694873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58692730446279555676519661 22009773917354833378694873)
                ·
                  refine ⟨16507330438016125034021155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22009773917354833378694873 16507330438016125034021155)
                  ·
                    refine ⟨24760995657024187551031733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16507330438016125034021155 24760995657024187551031733)
                    ·
                      refine ⟨2321343342846017582909225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24760995657024187551031733 2321343342846017582909225)
                      ·
                        rfl

theorem cell23_4520800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_4520800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520800 prefixEnd_4520800 := by exact prefixLift 4520800
  have htrace : WordTrace (prefixWord ++ tailWord_4520800) baseStart_4520800 baseEnd_4520800 := by
    simpa [prefixWord, tailWord_4520800, baseEnd_4520800] using wordTrace_append hprefix tailTrace_4520800
  have hstable : (prefixWord ++ tailWord_4520800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520800).length < 2 ^ (prefixWord ++ tailWord_4520800).sum := by decide
  have hdescent : baseEnd_4520800 < baseStart_4520800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520884 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_4520884 : Nat := 118140960795 + 4520884 * 2 ^ 59
def prefixEnd_4520884 : Nat := 4983230072969 + 3 ^ 40 * 4520884 * 2
def baseEnd_4520884 : Nat := 773795491740331751419613

theorem tailTrace_4520884 : CollatzResearch.WordTrace tailWord_4520884 prefixEnd_4520884 773795491740331751419613 := by
  unfold tailWord_4520884
  simp only [CollatzResearch.WordTrace]
  refine ⟨82445092876808424180924853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109926790502411232241233137 82445092876808424180924853)
  ·
    refine ⟨7729227457200789766961705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82445092876808424180924853 7729227457200789766961705)
    ·
      refine ⟨5796920592900592325221279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7729227457200789766961705 5796920592900592325221279)
      ·
        refine ⟨8695380889350888487831919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5796920592900592325221279 8695380889350888487831919)
        ·
          refine ⟨13043071334026332731747879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8695380889350888487831919 13043071334026332731747879)
          ·
            refine ⟨19564607001039499097621819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13043071334026332731747879 19564607001039499097621819)
            ·
              refine ⟨29346910501559248646432729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19564607001039499097621819 29346910501559248646432729)
              ·
                refine ⟨22010182876169436484824547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29346910501559248646432729 22010182876169436484824547)
                ·
                  refine ⟨33015274314254154727236821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22010182876169436484824547 33015274314254154727236821)
                  ·
                    refine ⟨773795491740331751419613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33015274314254154727236821 773795491740331751419613)
                    ·
                      rfl

theorem cell23_4520884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_4520884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520884 prefixEnd_4520884 := by exact prefixLift 4520884
  have htrace : WordTrace (prefixWord ++ tailWord_4520884) baseStart_4520884 baseEnd_4520884 := by
    simpa [prefixWord, tailWord_4520884, baseEnd_4520884] using wordTrace_append hprefix tailTrace_4520884
  have hstable : (prefixWord ++ tailWord_4520884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520884).length < 2 ^ (prefixWord ++ tailWord_4520884).sum := by decide
  have hdescent : baseEnd_4520884 < baseStart_4520884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520907 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 3]
def baseStart_4520907 : Nat := 118140960795 + 4520907 * 2 ^ 59
def prefixEnd_4520907 : Nat := 4983230072969 + 3 ^ 40 * 4520907 * 2
def baseEnd_4520907 : Nat := 2321398285276048664271233

theorem tailTrace_4520907 : CollatzResearch.WordTrace tailWord_4520907 prefixEnd_4520907 2321398285276048664271233 := by
  unfold tailWord_4520907
  simp only [CollatzResearch.WordTrace]
  refine ⟨164891024632533523289936975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109927349755022348859957983 164891024632533523289936975)
  ·
    refine ⟨247336536948800284934905463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164891024632533523289936975 247336536948800284934905463)
    ·
      refine ⟨371004805423200427402358195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247336536948800284934905463 371004805423200427402358195)
      ·
        refine ⟨556507208134800641103537293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371004805423200427402358195 556507208134800641103537293)
        ·
          refine ⟨208690203050550240413826485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 556507208134800641103537293 208690203050550240413826485)
          ·
            refine ⟨19564706535989085038796233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 208690203050550240413826485 19564706535989085038796233)
            ·
              refine ⟨14673529901991813779097175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19564706535989085038796233 14673529901991813779097175)
              ·
                refine ⟨22010294852987720668645763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14673529901991813779097175 22010294852987720668645763)
                ·
                  refine ⟨33015442279481581002968645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22010294852987720668645763 33015442279481581002968645)
                  ·
                    refine ⟨6190395427402796438056621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33015442279481581002968645 6190395427402796438056621)
                    ·
                      refine ⟨2321398285276048664271233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6190395427402796438056621 2321398285276048664271233)
                      ·
                        rfl

theorem cell23_4520907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 3].length) (baseStart_4520907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520907 prefixEnd_4520907 := by exact prefixLift 4520907
  have htrace : WordTrace (prefixWord ++ tailWord_4520907) baseStart_4520907 baseEnd_4520907 := by
    simpa [prefixWord, tailWord_4520907, baseEnd_4520907] using wordTrace_append hprefix tailTrace_4520907
  have hstable : (prefixWord ++ tailWord_4520907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520907).length < 2 ^ (prefixWord ++ tailWord_4520907).sum := by decide
  have hdescent : baseEnd_4520907 < baseStart_4520907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520940 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 1, 11]
def baseStart_4520940 : Nat := 118140960795 + 4520940 * 2 ^ 59
def prefixEnd_4520940 : Nat := 4983230072969 + 3 ^ 40 * 4520940 * 2
def baseEnd_4520940 : Nat := 773805076712549011719527

theorem tailTrace_4520940 : CollatzResearch.WordTrace tailWord_4520940 prefixEnd_4520940 773805076712549011719527 := by
  unfold tailWord_4520940
  simp only [CollatzResearch.WordTrace]
  refine ⟨82446114120706984962944137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109928152160942646617258849 82446114120706984962944137)
  ·
    refine ⟨61834585590530238722208103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82446114120706984962944137 61834585590530238722208103)
    ·
      refine ⟨92751878385795358083312155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61834585590530238722208103 92751878385795358083312155)
      ·
        refine ⟨139127817578693037124968233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92751878385795358083312155 139127817578693037124968233)
        ·
          refine ⟨104345863184019777843726175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139127817578693037124968233 104345863184019777843726175)
          ·
            refine ⟨156518794776029666765589263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104345863184019777843726175 156518794776029666765589263)
            ·
              refine ⟨234778192164044500148383895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156518794776029666765589263 234778192164044500148383895)
              ·
                refine ⟨352167288246066750222575843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234778192164044500148383895 352167288246066750222575843)
                ·
                  refine ⟨528250932369100125333863765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352167288246066750222575843 528250932369100125333863765)
                  ·
                    refine ⟨773805076712549011719527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 528250932369100125333863765 773805076712549011719527)
                    ·
                      rfl

theorem cell23_4520940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_4520940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520940 prefixEnd_4520940 := by exact prefixLift 4520940
  have htrace : WordTrace (prefixWord ++ tailWord_4520940) baseStart_4520940 baseEnd_4520940 := by
    simpa [prefixWord, tailWord_4520940, baseEnd_4520940] using wordTrace_append hprefix tailTrace_4520940
  have hstable : (prefixWord ++ tailWord_4520940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520940).length < 2 ^ (prefixWord ++ tailWord_4520940).sum := by decide
  have hdescent : baseEnd_4520940 < baseStart_4520940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520954 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3]
def baseStart_4520954 : Nat := 118140960795 + 4520954 * 2 ^ 59
def prefixEnd_4520954 : Nat := 4983230072969 + 3 ^ 40 * 4520954 * 2
def baseEnd_4520954 : Nat := 2321422418866809980383517

theorem tailTrace_4520954 : CollatzResearch.WordTrace tailWord_4520954 prefixEnd_4520954 2321422418866809980383517 := by
  unfold tailWord_4520954
  simp only [CollatzResearch.WordTrace]
  refine ⟨41223184715840812579224479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109928492575575500211265277 41223184715840812579224479)
  ·
    refine ⟨61834777073761218868836719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41223184715840812579224479 61834777073761218868836719)
    ·
      refine ⟨92752165610641828303255079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61834777073761218868836719 92752165610641828303255079)
      ·
        refine ⟨139128248415962742454882619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92752165610641828303255079 139128248415962742454882619)
        ·
          refine ⟨208692372623944113682323929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139128248415962742454882619 208692372623944113682323929)
          ·
            refine ⟨156519279467958085261742947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208692372623944113682323929 156519279467958085261742947)
            ·
              refine ⟨234778919201937127892614421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156519279467958085261742947 234778919201937127892614421)
              ·
                refine ⟨11005261837590802869966301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 234778919201937127892614421 11005261837590802869966301)
                ·
                  refine ⟨4126973189096551076237363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11005261837590802869966301 4126973189096551076237363)
                  ·
                    refine ⟨6190459783644826614356045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4126973189096551076237363 6190459783644826614356045)
                    ·
                      refine ⟨2321422418866809980383517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6190459783644826614356045 2321422418866809980383517)
                      ·
                        rfl

theorem cell23_4520954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_4520954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520954 prefixEnd_4520954 := by exact prefixLift 4520954
  have htrace : WordTrace (prefixWord ++ tailWord_4520954) baseStart_4520954 baseEnd_4520954 := by
    simpa [prefixWord, tailWord_4520954, baseEnd_4520954] using wordTrace_append hprefix tailTrace_4520954
  have hstable : (prefixWord ++ tailWord_4520954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520954).length < 2 ^ (prefixWord ++ tailWord_4520954).sum := by decide
  have hdescent : baseEnd_4520954 < baseStart_4520954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520958 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_4520958 : Nat := 118140960795 + 4520958 * 2 ^ 59
def prefixEnd_4520958 : Nat := 4983230072969 + 3 ^ 40 * 4520958 * 2
def baseEnd_4520958 : Nat := 2321424472789427964733499

theorem tailTrace_4520958 : CollatzResearch.WordTrace tailWord_4520958 prefixEnd_4520958 2321424472789427964733499 := by
  unfold tailWord_4520958
  simp only [CollatzResearch.WordTrace]
  refine ⟨20611610594418594875005441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109928589836899172666695685 20611610594418594875005441)
  ·
    refine ⟨15458707945813946156254081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20611610594418594875005441 15458707945813946156254081)
    ·
      refine ⟨11594030959360459617190561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15458707945813946156254081 11594030959360459617190561)
      ·
        refine ⟨8695523219520344712892921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11594030959360459617190561 8695523219520344712892921)
        ·
          refine ⟨6521642414640258534669691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8695523219520344712892921 6521642414640258534669691)
          ·
            refine ⟨9782463621960387802004537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6521642414640258534669691 9782463621960387802004537)
            ·
              refine ⟨7336847716470290851503403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9782463621960387802004537 7336847716470290851503403)
              ·
                refine ⟨11005271574705436277255105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7336847716470290851503403 11005271574705436277255105)
                ·
                  refine ⟨8253953681029077207941329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11005271574705436277255105 8253953681029077207941329)
                  ·
                    refine ⟨6190465260771807905955997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8253953681029077207941329 6190465260771807905955997)
                    ·
                      refine ⟨2321424472789427964733499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6190465260771807905955997 2321424472789427964733499)
                      ·
                        rfl

theorem cell23_4520958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_4520958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520958 prefixEnd_4520958 := by exact prefixLift 4520958
  have htrace : WordTrace (prefixWord ++ tailWord_4520958) baseStart_4520958 baseEnd_4520958 := by
    simpa [prefixWord, tailWord_4520958, baseEnd_4520958] using wordTrace_append hprefix tailTrace_4520958
  have hstable : (prefixWord ++ tailWord_4520958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520958).length < 2 ^ (prefixWord ++ tailWord_4520958).sum := by decide
  have hdescent : baseEnd_4520958 < baseStart_4520958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520981 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 2, 3, 2]
def baseStart_4520981 : Nat := 118140960795 + 4520981 * 2 ^ 59
def prefixEnd_4520981 : Nat := 4983230072969 + 3 ^ 40 * 4520981 * 2
def baseEnd_4520981 : Nat := 2321436282844481374745893

theorem tailTrace_4520981 : CollatzResearch.WordTrace tailWord_4520981 prefixEnd_4520981 2321436282844481374745893 := by
  unfold tailWord_4520981
  simp only [CollatzResearch.WordTrace]
  refine ⟨164893723634265433928130797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109929149089510289285420531 164893723634265433928130797)
  ·
    refine ⟨61835146362849537723049049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164893723634265433928130797 61835146362849537723049049)
    ·
      refine ⟨46376359772137153292286787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61835146362849537723049049 46376359772137153292286787)
      ·
        refine ⟨69564539658205729938430181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46376359772137153292286787 69564539658205729938430181)
        ·
          refine ⟨13043351185913574363455659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69564539658205729938430181 13043351185913574363455659)
          ·
            refine ⟨19565026778870361545183489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13043351185913574363455659 19565026778870361545183489)
            ·
              refine ⟨14673770084152771158887617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19565026778870361545183489 14673770084152771158887617)
              ·
                refine ⟨11005327563114578369165713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14673770084152771158887617 11005327563114578369165713)
                ·
                  refine ⟨8253995672335933776874285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11005327563114578369165713 8253995672335933776874285)
                  ·
                    refine ⟨3095248377125975166327857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8253995672335933776874285 3095248377125975166327857)
                    ·
                      refine ⟨2321436282844481374745893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3095248377125975166327857 2321436282844481374745893)
                      ·
                        rfl

theorem cell23_4520981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_4520981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520981 prefixEnd_4520981 := by exact prefixLift 4520981
  have htrace : WordTrace (prefixWord ++ tailWord_4520981) baseStart_4520981 baseEnd_4520981 := by
    simpa [prefixWord, tailWord_4520981, baseEnd_4520981] using wordTrace_append hprefix tailTrace_4520981
  have hstable : (prefixWord ++ tailWord_4520981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520981).length < 2 ^ (prefixWord ++ tailWord_4520981).sum := by decide
  have hdescent : baseEnd_4520981 < baseStart_4520981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520987 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 8, 4]
def baseStart_4520987 : Nat := 118140960795 + 4520987 * 2 ^ 59
def prefixEnd_4520987 : Nat := 4983230072969 + 3 ^ 40 * 4520987 * 2
def baseEnd_4520987 : Nat := 773813121242802783756955

theorem tailTrace_4520987 : CollatzResearch.WordTrace tailWord_4520987 prefixEnd_4520987 773813121242802783756955 := by
  unfold tailWord_4520987
  simp only [CollatzResearch.WordTrace]
  refine ⟨164893942472243696952849215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109929294981495797968566143 164893942472243696952849215)
  ·
    refine ⟨247340913708365545429273823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164893942472243696952849215 247340913708365545429273823)
    ·
      refine ⟨371011370562548318143910735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247340913708365545429273823 371011370562548318143910735)
      ·
        refine ⟨556517055843822477215866103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371011370562548318143910735 556517055843822477215866103)
        ·
          refine ⟨834775583765733715823799155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556517055843822477215866103 834775583765733715823799155)
          ·
            refine ⟨1252163375648600573735698733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834775583765733715823799155 1252163375648600573735698733)
            ·
              refine ⟨469561265868225215150887025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1252163375648600573735698733 469561265868225215150887025)
              ·
                refine ⟨352170949401168911363165269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469561265868225215150887025 352170949401168911363165269)
                ·
                  refine ⟨4127003313294948180037093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 352170949401168911363165269 4127003313294948180037093)
                  ·
                    refine ⟨773813121242802783756955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4127003313294948180037093 773813121242802783756955)
                    ·
                      rfl

theorem cell23_4520987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 4].length) (baseStart_4520987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520987 prefixEnd_4520987 := by exact prefixLift 4520987
  have htrace : WordTrace (prefixWord ++ tailWord_4520987) baseStart_4520987 baseEnd_4520987 := by
    simpa [prefixWord, tailWord_4520987, baseEnd_4520987] using wordTrace_append hprefix tailTrace_4520987
  have hstable : (prefixWord ++ tailWord_4520987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520987).length < 2 ^ (prefixWord ++ tailWord_4520987).sum := by decide
  have hdescent : baseEnd_4520987 < baseStart_4520987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520994 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_4520994 : Nat := 118140960795 + 4520994 * 2 ^ 59
def prefixEnd_4520994 : Nat := 4983230072969 + 3 ^ 40 * 4520994 * 2
def baseEnd_4520994 : Nat := 2321442958092989823883333

theorem tailTrace_4520994 : CollatzResearch.WordTrace tailWord_4520994 prefixEnd_4520994 2321442958092989823883333 := by
  unfold tailWord_4520994
  simp only [CollatzResearch.WordTrace]
  refine ⟨41223549445804584287088509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109929465188812224765569357 41223549445804584287088509)
  ·
    refine ⟨15458831042176719107658191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41223549445804584287088509 15458831042176719107658191)
    ·
      refine ⟨23188246563265078661487287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15458831042176719107658191 23188246563265078661487287)
      ·
        refine ⟨34782369844897617992230931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23188246563265078661487287 34782369844897617992230931)
        ·
          refine ⟨52173554767346426988346397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34782369844897617992230931 52173554767346426988346397)
          ·
            refine ⟨19565083037754910120629899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52173554767346426988346397 19565083037754910120629899)
            ·
              refine ⟨29347624556632365180944849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19565083037754910120629899 29347624556632365180944849)
              ·
                refine ⟨22010718417474273885708637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29347624556632365180944849 22010718417474273885708637)
                ·
                  refine ⟨8254019406552852707140739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22010718417474273885708637 8254019406552852707140739)
                  ·
                    refine ⟨12381029109829279060711109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8254019406552852707140739 12381029109829279060711109)
                    ·
                      refine ⟨2321442958092989823883333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12381029109829279060711109 2321442958092989823883333)
                      ·
                        rfl

theorem cell23_4520994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_4520994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520994 prefixEnd_4520994 := by exact prefixLift 4520994
  have htrace : WordTrace (prefixWord ++ tailWord_4520994) baseStart_4520994 baseEnd_4520994 := by
    simpa [prefixWord, tailWord_4520994, baseEnd_4520994] using wordTrace_append hprefix tailTrace_4520994
  have hstable : (prefixWord ++ tailWord_4520994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520994).length < 2 ^ (prefixWord ++ tailWord_4520994).sum := by decide
  have hdescent : baseEnd_4520994 < baseStart_4520994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4520997 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_4520997 : Nat := 118140960795 + 4520997 * 2 ^ 59
def prefixEnd_4520997 : Nat := 4983230072969 + 3 ^ 40 * 4520997 * 2
def baseEnd_4520997 : Nat := 2321444498534953312145819

theorem tailTrace_4520997 : CollatzResearch.WordTrace tailWord_4520997 prefixEnd_4520997 2321444498534953312145819 := by
  unfold tailWord_4520997
  simp only [CollatzResearch.WordTrace]
  refine ⟨164894307202207468660713245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109929538134804979107142163 164894307202207468660713245)
  ·
    refine ⟨61835365200827800747767467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164894307202207468660713245 61835365200827800747767467)
    ·
      refine ⟨92753047801241701121651201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61835365200827800747767467 92753047801241701121651201)
      ·
        refine ⟨69564785850931275841238401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92753047801241701121651201 69564785850931275841238401)
        ·
          refine ⟨52173589388198456880928801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69564785850931275841238401 52173589388198456880928801)
          ·
            refine ⟨39130192041148842660696601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52173589388198456880928801 39130192041148842660696601)
            ·
              refine ⟨29347644030861631995522451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39130192041148842660696601 29347644030861631995522451)
              ·
                refine ⟨44021466046292447993283677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29347644030861631995522451 44021466046292447993283677)
                ·
                  refine ⟨16508049767359667997481379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44021466046292447993283677 16508049767359667997481379)
                  ·
                    refine ⟨24762074651039501996222069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16508049767359667997481379 24762074651039501996222069)
                    ·
                      refine ⟨2321444498534953312145819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24762074651039501996222069 2321444498534953312145819)
                      ·
                        rfl

theorem cell23_4520997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_4520997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4520997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4520997 prefixEnd_4520997 := by exact prefixLift 4520997
  have htrace : WordTrace (prefixWord ++ tailWord_4520997) baseStart_4520997 baseEnd_4520997 := by
    simpa [prefixWord, tailWord_4520997, baseEnd_4520997] using wordTrace_append hprefix tailTrace_4520997
  have hstable : (prefixWord ++ tailWord_4520997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4520997).length < 2 ^ (prefixWord ++ tailWord_4520997).sum := by decide
  have hdescent : baseEnd_4520997 < baseStart_4520997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4520997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521004 : List Nat := [2, 2, 1, 1, 1, 2, 3, 5, 2, 4]
def baseStart_4521004 : Nat := 118140960795 + 4521004 * 2 ^ 59
def prefixEnd_4521004 : Nat := 4983230072969 + 3 ^ 40 * 4521004 * 2
def baseEnd_4521004 : Nat := 773816030966511594919429

theorem tailTrace_4521004 : CollatzResearch.WordTrace tailWord_4521004 prefixEnd_4521004 773816030966511594919429 := by
  unfold tailWord_4521004
  simp only [CollatzResearch.WordTrace]
  refine ⟨82447281256591054428109033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109929708342121405904145377 82447281256591054428109033)
  ·
    refine ⟨61835460942443290821081775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82447281256591054428109033 61835460942443290821081775)
    ·
      refine ⟨92753191413664936231622663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61835460942443290821081775 92753191413664936231622663)
      ·
        refine ⟨139129787120497404347433995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92753191413664936231622663 139129787120497404347433995)
        ·
          refine ⟨208694680680746106521150993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139129787120497404347433995 208694680680746106521150993)
          ·
            refine ⟨156521010510559579890863245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208694680680746106521150993 156521010510559579890863245)
            ·
              refine ⟨58695378941459842459073717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156521010510559579890863245 58695378941459842459073717)
              ·
                refine ⟨5502691775761860230538161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58695378941459842459073717 5502691775761860230538161)
                ·
                  refine ⟨4127018831821395172903621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5502691775761860230538161 4127018831821395172903621)
                  ·
                    refine ⟨773816030966511594919429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4127018831821395172903621 773816030966511594919429)
                    ·
                      rfl

theorem cell23_4521004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_4521004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521004 prefixEnd_4521004 := by exact prefixLift 4521004
  have htrace : WordTrace (prefixWord ++ tailWord_4521004) baseStart_4521004 baseEnd_4521004 := by
    simpa [prefixWord, tailWord_4521004, baseEnd_4521004] using wordTrace_append hprefix tailTrace_4521004
  have hstable : (prefixWord ++ tailWord_4521004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521004).length < 2 ^ (prefixWord ++ tailWord_4521004).sum := by decide
  have hdescent : baseEnd_4521004 < baseStart_4521004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521025 : List Nat := [1, 2, 5, 1, 4, 1, 2, 1, 1, 5]
def baseStart_4521025 : Nat := 118140960795 + 4521025 * 2 ^ 59
def prefixEnd_4521025 : Nat := 4983230072969 + 3 ^ 40 * 4521025 * 2
def baseEnd_4521025 : Nat := 773819625331093067531897

theorem tailTrace_4521025 : CollatzResearch.WordTrace tailWord_4521025 prefixEnd_4521025 773819625331093067531897 := by
  unfold tailWord_4521025
  simp only [CollatzResearch.WordTrace]
  refine ⟨164895328446106029442732529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109930218964070686295155019 164895328446106029442732529)
  ·
    refine ⟨123671496334579522082049397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164895328446106029442732529 123671496334579522082049397)
    ·
      refine ⟨11594202781366830195192131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123671496334579522082049397 11594202781366830195192131)
      ·
        refine ⟨17391304172050245292788197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11594202781366830195192131 17391304172050245292788197)
        ·
          refine ⟨3260869532259420992397787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17391304172050245292788197 3260869532259420992397787)
          ·
            refine ⟨4891304298389131488596681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3260869532259420992397787 4891304298389131488596681)
            ·
              refine ⟨3668478223791848616447511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4891304298389131488596681 3668478223791848616447511)
              ·
                refine ⟨5502717335687772924671267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3668478223791848616447511 5502717335687772924671267)
                ·
                  refine ⟨8254076003531659387006901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5502717335687772924671267 8254076003531659387006901)
                  ·
                    refine ⟨773819625331093067531897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8254076003531659387006901 773819625331093067531897)
                    ·
                      rfl

theorem cell23_4521025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_4521025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521025 prefixEnd_4521025 := by exact prefixLift 4521025
  have htrace : WordTrace (prefixWord ++ tailWord_4521025) baseStart_4521025 baseEnd_4521025 := by
    simpa [prefixWord, tailWord_4521025, baseEnd_4521025] using wordTrace_append hprefix tailTrace_4521025
  have hstable : (prefixWord ++ tailWord_4521025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521025).length < 2 ^ (prefixWord ++ tailWord_4521025).sum := by decide
  have hdescent : baseEnd_4521025 < baseStart_4521025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521031 : List Nat := [1, 1, 4, 1, 3, 3, 1, 3, 1, 2, 3]
def baseStart_4521031 : Nat := 118140960795 + 4521031 * 2 ^ 59
def prefixEnd_4521031 : Nat := 4983230072969 + 3 ^ 40 * 4521031 * 2
def baseEnd_4521031 : Nat := 2321461956877206179120663

theorem tailTrace_4521031 : CollatzResearch.WordTrace tailWord_4521031 prefixEnd_4521031 2321461956877206179120663 := by
  unfold tailWord_4521031
  simp only [CollatzResearch.WordTrace]
  refine ⟨164895547284084292467450947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109930364856056194978300631 164895547284084292467450947)
  ·
    refine ⟨247343320926126438701176421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164895547284084292467450947 247343320926126438701176421)
    ·
      refine ⟨46376872673648707256470579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 247343320926126438701176421 46376872673648707256470579)
      ·
        refine ⟨69565309010473060884705869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46376872673648707256470579 69565309010473060884705869)
        ·
          refine ⟨26086990878927397831764701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69565309010473060884705869 26086990878927397831764701)
          ·
            refine ⟨9782621579597774186911763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26086990878927397831764701 9782621579597774186911763)
            ·
              refine ⟨14673932369396661280367645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9782621579597774186911763 14673932369396661280367645)
              ·
                refine ⟨5502724638523747980137867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14673932369396661280367645 5502724638523747980137867)
                ·
                  refine ⟨8254086957785621970206801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5502724638523747980137867 8254086957785621970206801)
                  ·
                    refine ⟨6190565218339216477655101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8254086957785621970206801 6190565218339216477655101)
                    ·
                      refine ⟨2321461956877206179120663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6190565218339216477655101 2321461956877206179120663)
                      ·
                        rfl

theorem cell23_4521031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_4521031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521031 prefixEnd_4521031 := by exact prefixLift 4521031
  have htrace : WordTrace (prefixWord ++ tailWord_4521031) baseStart_4521031 baseEnd_4521031 := by
    simpa [prefixWord, tailWord_4521031, baseEnd_4521031] using wordTrace_append hprefix tailTrace_4521031
  have hstable : (prefixWord ++ tailWord_4521031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521031).length < 2 ^ (prefixWord ++ tailWord_4521031).sum := by decide
  have hdescent : baseEnd_4521031 < baseStart_4521031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521044 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_4521044 : Nat := 118140960795 + 4521044 * 2 ^ 59
def prefixEnd_4521044 : Nat := 4983230072969 + 3 ^ 40 * 4521044 * 2
def baseEnd_4521044 : Nat := 2321468632125714628258103

theorem tailTrace_4521044 : CollatzResearch.WordTrace tailWord_4521044 prefixEnd_4521044 2321468632125714628258103 := by
  unfold tailWord_4521044
  simp only [CollatzResearch.WordTrace]
  refine ⟨82448010716518597843837093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109930680955358130458449457 82448010716518597843837093)
  ·
    refine ⟨15459002009347237095719455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82448010716518597843837093 15459002009347237095719455)
    ·
      refine ⟨23188503014020855643579183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15459002009347237095719455 23188503014020855643579183)
      ·
        refine ⟨34782754521031283465368775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23188503014020855643579183 34782754521031283465368775)
        ·
          refine ⟨52174131781546925198053163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34782754521031283465368775 52174131781546925198053163)
          ·
            refine ⟨78261197672320387797079745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52174131781546925198053163 78261197672320387797079745)
            ·
              refine ⟨58695898254240290847809809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78261197672320387797079745 58695898254240290847809809)
              ·
                refine ⟨44021923690680218135857357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58695898254240290847809809 44021923690680218135857357)
                ·
                  refine ⟨16508221384005081800946509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44021923690680218135857357 16508221384005081800946509)
                  ·
                    refine ⟨6190583019001905675354941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16508221384005081800946509 6190583019001905675354941)
                    ·
                      refine ⟨2321468632125714628258103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6190583019001905675354941 2321468632125714628258103)
                      ·
                        rfl

theorem cell23_4521044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_4521044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521044 prefixEnd_4521044 := by exact prefixLift 4521044
  have htrace : WordTrace (prefixWord ++ tailWord_4521044) baseStart_4521044 baseEnd_4521044 := by
    simpa [prefixWord, tailWord_4521044, baseEnd_4521044] using wordTrace_append hprefix tailTrace_4521044
  have hstable : (prefixWord ++ tailWord_4521044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521044).length < 2 ^ (prefixWord ++ tailWord_4521044).sum := by decide
  have hdescent : baseEnd_4521044 < baseStart_4521044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521058 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_4521058 : Nat := 118140960795 + 4521058 * 2 ^ 59
def prefixEnd_4521058 : Nat := 4983230072969 + 3 ^ 40 * 4521058 * 2
def baseEnd_4521058 : Nat := 2321475820854877573483039

theorem tailTrace_4521058 : CollatzResearch.WordTrace tailWord_4521058 prefixEnd_4521058 2321475820854877573483039 := by
  unfold tailWord_4521058
  simp only [CollatzResearch.WordTrace]
  refine ⟨41224133013746619019670957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109931021369990984052455885 41224133013746619019670957)
  ·
    refine ⟨15459049880154982132376609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41224133013746619019670957 15459049880154982132376609)
    ·
      refine ⟨11594287410116236599282457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15459049880154982132376609 11594287410116236599282457)
      ·
        refine ⟨8695715557587177449461843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11594287410116236599282457 8695715557587177449461843)
        ·
          refine ⟨13043573336380766174192765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8695715557587177449461843 13043573336380766174192765)
          ·
            refine ⟨4891340001142787315322287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13043573336380766174192765 4891340001142787315322287)
            ·
              refine ⟨7337010001714180972983431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4891340001142787315322287 7337010001714180972983431)
              ·
                refine ⟨11005515002571271459475147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7337010001714180972983431 11005515002571271459475147)
                ·
                  refine ⟨16508272503856907189212721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11005515002571271459475147 16508272503856907189212721)
                  ·
                    refine ⟨12381204377892680391909541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16508272503856907189212721 12381204377892680391909541)
                    ·
                      refine ⟨2321475820854877573483039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12381204377892680391909541 2321475820854877573483039)
                      ·
                        rfl

theorem cell23_4521058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_4521058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521058 prefixEnd_4521058 := by exact prefixLift 4521058
  have htrace : WordTrace (prefixWord ++ tailWord_4521058) baseStart_4521058 baseEnd_4521058 := by
    simpa [prefixWord, tailWord_4521058, baseEnd_4521058] using wordTrace_append hprefix tailTrace_4521058
  have hstable : (prefixWord ++ tailWord_4521058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521058).length < 2 ^ (prefixWord ++ tailWord_4521058).sum := by decide
  have hdescent : baseEnd_4521058 < baseStart_4521058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521122 : List Nat := [3, 3, 1, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_4521122 : Nat := 118140960795 + 4521122 * 2 ^ 59
def prefixEnd_4521122 : Nat := 4983230072969 + 3 ^ 40 * 4521122 * 2
def baseEnd_4521122 : Nat := 2321508683616765323082745

theorem tailTrace_4521122 : CollatzResearch.WordTrace tailWord_4521122 prefixEnd_4521122 2321508683616765323082745 := by
  unfold tailWord_4521122
  simp only [CollatzResearch.WordTrace]
  refine ⟨41224716581688653752253405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109932577551169743339342413 41224716581688653752253405)
  ·
    refine ⟨15459268718133245157095027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41224716581688653752253405 15459268718133245157095027)
    ·
      refine ⟨23188903077199867735642541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15459268718133245157095027 23188903077199867735642541)
      ·
        refine ⟨8695838653949950400865953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23188903077199867735642541 8695838653949950400865953)
        ·
          refine ⟨6521878990462462800649465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8695838653949950400865953 6521878990462462800649465)
          ·
            refine ⟨4891409242846847100487099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6521878990462462800649465 4891409242846847100487099)
            ·
              refine ⟨7337113864270270650730649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4891409242846847100487099 7337113864270270650730649)
              ·
                refine ⟨5502835398202702988047987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7337113864270270650730649 5502835398202702988047987)
                ·
                  refine ⟨8254253097304054482071981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5502835398202702988047987 8254253097304054482071981)
                  ·
                    refine ⟨3095344911489020430776993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8254253097304054482071981 3095344911489020430776993)
                    ·
                      refine ⟨2321508683616765323082745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3095344911489020430776993 2321508683616765323082745)
                      ·
                        rfl

theorem cell23_4521122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_4521122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521122 prefixEnd_4521122 := by exact prefixLift 4521122
  have htrace : WordTrace (prefixWord ++ tailWord_4521122) baseStart_4521122 baseEnd_4521122 := by
    simpa [prefixWord, tailWord_4521122, baseEnd_4521122] using wordTrace_append hprefix tailTrace_4521122
  have hstable : (prefixWord ++ tailWord_4521122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521122).length < 2 ^ (prefixWord ++ tailWord_4521122).sum := by decide
  have hdescent : baseEnd_4521122 < baseStart_4521122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521165 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_4521165 : Nat := 118140960795 + 4521165 * 2 ^ 59
def prefixEnd_4521165 : Nat := 4983230072969 + 3 ^ 40 * 4521165 * 2
def baseEnd_4521165 : Nat := 2321530763284908654845047

theorem tailTrace_4521165 : CollatzResearch.WordTrace tailWord_4521165 prefixEnd_4521165 2321530763284908654845047 := by
  unfold tailWord_4521165
  simp only [CollatzResearch.WordTrace]
  refine ⟨164900434665598833352828949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109933623110399222235219299 164900434665598833352828949)
  ·
    refine ⟨7729707874949945313413857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 164900434665598833352828949 7729707874949945313413857)
    ·
      refine ⟨5797280906212458985060393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7729707874949945313413857 5797280906212458985060393)
      ·
        refine ⟨4347960679659344238795295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5797280906212458985060393 4347960679659344238795295)
        ·
          refine ⟨6521941019489016358192943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4347960679659344238795295 6521941019489016358192943)
          ·
            refine ⟨9782911529233524537289415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6521941019489016358192943 9782911529233524537289415)
            ·
              refine ⟨14674367293850286805934123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9782911529233524537289415 14674367293850286805934123)
              ·
                refine ⟨22011550940775430208901185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14674367293850286805934123 22011550940775430208901185)
                ·
                  refine ⟨16508663205581572656675889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22011550940775430208901185 16508663205581572656675889)
                  ·
                    refine ⟨12381497404186179492506917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16508663205581572656675889 12381497404186179492506917)
                    ·
                      refine ⟨2321530763284908654845047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12381497404186179492506917 2321530763284908654845047)
                      ·
                        rfl

theorem cell23_4521165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_4521165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521165 prefixEnd_4521165 := by exact prefixLift 4521165
  have htrace : WordTrace (prefixWord ++ tailWord_4521165) baseStart_4521165 baseEnd_4521165 := by
    simpa [prefixWord, tailWord_4521165, baseEnd_4521165] using wordTrace_append hprefix tailTrace_4521165
  have hstable : (prefixWord ++ tailWord_4521165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521165).length < 2 ^ (prefixWord ++ tailWord_4521165).sum := by decide
  have hdescent : baseEnd_4521165 < baseStart_4521165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521304 : List Nat := [2, 1, 2, 2, 1, 1, 3, 11]
def baseStart_4521304 : Nat := 118140960795 + 4521304 * 2 ^ 59
def prefixEnd_4521304 : Nat := 4983230072969 + 3 ^ 40 * 4521304 * 2
def baseEnd_4521304 : Nat := 85985264336884578185441

theorem tailTrace_4521304 : CollatzResearch.WordTrace tailWord_4521304 prefixEnd_4521304 85985264336884578185441 := by
  unfold tailWord_4521304
  simp only [CollatzResearch.WordTrace]
  refine ⟨82452752206047630046069483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109937002941396840061425977 82452752206047630046069483)
  ·
    refine ⟨123679128309071445069104225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82452752206047630046069483 123679128309071445069104225)
    ·
      refine ⟨92759346231803583801828169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123679128309071445069104225 92759346231803583801828169)
      ·
        refine ⟨69569509673852687851371127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92759346231803583801828169 69569509673852687851371127)
        ·
          refine ⟨104354264510779031777056691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69569509673852687851371127 104354264510779031777056691)
          ·
            refine ⟨156531396766168547665585037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104354264510779031777056691 156531396766168547665585037)
            ·
              refine ⟨58699273787313205374594389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156531396766168547665585037 58699273787313205374594389)
              ·
                refine ⟨85985264336884578185441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 58699273787313205374594389 85985264336884578185441)
                ·
                  rfl

theorem cell23_4521304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 11].length) (baseStart_4521304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521304 prefixEnd_4521304 := by exact prefixLift 4521304
  have htrace : WordTrace (prefixWord ++ tailWord_4521304) baseStart_4521304 baseEnd_4521304 := by
    simpa [prefixWord, tailWord_4521304, baseEnd_4521304] using wordTrace_append hprefix tailTrace_4521304
  have hstable : (prefixWord ++ tailWord_4521304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521304).length < 2 ^ (prefixWord ++ tailWord_4521304).sum := by decide
  have hdescent : baseEnd_4521304 < baseStart_4521304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521315 : List Nat := [1, 1, 1, 5, 2, 3, 3, 1, 1, 1, 4]
def baseStart_4521315 : Nat := 118140960795 + 4521315 * 2 ^ 59
def prefixEnd_4521315 : Nat := 4983230072969 + 3 ^ 40 * 4521315 * 2
def baseEnd_4521315 : Nat := 2321607785383083067969357

theorem tailTrace_4521315 : CollatzResearch.WordTrace tailWord_4521315 prefixEnd_4521315 2321607785383083067969357 := by
  unfold tailWord_4521315
  simp only [CollatzResearch.WordTrace]
  refine ⟨164905905615055408970789399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109937270410036939313859599 164905905615055408970789399)
  ·
    refine ⟨247358858422583113456184099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164905905615055408970789399 247358858422583113456184099)
    ·
      refine ⟨371038287633874670184276149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247358858422583113456184099 371038287633874670184276149)
      ·
        refine ⟨34784839465675750329775889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 371038287633874670184276149 34784839465675750329775889)
        ·
          refine ⟨26088629599256812747331917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34784839465675750329775889 26088629599256812747331917)
          ·
            refine ⟨9783236099721304780249469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26088629599256812747331917 9783236099721304780249469)
            ·
              refine ⟨3668713537395489292593551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9783236099721304780249469 3668713537395489292593551)
              ·
                refine ⟨5503070306093233938890327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3668713537395489292593551 5503070306093233938890327)
                ·
                  refine ⟨8254605459139850908335491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5503070306093233938890327 8254605459139850908335491)
                  ·
                    refine ⟨12381908188709776362503237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8254605459139850908335491 12381908188709776362503237)
                    ·
                      refine ⟨2321607785383083067969357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12381908188709776362503237 2321607785383083067969357)
                      ·
                        rfl

theorem cell23_4521315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_4521315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521315 prefixEnd_4521315 := by exact prefixLift 4521315
  have htrace : WordTrace (prefixWord ++ tailWord_4521315) baseStart_4521315 baseEnd_4521315 := by
    simpa [prefixWord, tailWord_4521315, baseEnd_4521315] using wordTrace_append hprefix tailTrace_4521315
  have hstable : (prefixWord ++ tailWord_4521315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521315).length < 2 ^ (prefixWord ++ tailWord_4521315).sum := by decide
  have hdescent : baseEnd_4521315 < baseStart_4521315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521325 : List Nat := [1, 5, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_4521325 : Nat := 118140960795 + 4521325 * 2 ^ 59
def prefixEnd_4521325 : Nat := 4983230072969 + 3 ^ 40 * 4521325 * 2
def baseEnd_4521325 : Nat := 773870973396542676281437

theorem tailTrace_4521325 : CollatzResearch.WordTrace tailWord_4521325 prefixEnd_4521325 773870973396542676281437 := by
  unfold tailWord_4521325
  simp only [CollatzResearch.WordTrace]
  refine ⟨164906270345019180678653429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109937513563346120452435619 164906270345019180678653429)
  ·
    refine ⟨15459962844845548188623759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164906270345019180678653429 15459962844845548188623759)
    ·
      refine ⟨23189944267268322282935639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15459962844845548188623759 23189944267268322282935639)
      ·
        refine ⟨34784916400902483424403459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23189944267268322282935639 34784916400902483424403459)
        ·
          refine ⟨52177374601353725136605189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34784916400902483424403459 52177374601353725136605189)
          ·
            refine ⟨9783257737753823463113473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52177374601353725136605189 9783257737753823463113473)
            ·
              refine ⟨7337443303315367597335105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9783257737753823463113473 7337443303315367597335105)
              ·
                refine ⟨5503082477486525698001329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7337443303315367597335105 5503082477486525698001329)
                ·
                  refine ⟨4127311858114894273500997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5503082477486525698001329 4127311858114894273500997)
                  ·
                    refine ⟨773870973396542676281437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4127311858114894273500997 773870973396542676281437)
                    ·
                      rfl

theorem cell23_4521325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_4521325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521325 prefixEnd_4521325 := by exact prefixLift 4521325
  have htrace : WordTrace (prefixWord ++ tailWord_4521325) baseStart_4521325 baseEnd_4521325 := by
    simpa [prefixWord, tailWord_4521325, baseEnd_4521325] using wordTrace_append hprefix tailTrace_4521325
  have hstable : (prefixWord ++ tailWord_4521325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521325).length < 2 ^ (prefixWord ++ tailWord_4521325).sum := by decide
  have hdescent : baseEnd_4521325 < baseStart_4521325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521342 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_4521342 : Nat := 118140960795 + 4521342 * 2 ^ 59
def prefixEnd_4521342 : Nat := 4983230072969 + 3 ^ 40 * 4521342 * 2
def baseEnd_4521342 : Nat := 773873883120251487443911

theorem tailTrace_4521342 : CollatzResearch.WordTrace tailWord_4521342 prefixEnd_4521342 773873883120251487443911 := by
  unfold tailWord_4521342
  simp only [CollatzResearch.WordTrace]
  refine ⟨20613361298244699072752785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109937926923971728388014853 20613361298244699072752785)
  ·
    refine ⟨15460020973683524304564589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20613361298244699072752785 15460020973683524304564589)
    ·
      refine ⟨5797507865131321614211721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15460020973683524304564589 5797507865131321614211721)
      ·
        refine ⟨4348130898848491210658791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5797507865131321614211721 4348130898848491210658791)
        ·
          refine ⟨6522196348272736815988187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4348130898848491210658791 6522196348272736815988187)
          ·
            refine ⟨9783294522409105223982281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6522196348272736815988187 9783294522409105223982281)
            ·
              refine ⟨7337470891806828917986711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9783294522409105223982281 7337470891806828917986711)
              ·
                refine ⟨11006206337710243376980067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7337470891806828917986711 11006206337710243376980067)
                ·
                  refine ⟨16509309506565365065470101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11006206337710243376980067 16509309506565365065470101)
                  ·
                    refine ⟨773873883120251487443911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16509309506565365065470101 773873883120251487443911)
                    ·
                      rfl

theorem cell23_4521342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_4521342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521342 prefixEnd_4521342 := by exact prefixLift 4521342
  have htrace : WordTrace (prefixWord ++ tailWord_4521342) baseStart_4521342 baseEnd_4521342 := by
    simpa [prefixWord, tailWord_4521342, baseEnd_4521342] using wordTrace_append hprefix tailTrace_4521342
  have hstable : (prefixWord ++ tailWord_4521342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521342).length < 2 ^ (prefixWord ++ tailWord_4521342).sum := by decide
  have hdescent : baseEnd_4521342 < baseStart_4521342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521345 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_4521345 : Nat := 118140960795 + 4521345 * 2 ^ 59
def prefixEnd_4521345 : Nat := 4983230072969 + 3 ^ 40 * 4521345 * 2
def baseEnd_4521345 : Nat := 2321623189802717950594219

theorem tailTrace_4521345 : CollatzResearch.WordTrace tailWord_4521345 prefixEnd_4521345 2321623189802717950594219 := by
  unfold tailWord_4521345
  simp only [CollatzResearch.WordTrace]
  refine ⟨164906999804946724094381489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109937999869964482729587659 164906999804946724094381489)
  ·
    refine ⟨123680249853710043070786117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164906999804946724094381489 123680249853710043070786117)
    ·
      refine ⟨23190046847570633075772397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123680249853710043070786117 23190046847570633075772397)
      ·
        refine ⟨8696267567838987403414649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23190046847570633075772397 8696267567838987403414649)
        ·
          refine ⟨6522200675879240552560987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8696267567838987403414649 6522200675879240552560987)
          ·
            refine ⟨9783301013818860828841481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6522200675879240552560987 9783301013818860828841481)
            ·
              refine ⟨7337475760364145621631111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9783301013818860828841481 7337475760364145621631111)
              ·
                refine ⟨11006213640546218432446667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7337475760364145621631111 11006213640546218432446667)
                ·
                  refine ⟨16509320460819327648670001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11006213640546218432446667 16509320460819327648670001)
                  ·
                    refine ⟨12381990345614495736502501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16509320460819327648670001 12381990345614495736502501)
                    ·
                      refine ⟨2321623189802717950594219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12381990345614495736502501 2321623189802717950594219)
                      ·
                        rfl

theorem cell23_4521345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_4521345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521345 prefixEnd_4521345 := by exact prefixLift 4521345
  have htrace : WordTrace (prefixWord ++ tailWord_4521345) baseStart_4521345 baseEnd_4521345 := by
    simpa [prefixWord, tailWord_4521345, baseEnd_4521345] using wordTrace_append hprefix tailTrace_4521345
  have hstable : (prefixWord ++ tailWord_4521345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521345).length < 2 ^ (prefixWord ++ tailWord_4521345).sum := by decide
  have hdescent : baseEnd_4521345 < baseStart_4521345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521348 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_4521348 : Nat := 118140960795 + 4521348 * 2 ^ 59
def prefixEnd_4521348 : Nat := 4983230072969 + 3 ^ 40 * 4521348 * 2
def baseEnd_4521348 : Nat := 2321624730244681438856705

theorem tailTrace_4521348 : CollatzResearch.WordTrace tailWord_4521348 prefixEnd_4521348 2321624730244681438856705 := by
  unfold tailWord_4521348
  simp only [CollatzResearch.WordTrace]
  refine ⟨82453554611967927803370349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109938072815957237071160465 82453554611967927803370349)
  ·
    refine ⟨30920082979487972926263881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82453554611967927803370349 30920082979487972926263881)
    ·
      refine ⟨23190062234615979694697911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30920082979487972926263881 23190062234615979694697911)
      ·
        refine ⟨34785093351923969542046867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23190062234615979694697911 34785093351923969542046867)
        ·
          refine ⟨52177640027885954313070301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34785093351923969542046867 52177640027885954313070301)
          ·
            refine ⟨19566615010457232867401363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52177640027885954313070301 19566615010457232867401363)
            ·
              refine ⟨29349922515685849301102045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19566615010457232867401363 29349922515685849301102045)
              ·
                refine ⟨11006220943382193487913267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29349922515685849301102045 11006220943382193487913267)
                ·
                  refine ⟨16509331415073290231869901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11006220943382193487913267 16509331415073290231869901)
                  ·
                    refine ⟨6190999280652483836951213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16509331415073290231869901 6190999280652483836951213)
                    ·
                      refine ⟨2321624730244681438856705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6190999280652483836951213 2321624730244681438856705)
                      ·
                        rfl

theorem cell23_4521348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_4521348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521348 prefixEnd_4521348 := by exact prefixLift 4521348
  have htrace : WordTrace (prefixWord ++ tailWord_4521348) baseStart_4521348 baseEnd_4521348 := by
    simpa [prefixWord, tailWord_4521348, baseEnd_4521348] using wordTrace_append hprefix tailTrace_4521348
  have hstable : (prefixWord ++ tailWord_4521348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521348).length < 2 ^ (prefixWord ++ tailWord_4521348).sum := by decide
  have hdescent : baseEnd_4521348 < baseStart_4521348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521388 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 3, 4, 2]
def baseStart_4521388 : Nat := 118140960795 + 4521388 * 2 ^ 59
def prefixEnd_4521388 : Nat := 4983230072969 + 3 ^ 40 * 4521388 * 2
def baseEnd_4521388 : Nat := 2321645269470861282356521

theorem tailTrace_4521388 : CollatzResearch.WordTrace tailWord_4521388 prefixEnd_4521388 2321645269470861282356521 := by
  unfold tailWord_4521388
  simp only [CollatzResearch.WordTrace]
  refine ⟨82454284071895471219098409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109939045429193961625464545 82454284071895471219098409)
  ·
    refine ⟨61840713053921603414323807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82454284071895471219098409 61840713053921603414323807)
    ·
      refine ⟨92761069580882405121485711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61840713053921603414323807 92761069580882405121485711)
      ·
        refine ⟨139141604371323607682228567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92761069580882405121485711 139141604371323607682228567)
        ·
          refine ⟨208712406556985411523342851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139141604371323607682228567 208712406556985411523342851)
          ·
            refine ⟨313068609835478117285014277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208712406556985411523342851 313068609835478117285014277)
            ·
              refine ⟨58700364344152146990940177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 313068609835478117285014277 58700364344152146990940177)
              ·
                refine ⟨44025273258114110243205133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58700364344152146990940177 44025273258114110243205133)
                ·
                  refine ⟨16509477471792791341201925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44025273258114110243205133 16509477471792791341201925)
                  ·
                    refine ⟨3095527025961148376475361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16509477471792791341201925 3095527025961148376475361)
                    ·
                      refine ⟨2321645269470861282356521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3095527025961148376475361 2321645269470861282356521)
                      ·
                        rfl

theorem cell23_4521388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 4, 2].length) (baseStart_4521388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521388 prefixEnd_4521388 := by exact prefixLift 4521388
  have htrace : WordTrace (prefixWord ++ tailWord_4521388) baseStart_4521388 baseEnd_4521388 := by
    simpa [prefixWord, tailWord_4521388, baseEnd_4521388] using wordTrace_append hprefix tailTrace_4521388
  have hstable : (prefixWord ++ tailWord_4521388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521388).length < 2 ^ (prefixWord ++ tailWord_4521388).sum := by decide
  have hdescent : baseEnd_4521388 < baseStart_4521388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521391 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 3]
def baseStart_4521391 : Nat := 118140960795 + 4521391 * 2 ^ 59
def prefixEnd_4521391 : Nat := 4983230072969 + 3 ^ 40 * 4521391 * 2
def baseEnd_4521391 : Nat := 2321646809912824770619007

theorem tailTrace_4521391 : CollatzResearch.WordTrace tailWord_4521391 prefixEnd_4521391 2321646809912824770619007 := by
  unfold tailWord_4521391
  simp only [CollatzResearch.WordTrace]
  refine ⟨164908677562780073950556027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109939118375186715967037351 164908677562780073950556027)
  ·
    refine ⟨247363016344170110925834041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164908677562780073950556027 247363016344170110925834041)
    ·
      refine ⟨185522262258127583194375531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247363016344170110925834041 185522262258127583194375531)
      ·
        refine ⟨278283393387191374791563297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185522262258127583194375531 278283393387191374791563297)
        ·
          refine ⟨208712545040393531093672473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278283393387191374791563297 208712545040393531093672473)
          ·
            refine ⟨156534408780295148320254355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208712545040393531093672473 156534408780295148320254355)
            ·
              refine ⟨234801613170442722480381533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156534408780295148320254355 234801613170442722480381533)
              ·
                refine ⟨88050604938916020930143075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234801613170442722480381533 88050604938916020930143075)
                ·
                  refine ⟨132075907408374031395214613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88050604938916020930143075 132075907408374031395214613)
                  ·
                    refine ⟨6191058159767532721650685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 132075907408374031395214613 6191058159767532721650685)
                    ·
                      refine ⟨2321646809912824770619007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6191058159767532721650685 2321646809912824770619007)
                      ·
                        rfl

theorem cell23_4521391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 3].length) (baseStart_4521391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521391 prefixEnd_4521391 := by exact prefixLift 4521391
  have htrace : WordTrace (prefixWord ++ tailWord_4521391) baseStart_4521391 baseEnd_4521391 := by
    simpa [prefixWord, tailWord_4521391, baseEnd_4521391] using wordTrace_append hprefix tailTrace_4521391
  have hstable : (prefixWord ++ tailWord_4521391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521391).length < 2 ^ (prefixWord ++ tailWord_4521391).sum := by decide
  have hdescent : baseEnd_4521391 < baseStart_4521391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521411 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 7]
def baseStart_4521411 : Nat := 118140960795 + 4521411 * 2 ^ 59
def prefixEnd_4521411 : Nat := 4983230072969 + 3 ^ 40 * 4521411 * 2
def baseEnd_4521411 : Nat := 257961897725101632485435

theorem tailTrace_4521411 : CollatzResearch.WordTrace tailWord_4521411 prefixEnd_4521411 257961897725101632485435 := by
  unfold tailWord_4521411
  simp only [CollatzResearch.WordTrace]
  refine ⟨164909407022707617366284087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109939604681805078244189391 164909407022707617366284087)
  ·
    refine ⟨247364110534061426049426131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164909407022707617366284087 247364110534061426049426131)
    ·
      refine ⟨371046165801092139074139197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247364110534061426049426131 371046165801092139074139197)
      ·
        refine ⟨139142312175409552152802199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 371046165801092139074139197 139142312175409552152802199)
        ·
          refine ⟨208713468263114328229203299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139142312175409552152802199 208713468263114328229203299)
          ·
            refine ⟨313070202394671492343804949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208713468263114328229203299 313070202394671492343804949)
            ·
              refine ⟨14675165737250226203615857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 313070202394671492343804949 14675165737250226203615857)
              ·
                refine ⟨11006374302937669652711893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14675165737250226203615857 11006374302937669652711893)
                ·
                  refine ⟨257961897725101632485435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11006374302937669652711893 257961897725101632485435)
                  ·
                    rfl

theorem cell23_4521411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 7].length) (baseStart_4521411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521411 prefixEnd_4521411 := by exact prefixLift 4521411
  have htrace : WordTrace (prefixWord ++ tailWord_4521411) baseStart_4521411 baseEnd_4521411 := by
    simpa [prefixWord, tailWord_4521411, baseEnd_4521411] using wordTrace_append hprefix tailTrace_4521411
  have hstable : (prefixWord ++ tailWord_4521411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521411).length < 2 ^ (prefixWord ++ tailWord_4521411).sum := by decide
  have hdescent : baseEnd_4521411 < baseStart_4521411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521445 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 7]
def baseStart_4521445 : Nat := 118140960795 + 4521445 * 2 ^ 59
def prefixEnd_4521445 : Nat := 4983230072969 + 3 ^ 40 * 4521445 * 2
def baseEnd_4521445 : Nat := 257963837540907506593751

theorem tailTrace_4521445 : CollatzResearch.WordTrace tailWord_4521445 prefixEnd_4521445 257963837540907506593751 := by
  unfold tailWord_4521445
  simp only [CollatzResearch.WordTrace]
  refine ⟨164910647104584441173021789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109940431403056294115347859 164910647104584441173021789)
  ·
    refine ⟨61841492664219165439883171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164910647104584441173021789 61841492664219165439883171)
    ·
      refine ⟨92762238996328748159824757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61841492664219165439883171 92762238996328748159824757)
      ·
        refine ⟨8696459905905820139983571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92762238996328748159824757 8696459905905820139983571)
        ·
          refine ⟨13044689858858730209975357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8696459905905820139983571 13044689858858730209975357)
          ·
            refine ⟨4891758697072023828740759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13044689858858730209975357 4891758697072023828740759)
            ·
              refine ⟨7337638045608035743111139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4891758697072023828740759 7337638045608035743111139)
              ·
                refine ⟨11006457068412053614666709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7337638045608035743111139 11006457068412053614666709)
                ·
                  refine ⟨257963837540907506593751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11006457068412053614666709 257963837540907506593751)
                  ·
                    rfl

theorem cell23_4521445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 7].length) (baseStart_4521445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521445 prefixEnd_4521445 := by exact prefixLift 4521445
  have htrace : WordTrace (prefixWord ++ tailWord_4521445) baseStart_4521445 baseEnd_4521445 := by
    simpa [prefixWord, tailWord_4521445, baseEnd_4521445] using wordTrace_append hprefix tailTrace_4521445
  have hstable : (prefixWord ++ tailWord_4521445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521445).length < 2 ^ (prefixWord ++ tailWord_4521445).sum := by decide
  have hdescent : baseEnd_4521445 < baseStart_4521445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521498 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3]
def baseStart_4521498 : Nat := 118140960795 + 4521498 * 2 ^ 59
def prefixEnd_4521498 : Nat := 4983230072969 + 3 ^ 40 * 4521498 * 2
def baseEnd_4521498 : Nat := 2321701752342855851981015

theorem tailTrace_4521498 : CollatzResearch.WordTrace tailWord_4521498 prefixEnd_4521498 2321701752342855851981015 := by
  unfold tailWord_4521498
  simp only [CollatzResearch.WordTrace]
  refine ⟨41228145043348107806175287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109941720115594954149800765 41228145043348107806175287)
  ·
    refine ⟨61842217565022161709262931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41228145043348107806175287 61842217565022161709262931)
    ·
      refine ⟨92763326347533242563894397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61842217565022161709262931 92763326347533242563894397)
      ·
        refine ⟨34786247380324965961460399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92763326347533242563894397 34786247380324965961460399)
        ·
          refine ⟨52179371070487448942190599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34786247380324965961460399 52179371070487448942190599)
          ·
            refine ⟨78269056605731173413285899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52179371070487448942190599 78269056605731173413285899)
            ·
              refine ⟨117403584908596760119928849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78269056605731173413285899 117403584908596760119928849)
              ·
                refine ⟨88052688681447570089946637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117403584908596760119928849 88052688681447570089946637)
                ·
                  refine ⟨33019758255542838783729989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88052688681447570089946637 33019758255542838783729989)
                  ·
                    refine ⟨6191204672914282271949373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33019758255542838783729989 6191204672914282271949373)
                    ·
                      refine ⟨2321701752342855851981015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6191204672914282271949373 2321701752342855851981015)
                      ·
                        rfl

theorem cell23_4521498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_4521498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521498 prefixEnd_4521498 := by exact prefixLift 4521498
  have htrace : WordTrace (prefixWord ++ tailWord_4521498) baseStart_4521498 baseEnd_4521498 := by
    simpa [prefixWord, tailWord_4521498, baseEnd_4521498] using wordTrace_append hprefix tailTrace_4521498
  have hstable : (prefixWord ++ tailWord_4521498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521498).length < 2 ^ (prefixWord ++ tailWord_4521498).sum := by decide
  have hdescent : baseEnd_4521498 < baseStart_4521498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521605 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 1, 1, 5]
def baseStart_4521605 : Nat := 118140960795 + 4521605 * 2 ^ 59
def prefixEnd_4521605 : Nat := 4983230072969 + 3 ^ 40 * 4521605 * 2
def baseEnd_4521605 : Nat := 2321756694772886933343023

theorem tailTrace_4521605 : CollatzResearch.WordTrace tailWord_4521605 prefixEnd_4521605 2321756694772886933343023 := by
  unfold tailWord_4521605
  simp only [CollatzResearch.WordTrace]
  refine ⟨164916482784004788498846269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109944321856003192332564179 164916482784004788498846269)
  ·
    refine ⟨61843681044001795687067351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164916482784004788498846269 61843681044001795687067351)
    ·
      refine ⟨92765521566002693530601027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61843681044001795687067351 92765521566002693530601027)
      ·
        refine ⟨139148282349004040295901541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92765521566002693530601027 139148282349004040295901541)
        ·
          refine ⟨26090302940438257555481539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139148282349004040295901541 26090302940438257555481539)
          ·
            refine ⟨39135454410657386333222309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26090302940438257555481539 39135454410657386333222309)
            ·
              refine ⟨7337897701998259937479183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39135454410657386333222309 7337897701998259937479183)
              ·
                refine ⟨11006846552997389906218775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7337897701998259937479183 11006846552997389906218775)
                ·
                  refine ⟨16510269829496084859328163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11006846552997389906218775 16510269829496084859328163)
                  ·
                    refine ⟨24765404744244127288992245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16510269829496084859328163 24765404744244127288992245)
                    ·
                      refine ⟨2321756694772886933343023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24765404744244127288992245 2321756694772886933343023)
                      ·
                        rfl

theorem cell23_4521605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_4521605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521605 prefixEnd_4521605 := by exact prefixLift 4521605
  have htrace : WordTrace (prefixWord ++ tailWord_4521605) baseStart_4521605 baseEnd_4521605 := by
    simpa [prefixWord, tailWord_4521605, baseEnd_4521605] using wordTrace_append hprefix tailTrace_4521605
  have hstable : (prefixWord ++ tailWord_4521605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521605).length < 2 ^ (prefixWord ++ tailWord_4521605).sum := by decide
  have hdescent : baseEnd_4521605 < baseStart_4521605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521635 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 3]
def baseStart_4521635 : Nat := 118140960795 + 4521635 * 2 ^ 59
def prefixEnd_4521635 : Nat := 4983230072969 + 3 ^ 40 * 4521635 * 2
def baseEnd_4521635 : Nat := 2321772099192521815967885

theorem tailTrace_4521635 : CollatzResearch.WordTrace tailWord_4521635 prefixEnd_4521635 2321772099192521815967885 := by
  unfold tailWord_4521635
  simp only [CollatzResearch.WordTrace]
  refine ⟨164917576973896103622438359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109945051315930735748292239 164917576973896103622438359)
  ·
    refine ⟨247376365460844155433657539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164917576973896103622438359 247376365460844155433657539)
    ·
      refine ⟨371064548191266233150486309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247376365460844155433657539 371064548191266233150486309)
      ·
        refine ⟨69574602785862418715716183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 371064548191266233150486309 69574602785862418715716183)
        ·
          refine ⟨104361904178793628073574275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69574602785862418715716183 104361904178793628073574275)
          ·
            refine ⟨156542856268190442110361413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104361904178793628073574275 156542856268190442110361413)
            ·
              refine ⟨29351785550285707895692765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156542856268190442110361413 29351785550285707895692765)
              ·
                refine ⟨11006919581357140460884787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29351785550285707895692765 11006919581357140460884787)
                ·
                  refine ⟨16510379372035710691327181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11006919581357140460884787 16510379372035710691327181)
                  ·
                    refine ⟨6191392264513391509247693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16510379372035710691327181 6191392264513391509247693)
                    ·
                      refine ⟨2321772099192521815967885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6191392264513391509247693 2321772099192521815967885)
                      ·
                        rfl

theorem cell23_4521635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_4521635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521635 prefixEnd_4521635 := by exact prefixLift 4521635
  have htrace : WordTrace (prefixWord ++ tailWord_4521635) baseStart_4521635 baseEnd_4521635 := by
    simpa [prefixWord, tailWord_4521635, baseEnd_4521635] using wordTrace_append hprefix tailTrace_4521635
  have hstable : (prefixWord ++ tailWord_4521635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521635).length < 2 ^ (prefixWord ++ tailWord_4521635).sum := by decide
  have hdescent : baseEnd_4521635 < baseStart_4521635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521648 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 5]
def baseStart_4521648 : Nat := 118140960795 + 4521648 * 2 ^ 59
def prefixEnd_4521648 : Nat := 4983230072969 + 3 ^ 40 * 4521648 * 2
def baseEnd_4521648 : Nat := 2321778774441030265105325

theorem tailTrace_4521648 : CollatzResearch.WordTrace tailWord_4521648 prefixEnd_4521648 2321778774441030265105325 := by
  unfold tailWord_4521648
  simp only [CollatzResearch.WordTrace]
  refine ⟨82459025561424503421330799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109945367415232671228441065 82459025561424503421330799)
  ·
    refine ⟨123688538342136755131996199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82459025561424503421330799 123688538342136755131996199)
    ·
      refine ⟨185532807513205132697994299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123688538342136755131996199 185532807513205132697994299)
      ·
        refine ⟨278299211269807699046991449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185532807513205132697994299 278299211269807699046991449)
        ·
          refine ⟨208724408452355774285243587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278299211269807699046991449 208724408452355774285243587)
          ·
            refine ⟨313086612678533661427865381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208724408452355774285243587 313086612678533661427865381)
            ·
              refine ⟨58703739877225061517724759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 313086612678533661427865381 58703739877225061517724759)
              ·
                refine ⟨88055609815837592276587139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58703739877225061517724759 88055609815837592276587139)
                ·
                  refine ⟨132083414723756388414880709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88055609815837592276587139 132083414723756388414880709)
                  ·
                    refine ⟨24765640260704322827790133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 132083414723756388414880709 24765640260704322827790133)
                    ·
                      refine ⟨2321778774441030265105325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24765640260704322827790133 2321778774441030265105325)
                      ·
                        rfl

theorem cell23_4521648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_4521648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521648 prefixEnd_4521648 := by exact prefixLift 4521648
  have htrace : WordTrace (prefixWord ++ tailWord_4521648) baseStart_4521648 baseEnd_4521648 := by
    simpa [prefixWord, tailWord_4521648, baseEnd_4521648] using wordTrace_append hprefix tailTrace_4521648
  have hstable : (prefixWord ++ tailWord_4521648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521648).length < 2 ^ (prefixWord ++ tailWord_4521648).sum := by decide
  have hdescent : baseEnd_4521648 < baseStart_4521648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521695 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 3]
def baseStart_4521695 : Nat := 118140960795 + 4521695 * 2 ^ 59
def prefixEnd_4521695 : Nat := 4983230072969 + 3 ^ 40 * 4521695 * 2
def baseEnd_4521695 : Nat := 2321802908031791581217609

theorem tailTrace_4521695 : CollatzResearch.WordTrace tailWord_4521695 prefixEnd_4521695 2321802908031791581217609 := by
  unfold tailWord_4521695
  simp only [CollatzResearch.WordTrace]
  refine ⟨164919765353678733869622539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109946510235785822579748359 164919765353678733869622539)
  ·
    refine ⟨247379648030518100804433809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164919765353678733869622539 247379648030518100804433809)
    ·
      refine ⟨185534736022888575603325357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247379648030518100804433809 185534736022888575603325357)
      ·
        refine ⟨69575526008583215851247009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185534736022888575603325357 69575526008583215851247009)
        ·
          refine ⟨52181644506437411888435257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69575526008583215851247009 52181644506437411888435257)
          ·
            refine ⟨39136233379828058916326443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52181644506437411888435257 39136233379828058916326443)
            ·
              refine ⟨58704350069742088374489665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39136233379828058916326443 58704350069742088374489665)
              ·
                refine ⟨44028262552306566280867249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58704350069742088374489665 44028262552306566280867249)
                ·
                  refine ⟨33021196914229924710650437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44028262552306566280867249 33021196914229924710650437)
                  ·
                    refine ⟨6191474421418110883246957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33021196914229924710650437 6191474421418110883246957)
                    ·
                      refine ⟨2321802908031791581217609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6191474421418110883246957 2321802908031791581217609)
                      ·
                        rfl

theorem cell23_4521695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_4521695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521695 prefixEnd_4521695 := by exact prefixLift 4521695
  have htrace : WordTrace (prefixWord ++ tailWord_4521695) baseStart_4521695 baseEnd_4521695 := by
    simpa [prefixWord, tailWord_4521695, baseEnd_4521695] using wordTrace_append hprefix tailTrace_4521695
  have hstable : (prefixWord ++ tailWord_4521695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521695).length < 2 ^ (prefixWord ++ tailWord_4521695).sum := by decide
  have hdescent : baseEnd_4521695 < baseStart_4521695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521709 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_4521709 : Nat := 118140960795 + 4521709 * 2 ^ 59
def prefixEnd_4521709 : Nat := 4983230072969 + 3 ^ 40 * 4521709 * 2
def baseEnd_4521709 : Nat := 2321810096760954526442545

theorem tailTrace_4521709 : CollatzResearch.WordTrace tailWord_4521709 prefixEnd_4521709 2321810096760954526442545 := by
  unfold tailWord_4521709
  simp only [CollatzResearch.WordTrace]
  refine ⟨164920275975628014260632181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109946850650418676173754787 164920275975628014260632181)
  ·
    refine ⟨15461275872715126336934267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164920275975628014260632181 15461275872715126336934267)
    ·
      refine ⟨23191913809072689505401401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15461275872715126336934267 23191913809072689505401401)
      ·
        refine ⟨17393935356804517129051051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23191913809072689505401401 17393935356804517129051051)
        ·
          refine ⟨26090903035206775693576577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17393935356804517129051051 26090903035206775693576577)
          ·
            refine ⟨19568177276405081770182433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26090903035206775693576577 19568177276405081770182433)
            ·
              refine ⟨14676132957303811327636825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19568177276405081770182433 14676132957303811327636825)
              ·
                refine ⟨11007099717977858495727619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14676132957303811327636825 11007099717977858495727619)
                ·
                  refine ⟨16510649576966787743591429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11007099717977858495727619 16510649576966787743591429)
                  ·
                    refine ⟨3095746795681272701923393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16510649576966787743591429 3095746795681272701923393)
                    ·
                      refine ⟨2321810096760954526442545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3095746795681272701923393 2321810096760954526442545)
                      ·
                        rfl

theorem cell23_4521709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_4521709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521709 prefixEnd_4521709 := by exact prefixLift 4521709
  have htrace : WordTrace (prefixWord ++ tailWord_4521709) baseStart_4521709 baseEnd_4521709 := by
    simpa [prefixWord, tailWord_4521709, baseEnd_4521709] using wordTrace_append hprefix tailTrace_4521709
  have hstable : (prefixWord ++ tailWord_4521709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521709).length < 2 ^ (prefixWord ++ tailWord_4521709).sum := by decide
  have hdescent : baseEnd_4521709 < baseStart_4521709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521732 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 7]
def baseStart_4521732 : Nat := 118140960795 + 4521732 * 2 ^ 59
def prefixEnd_4521732 : Nat := 4983230072969 + 3 ^ 40 * 4521732 * 2
def baseEnd_4521732 : Nat := 257980211868445326272771

theorem tailTrace_4521732 : CollatzResearch.WordTrace tailWord_4521732 prefixEnd_4521732 257980211868445326272771 := by
  unfold tailWord_4521732
  simp only [CollatzResearch.WordTrace]
  refine ⟨82460557427272344594359725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109947409903029792792479633 82460557427272344594359725)
  ·
    refine ⟨30922709035227129222884897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82460557427272344594359725 30922709035227129222884897)
    ·
      refine ⟨23192031776420346917163673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30922709035227129222884897 23192031776420346917163673)
      ·
        refine ⟨17394023832315260187872755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23192031776420346917163673 17394023832315260187872755)
        ·
          refine ⟨26091035748472890281809133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17394023832315260187872755 26091035748472890281809133)
          ·
            refine ⟨9784138405677333855678425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26091035748472890281809133 9784138405677333855678425)
            ·
              refine ⟨7338103804258000391758819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9784138405677333855678425 7338103804258000391758819)
              ·
                refine ⟨11007155706387000587638229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7338103804258000391758819 11007155706387000587638229)
                ·
                  refine ⟨257980211868445326272771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11007155706387000587638229 257980211868445326272771)
                  ·
                    rfl

theorem cell23_4521732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_4521732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521732 prefixEnd_4521732 := by exact prefixLift 4521732
  have htrace : WordTrace (prefixWord ++ tailWord_4521732) baseStart_4521732 baseEnd_4521732 := by
    simpa [prefixWord, tailWord_4521732, baseEnd_4521732] using wordTrace_append hprefix tailTrace_4521732
  have hstable : (prefixWord ++ tailWord_4521732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521732).length < 2 ^ (prefixWord ++ tailWord_4521732).sum := by decide
  have hdescent : baseEnd_4521732 < baseStart_4521732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521742 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_4521742 : Nat := 118140960795 + 4521742 * 2 ^ 59
def prefixEnd_4521742 : Nat := 4983230072969 + 3 ^ 40 * 4521742 * 2
def baseEnd_4521742 : Nat := 2321827041622552897329893

theorem tailTrace_4521742 : CollatzResearch.WordTrace tailWord_4521742 prefixEnd_4521742 2321827041622552897329893 := by
  unfold tailWord_4521742
  simp only [CollatzResearch.WordTrace]
  refine ⟨20615184948063557612072935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109947653056338973931055653 20615184948063557612072935)
  ·
    refine ⟨30922777422095336418109403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20615184948063557612072935 30922777422095336418109403)
    ·
      refine ⟨46384166133143004627164105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30922777422095336418109403 46384166133143004627164105)
      ·
        refine ⟨34788124599857253470373079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46384166133143004627164105 34788124599857253470373079)
        ·
          refine ⟨52182186899785880205559619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34788124599857253470373079 52182186899785880205559619)
          ·
            refine ⟨78273280349678820308339429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52182186899785880205559619 78273280349678820308339429)
            ·
              refine ⟨14676240065564778807813643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78273280349678820308339429 14676240065564778807813643)
              ·
                refine ⟨22014360098347168211720465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14676240065564778807813643 22014360098347168211720465)
                ·
                  refine ⟨16510770073760376158790349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22014360098347168211720465 16510770073760376158790349)
                  ·
                    refine ⟨6191538777660141059546381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16510770073760376158790349 6191538777660141059546381)
                    ·
                      refine ⟨2321827041622552897329893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6191538777660141059546381 2321827041622552897329893)
                      ·
                        rfl

theorem cell23_4521742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_4521742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521742 prefixEnd_4521742 := by exact prefixLift 4521742
  have htrace : WordTrace (prefixWord ++ tailWord_4521742) baseStart_4521742 baseEnd_4521742 := by
    simpa [prefixWord, tailWord_4521742, baseEnd_4521742] using wordTrace_append hprefix tailTrace_4521742
  have hstable : (prefixWord ++ tailWord_4521742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521742).length < 2 ^ (prefixWord ++ tailWord_4521742).sum := by decide
  have hdescent : baseEnd_4521742 < baseStart_4521742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521752 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 2, 5, 2]
def baseStart_4521752 : Nat := 118140960795 + 4521752 * 2 ^ 59
def prefixEnd_4521752 : Nat := 4983230072969 + 3 ^ 40 * 4521752 * 2
def baseEnd_4521752 : Nat := 2321832176429097858204847

theorem tailTrace_4521752 : CollatzResearch.WordTrace tailWord_4521752 prefixEnd_4521752 2321832176429097858204847 := by
  unfold tailWord_4521752
  simp only [CollatzResearch.WordTrace]
  refine ⟨82460922157236116302223755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109947896209648155069631673 82460922157236116302223755)
  ·
    refine ⟨123691383235854174453335633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82460922157236116302223755 123691383235854174453335633)
    ·
      refine ⟨92768537426890630840001725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123691383235854174453335633 92768537426890630840001725)
      ·
        refine ⟨34788201535083986565000647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92768537426890630840001725 34788201535083986565000647)
        ·
          refine ⟨52182302302625979847500971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34788201535083986565000647 52182302302625979847500971)
          ·
            refine ⟨78273453453938969771251457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52182302302625979847500971 78273453453938969771251457)
            ·
              refine ⟨58705090090454227328438593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78273453453938969771251457 58705090090454227328438593)
              ·
                refine ⟨44028817567840670496328945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58705090090454227328438593 44028817567840670496328945)
                ·
                  refine ⟨33021613175880502872246709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44028817567840670496328945 33021613175880502872246709)
                  ·
                    refine ⟨3095776235238797144273129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33021613175880502872246709 3095776235238797144273129)
                    ·
                      refine ⟨2321832176429097858204847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3095776235238797144273129 2321832176429097858204847)
                      ·
                        rfl

theorem cell23_4521752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_4521752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521752 prefixEnd_4521752 := by exact prefixLift 4521752
  have htrace : WordTrace (prefixWord ++ tailWord_4521752) baseStart_4521752 baseEnd_4521752 := by
    simpa [prefixWord, tailWord_4521752, baseEnd_4521752] using wordTrace_append hprefix tailTrace_4521752
  have hstable : (prefixWord ++ tailWord_4521752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521752).length < 2 ^ (prefixWord ++ tailWord_4521752).sum := by decide
  have hdescent : baseEnd_4521752 < baseStart_4521752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521762 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_4521762 : Nat := 118140960795 + 4521762 * 2 ^ 59
def prefixEnd_4521762 : Nat := 4983230072969 + 3 ^ 40 * 4521762 * 2
def baseEnd_4521762 : Nat := 773945770411880939693267

theorem tailTrace_4521762 : CollatzResearch.WordTrace tailWord_4521762 prefixEnd_4521762 773945770411880939693267 := by
  unfold tailWord_4521762
  simp only [CollatzResearch.WordTrace]
  refine ⟨41230552261109001078077885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109948139362957336208207693 41230552261109001078077885)
  ·
    refine ⟨15461457097915875404279207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41230552261109001078077885 15461457097915875404279207)
    ·
      refine ⟨23192185646873813106418811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15461457097915875404279207 23192185646873813106418811)
      ·
        refine ⟨34788278470310719659628217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23192185646873813106418811 34788278470310719659628217)
        ·
          refine ⟨26091208852733039744721163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34788278470310719659628217 26091208852733039744721163)
          ·
            refine ⟨39136813279099559617081745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26091208852733039744721163 39136813279099559617081745)
            ·
              refine ⟨29352609959324669712811309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39136813279099559617081745 29352609959324669712811309)
              ·
                refine ⟨11007228734746751142304241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29352609959324669712811309 11007228734746751142304241)
                ·
                  refine ⟨8255421551060063356728181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11007228734746751142304241 8255421551060063356728181)
                  ·
                    refine ⟨773945770411880939693267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8255421551060063356728181 773945770411880939693267)
                    ·
                      rfl

theorem cell23_4521762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_4521762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521762 prefixEnd_4521762 := by exact prefixLift 4521762
  have htrace : WordTrace (prefixWord ++ tailWord_4521762) baseStart_4521762 baseEnd_4521762 := by
    simpa [prefixWord, tailWord_4521762, baseEnd_4521762] using wordTrace_append hprefix tailTrace_4521762
  have hstable : (prefixWord ++ tailWord_4521762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521762).length < 2 ^ (prefixWord ++ tailWord_4521762).sum := by decide
  have hdescent : baseEnd_4521762 < baseStart_4521762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521802 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_4521802 : Nat := 118140960795 + 4521802 * 2 ^ 59
def prefixEnd_4521802 : Nat := 4983230072969 + 3 ^ 40 * 4521802 * 2
def baseEnd_4521802 : Nat := 2321857850461822662579617

theorem tailTrace_4521802 : CollatzResearch.WordTrace tailWord_4521802 prefixEnd_4521802 2321857850461822662579617 := by
  unfold tailWord_4521802
  simp only [CollatzResearch.WordTrace]
  refine ⟨41230916991072772785941915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109949111976194060762511773 41230916991072772785941915)
  ·
    refine ⟨61846375486609159178912873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41230916991072772785941915 61846375486609159178912873)
    ·
      refine ⟨46384781614956869384184655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61846375486609159178912873 46384781614956869384184655)
      ·
        refine ⟨69577172422435304076276983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46384781614956869384184655 69577172422435304076276983)
        ·
          refine ⟨104365758633652956114415475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69577172422435304076276983 104365758633652956114415475)
          ·
            refine ⟨156548637950479434171623213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104365758633652956114415475 156548637950479434171623213)
            ·
              refine ⟨58705739231429787814358705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156548637950479434171623213 58705739231429787814358705)
              ·
                refine ⟨44029304423572340860769029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58705739231429787814358705 44029304423572340860769029)
                ·
                  refine ⟨8255494579419813911394193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44029304423572340860769029 8255494579419813911394193)
                  ·
                    refine ⟨6191620934564860433545645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8255494579419813911394193 6191620934564860433545645)
                    ·
                      refine ⟨2321857850461822662579617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6191620934564860433545645 2321857850461822662579617)
                      ·
                        rfl

theorem cell23_4521802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_4521802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521802 prefixEnd_4521802 := by exact prefixLift 4521802
  have htrace : WordTrace (prefixWord ++ tailWord_4521802) baseStart_4521802 baseEnd_4521802 := by
    simpa [prefixWord, tailWord_4521802, baseEnd_4521802] using wordTrace_append hprefix tailTrace_4521802
  have hstable : (prefixWord ++ tailWord_4521802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521802).length < 2 ^ (prefixWord ++ tailWord_4521802).sum := by decide
  have hdescent : baseEnd_4521802 < baseStart_4521802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521849 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 3, 1, 3]
def baseStart_4521849 : Nat := 118140960795 + 4521849 * 2 ^ 59
def prefixEnd_4521849 : Nat := 4983230072969 + 3 ^ 40 * 4521849 * 2
def baseEnd_4521849 : Nat := 2321881984052583978691901

theorem tailTrace_4521849 : CollatzResearch.WordTrace tailWord_4521849 prefixEnd_4521849 2321881984052583978691901 := by
  unfold tailWord_4521849
  simp only [CollatzResearch.WordTrace]
  refine ⟨164925382195120818170728601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109950254796747212113819067 164925382195120818170728601)
  ·
    refine ⟨123694036646340613628046451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164925382195120818170728601 123694036646340613628046451)
    ·
      refine ⟨185541054969510920442069677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123694036646340613628046451 185541054969510920442069677)
      ·
        refine ⟨69577895613566595165776129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185541054969510920442069677 69577895613566595165776129)
        ·
          refine ⟨52183421710174946374332097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69577895613566595165776129 52183421710174946374332097)
          ·
            refine ⟨39137566282631209780749073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52183421710174946374332097 39137566282631209780749073)
            ·
              refine ⟨29353174711973407335561805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39137566282631209780749073 29353174711973407335561805)
              ·
                refine ⟨11007440516990027750835677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29353174711973407335561805 11007440516990027750835677)
                ·
                  refine ⟨4127790193871260406563379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11007440516990027750835677 4127790193871260406563379)
                  ·
                    refine ⟨6191685290806890609845069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4127790193871260406563379 6191685290806890609845069)
                    ·
                      refine ⟨2321881984052583978691901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6191685290806890609845069 2321881984052583978691901)
                      ·
                        rfl

theorem cell23_4521849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_4521849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521849 prefixEnd_4521849 := by exact prefixLift 4521849
  have htrace : WordTrace (prefixWord ++ tailWord_4521849) baseStart_4521849 baseEnd_4521849 := by
    simpa [prefixWord, tailWord_4521849, baseEnd_4521849] using wordTrace_append hprefix tailTrace_4521849
  have hstable : (prefixWord ++ tailWord_4521849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521849).length < 2 ^ (prefixWord ++ tailWord_4521849).sum := by decide
  have hdescent : baseEnd_4521849 < baseStart_4521849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521870 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3]
def baseStart_4521870 : Nat := 118140960795 + 4521870 * 2 ^ 59
def prefixEnd_4521870 : Nat := 4983230072969 + 3 ^ 40 * 4521870 * 2
def baseEnd_4521870 : Nat := 2321892767146328396529305

theorem tailTrace_4521870 : CollatzResearch.WordTrace tailWord_4521870 prefixEnd_4521870 2321892767146328396529305 := by
  unfold tailWord_4521870
  simp only [CollatzResearch.WordTrace]
  refine ⟨20615768516005592344655383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109950765418696492504828709 20615768516005592344655383)
  ·
    refine ⟨30923652774008388516983075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20615768516005592344655383 30923652774008388516983075)
    ·
      refine ⟨46385479161012582775474613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30923652774008388516983075 46385479161012582775474613)
      ·
        refine ⟨4348638671344929635200745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46385479161012582775474613 4348638671344929635200745)
        ·
          refine ⟨3261479003508697226400559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4348638671344929635200745 3261479003508697226400559)
          ·
            refine ⟨4892218505263045839600839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3261479003508697226400559 4892218505263045839600839)
            ·
              refine ⟨7338327757894568759401259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4892218505263045839600839 7338327757894568759401259)
              ·
                refine ⟨11007491636841853139101889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7338327757894568759401259 11007491636841853139101889)
                ·
                  refine ⟨8255618727631389854326417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11007491636841853139101889 8255618727631389854326417)
                  ·
                    refine ⟨6191714045723542390744813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8255618727631389854326417 6191714045723542390744813)
                    ·
                      refine ⟨2321892767146328396529305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6191714045723542390744813 2321892767146328396529305)
                      ·
                        rfl

theorem cell23_4521870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_4521870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521870 prefixEnd_4521870 := by exact prefixLift 4521870
  have htrace : WordTrace (prefixWord ++ tailWord_4521870) baseStart_4521870 baseEnd_4521870 := by
    simpa [prefixWord, tailWord_4521870, baseEnd_4521870] using wordTrace_append hprefix tailTrace_4521870
  have hstable : (prefixWord ++ tailWord_4521870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521870).length < 2 ^ (prefixWord ++ tailWord_4521870).sum := by decide
  have hdescent : baseEnd_4521870 < baseStart_4521870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521876 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_4521876 : Nat := 118140960795 + 4521876 * 2 ^ 59
def prefixEnd_4521876 : Nat := 4983230072969 + 3 ^ 40 * 4521876 * 2
def baseEnd_4521876 : Nat := 2321895848030255373054277

theorem tailTrace_4521876 : CollatzResearch.WordTrace tailWord_4521876 prefixEnd_4521876 2321895848030255373054277 := by
  unfold tailWord_4521876
  simp only [CollatzResearch.WordTrace]
  refine ⟨82463183483011500890980741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109950911310682001187974321 82463183483011500890980741)
  ·
    refine ⟨15461846903064656417058889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82463183483011500890980741 15461846903064656417058889)
    ·
      refine ⟨11596385177298492312794167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15461846903064656417058889 11596385177298492312794167)
      ·
        refine ⟨17394577765947738469191251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11596385177298492312794167 17394577765947738469191251)
        ·
          refine ⟨26091866648921607703786877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17394577765947738469191251 26091866648921607703786877)
          ·
            refine ⟨9784449993345602888920079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26091866648921607703786877 9784449993345602888920079)
            ·
              refine ⟨14676674990018404333380119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9784449993345602888920079 14676674990018404333380119)
              ·
                refine ⟨22015012485027606500070179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14676674990018404333380119 22015012485027606500070179)
                ·
                  refine ⟨33022518727541409750105269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22015012485027606500070179 33022518727541409750105269)
                  ·
                    refine ⟨3095861130707007164072369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33022518727541409750105269 3095861130707007164072369)
                    ·
                      refine ⟨2321895848030255373054277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3095861130707007164072369 2321895848030255373054277)
                      ·
                        rfl

theorem cell23_4521876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_4521876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521876 prefixEnd_4521876 := by exact prefixLift 4521876
  have htrace : WordTrace (prefixWord ++ tailWord_4521876) baseStart_4521876 baseEnd_4521876 := by
    simpa [prefixWord, tailWord_4521876, baseEnd_4521876] using wordTrace_append hprefix tailTrace_4521876
  have hstable : (prefixWord ++ tailWord_4521876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521876).length < 2 ^ (prefixWord ++ tailWord_4521876).sum := by decide
  have hdescent : baseEnd_4521876 < baseStart_4521876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521909 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_4521909 : Nat := 118140960795 + 4521909 * 2 ^ 59
def prefixEnd_4521909 : Nat := 4983230072969 + 3 ^ 40 * 4521909 * 2
def baseEnd_4521909 : Nat := 2321912792891853743941625

theorem tailTrace_4521909 : CollatzResearch.WordTrace tailWord_4521909 prefixEnd_4521909 2321912792891853743941625 := by
  unfold tailWord_4521909
  simp only [CollatzResearch.WordTrace]
  refine ⟨164927570574903448417912781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109951713716602298945275187 164927570574903448417912781)
  ·
    refine ⟨61847838965588793156717293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164927570574903448417912781 61847838965588793156717293)
    ·
      refine ⟨23192939612095797433768985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61847838965588793156717293 23192939612095797433768985)
      ·
        refine ⟨17394704709071848075326739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23192939612095797433768985 17394704709071848075326739)
        ·
          refine ⟨26092057063607772112990109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17394704709071848075326739 26092057063607772112990109)
          ·
            refine ⟨9784521398852914542371291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26092057063607772112990109 9784521398852914542371291)
            ·
              refine ⟨14676782098279371813556937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9784521398852914542371291 14676782098279371813556937)
              ·
                refine ⟨11007586573709528860167703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14676782098279371813556937 11007586573709528860167703)
                ·
                  refine ⟨16511379860564293290251555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11007586573709528860167703 16511379860564293290251555)
                  ·
                    refine ⟨24767069790846439935377333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16511379860564293290251555 24767069790846439935377333)
                    ·
                      refine ⟨2321912792891853743941625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24767069790846439935377333 2321912792891853743941625)
                      ·
                        rfl

theorem cell23_4521909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_4521909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521909 prefixEnd_4521909 := by exact prefixLift 4521909
  have htrace : WordTrace (prefixWord ++ tailWord_4521909) baseStart_4521909 baseEnd_4521909 := by
    simpa [prefixWord, tailWord_4521909, baseEnd_4521909] using wordTrace_append hprefix tailTrace_4521909
  have hstable : (prefixWord ++ tailWord_4521909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521909).length < 2 ^ (prefixWord ++ tailWord_4521909).sum := by decide
  have hdescent : baseEnd_4521909 < baseStart_4521909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521956 : List Nat := [2, 3, 1, 1, 1, 1, 4, 4, 2, 1, 3]
def baseStart_4521956 : Nat := 118140960795 + 4521956 * 2 ^ 59
def prefixEnd_4521956 : Nat := 4983230072969 + 3 ^ 40 * 4521956 * 2
def baseEnd_4521956 : Nat := 2321936926482615060053909

theorem tailTrace_4521956 : CollatzResearch.WordTrace tailWord_4521956 prefixEnd_4521956 2321936926482615060053909 := by
  unfold tailWord_4521956
  simp only [CollatzResearch.WordTrace]
  refine ⟨82464642402866587722436861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109952856537155450296582481 82464642402866587722436861)
  ·
    refine ⟨30924240901074970395913823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82464642402866587722436861 30924240901074970395913823)
    ·
      refine ⟨46386361351612455593870735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30924240901074970395913823 46386361351612455593870735)
      ·
        refine ⟨69579542027418683390806103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46386361351612455593870735 69579542027418683390806103)
        ·
          refine ⟨104369313041128025086209155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69579542027418683390806103 104369313041128025086209155)
          ·
            refine ⟨156553969561692037629313733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104369313041128025086209155 156553969561692037629313733)
            ·
              refine ⟨29353869292817257055496325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156553969561692037629313733 29353869292817257055496325)
              ·
                refine ⟨5503850492403235697905561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29353869292817257055496325 5503850492403235697905561)
                ·
                  refine ⟨4127887869302426773429171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5503850492403235697905561 4127887869302426773429171)
                  ·
                    refine ⟨6191831803953640160143757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4127887869302426773429171 6191831803953640160143757)
                    ·
                      refine ⟨2321936926482615060053909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6191831803953640160143757 2321936926482615060053909)
                      ·
                        rfl

theorem cell23_4521956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_4521956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521956 prefixEnd_4521956 := by exact prefixLift 4521956
  have htrace : WordTrace (prefixWord ++ tailWord_4521956) baseStart_4521956 baseEnd_4521956 := by
    simpa [prefixWord, tailWord_4521956, baseEnd_4521956] using wordTrace_append hprefix tailTrace_4521956
  have hstable : (prefixWord ++ tailWord_4521956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521956).length < 2 ^ (prefixWord ++ tailWord_4521956).sum := by decide
  have hdescent : baseEnd_4521956 < baseStart_4521956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4521996 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 1, 4, 2]
def baseStart_4521996 : Nat := 118140960795 + 4521996 * 2 ^ 59
def prefixEnd_4521996 : Nat := 4983230072969 + 3 ^ 40 * 4521996 * 2
def baseEnd_4521996 : Nat := 2321957465708794903553725

theorem tailTrace_4521996 : CollatzResearch.WordTrace tailWord_4521996 prefixEnd_4521996 2321957465708794903553725 := by
  unfold tailWord_4521996
  simp only [CollatzResearch.WordTrace]
  refine ⟨82465371862794131138164921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109953829150392174850886561 82465371862794131138164921)
  ·
    refine ⟨61849028897095598353623691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82465371862794131138164921 61849028897095598353623691)
    ·
      refine ⟨92773543345643397530435537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61849028897095598353623691 92773543345643397530435537)
      ·
        refine ⟨69580157509232548147826653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92773543345643397530435537 69580157509232548147826653)
        ·
          refine ⟨26092559065962205555434995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69580157509232548147826653 26092559065962205555434995)
          ·
            refine ⟨39138838598943308333152493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26092559065962205555434995 39138838598943308333152493)
            ·
              refine ⟨14677064474603740624932185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39138838598943308333152493 14677064474603740624932185)
              ·
                refine ⟨11007798355952805468699139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14677064474603740624932185 11007798355952805468699139)
                ·
                  refine ⟨16511697533929208203048709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11007798355952805468699139 16511697533929208203048709)
                  ·
                    refine ⟨3095943287611726538071633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16511697533929208203048709 3095943287611726538071633)
                    ·
                      refine ⟨2321957465708794903553725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3095943287611726538071633 2321957465708794903553725)
                      ·
                        rfl

theorem cell23_4521996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_4521996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4521996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4521996 prefixEnd_4521996 := by exact prefixLift 4521996
  have htrace : WordTrace (prefixWord ++ tailWord_4521996) baseStart_4521996 baseEnd_4521996 := by
    simpa [prefixWord, tailWord_4521996, baseEnd_4521996] using wordTrace_append hprefix tailTrace_4521996
  have hstable : (prefixWord ++ tailWord_4521996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4521996).length < 2 ^ (prefixWord ++ tailWord_4521996).sum := by decide
  have hdescent : baseEnd_4521996 < baseStart_4521996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4521996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522026 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_4522026 : Nat := 118140960795 + 4522026 * 2 ^ 59
def prefixEnd_4522026 : Nat := 4983230072969 + 3 ^ 40 * 4522026 * 2
def baseEnd_4522026 : Nat := 2321972870128429786178587

theorem tailTrace_4522026 : CollatzResearch.WordTrace tailWord_4522026 prefixEnd_4522026 2321972870128429786178587 := by
  unfold tailWord_4522026
  simp only [CollatzResearch.WordTrace]
  refine ⟨41232959478869894349980483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109954558610319718266614621 41232959478869894349980483)
  ·
    refine ⟨61849439218304841524970725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41232959478869894349980483 61849439218304841524970725)
    ·
      refine ⟨11596769853432157785932011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61849439218304841524970725 11596769853432157785932011)
      ·
        refine ⟨17395154780148236678898017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11596769853432157785932011 17395154780148236678898017)
        ·
          refine ⟨13046366085111177509173513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17395154780148236678898017 13046366085111177509173513)
          ·
            refine ⟨9784774563833383131880135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13046366085111177509173513 9784774563833383131880135)
            ·
              refine ⟨14677161845750074697820203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9784774563833383131880135 14677161845750074697820203)
              ·
                refine ⟨22015742768625112046730305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14677161845750074697820203 22015742768625112046730305)
                ·
                  refine ⟨16511807076468834035047729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22015742768625112046730305 16511807076468834035047729)
                  ·
                    refine ⟨12383855307351625526285797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16511807076468834035047729 12383855307351625526285797)
                    ·
                      refine ⟨2321972870128429786178587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12383855307351625526285797 2321972870128429786178587)
                      ·
                        rfl

theorem cell23_4522026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_4522026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522026 prefixEnd_4522026 := by exact prefixLift 4522026
  have htrace : WordTrace (prefixWord ++ tailWord_4522026) baseStart_4522026 baseEnd_4522026 := by
    simpa [prefixWord, tailWord_4522026, baseEnd_4522026] using wordTrace_append hprefix tailTrace_4522026
  have hstable : (prefixWord ++ tailWord_4522026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522026).length < 2 ^ (prefixWord ++ tailWord_4522026).sum := by decide
  have hdescent : baseEnd_4522026 < baseStart_4522026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522030 : List Nat := [4, 1, 3, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_4522030 : Nat := 118140960795 + 4522030 * 2 ^ 59
def prefixEnd_4522030 : Nat := 4983230072969 + 3 ^ 40 * 4522030 * 2
def baseEnd_4522030 : Nat := 2321974924051047770528569

theorem tailTrace_4522030 : CollatzResearch.WordTrace tailWord_4522030 prefixEnd_4522030 2321974924051047770528569 := by
  unfold tailWord_4522030
  simp only [CollatzResearch.WordTrace]
  refine ⟨20616497975933135760383443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109954655871643390722045029 20616497975933135760383443)
  ·
    refine ⟨30924746963899703640575165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20616497975933135760383443 30924746963899703640575165)
    ·
      refine ⟨11596780111462388865215687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30924746963899703640575165 11596780111462388865215687)
      ·
        refine ⟨17395170167193583297823531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11596780111462388865215687 17395170167193583297823531)
        ·
          refine ⟨26092755250790374946735297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17395170167193583297823531 26092755250790374946735297)
          ·
            refine ⟨19569566438092781210051473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26092755250790374946735297 19569566438092781210051473)
            ·
              refine ⟨14677174828569585907538605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19569566438092781210051473 14677174828569585907538605)
              ·
                refine ⟨5503940560713594715326977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14677174828569585907538605 5503940560713594715326977)
                ·
                  refine ⟨4127955420535196036495233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5503940560713594715326977 4127955420535196036495233)
                  ·
                    refine ⟨3095966565401397027371425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4127955420535196036495233 3095966565401397027371425)
                    ·
                      refine ⟨2321974924051047770528569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3095966565401397027371425 2321974924051047770528569)
                      ·
                        rfl

theorem cell23_4522030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_4522030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522030 prefixEnd_4522030 := by exact prefixLift 4522030
  have htrace : WordTrace (prefixWord ++ tailWord_4522030) baseStart_4522030 baseEnd_4522030 := by
    simpa [prefixWord, tailWord_4522030, baseEnd_4522030] using wordTrace_append hprefix tailTrace_4522030
  have hstable : (prefixWord ++ tailWord_4522030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522030).length < 2 ^ (prefixWord ++ tailWord_4522030).sum := by decide
  have hdescent : baseEnd_4522030 < baseStart_4522030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522070 : List Nat := [5, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_4522070 : Nat := 118140960795 + 4522070 * 2 ^ 59
def prefixEnd_4522070 : Nat := 4983230072969 + 3 ^ 40 * 4522070 * 2
def baseEnd_4522070 : Nat := 257999495919691957114265

theorem tailTrace_4522070 : CollatzResearch.WordTrace tailWord_4522070 prefixEnd_4522070 257999495919691957114265 := by
  unfold tailWord_4522070
  simp only [CollatzResearch.WordTrace]
  refine ⟨10308340170457510807157729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109955628484880115276349109 10308340170457510807157729)
  ·
    refine ⟨7731255127843133105368297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10308340170457510807157729 7731255127843133105368297)
    ·
      refine ⟨5798441345882349829026223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7731255127843133105368297 5798441345882349829026223)
      ·
        refine ⟨8697662018823524743539335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5798441345882349829026223 8697662018823524743539335)
        ·
          refine ⟨13046493028235287115309003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8697662018823524743539335 13046493028235287115309003)
          ·
            refine ⟨19569739542352930672963505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13046493028235287115309003 19569739542352930672963505)
            ·
              refine ⟨14677304656764698004722629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19569739542352930672963505 14677304656764698004722629)
              ·
                refine ⟨2751994623143380875885493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14677304656764698004722629 2751994623143380875885493)
                ·
                  refine ⟨257999495919691957114265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2751994623143380875885493 257999495919691957114265)
                  ·
                    rfl

theorem cell23_4522070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_4522070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522070 prefixEnd_4522070 := by exact prefixLift 4522070
  have htrace : WordTrace (prefixWord ++ tailWord_4522070) baseStart_4522070 baseEnd_4522070 := by
    simpa [prefixWord, tailWord_4522070, baseEnd_4522070] using wordTrace_append hprefix tailTrace_4522070
  have hstable : (prefixWord ++ tailWord_4522070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522070).length < 2 ^ (prefixWord ++ tailWord_4522070).sum := by decide
  have hdescent : baseEnd_4522070 < baseStart_4522070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522089 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 3, 4, 3]
def baseStart_4522089 : Nat := 118140960795 + 4522089 * 2 ^ 59
def prefixEnd_4522089 : Nat := 4983230072969 + 3 ^ 40 * 4522089 * 2
def baseEnd_4522089 : Nat := 2322005219409663039690797

theorem tailTrace_4522089 : CollatzResearch.WordTrace tailWord_4522089 prefixEnd_4522089 2322005219409663039690797 := by
  unfold tailWord_4522089
  simp only [CollatzResearch.WordTrace]
  refine ⟨164934135714251339159465321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109956090476167559439643547 164934135714251339159465321)
  ·
    refine ⟨123700601785688504369598991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164934135714251339159465321 123700601785688504369598991)
    ·
      refine ⟨185550902678532756554398487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123700601785688504369598991 185550902678532756554398487)
      ·
        refine ⟨278326354017799134831597731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185550902678532756554398487 278326354017799134831597731)
        ·
          refine ⟨417489531026698702247396597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278326354017799134831597731 417489531026698702247396597)
          ·
            refine ⟨39139643533753003335693431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 417489531026698702247396597 39139643533753003335693431)
            ·
              refine ⟨58709465300629505003540147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39139643533753003335693431 58709465300629505003540147)
              ·
                refine ⟨88064197950944257505310221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58709465300629505003540147 88064197950944257505310221)
                ·
                  refine ⟨33024074231604096564491333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88064197950944257505310221 33024074231604096564491333)
                  ·
                    refine ⟨6192013918425768105842125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33024074231604096564491333 6192013918425768105842125)
                    ·
                      refine ⟨2322005219409663039690797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6192013918425768105842125 2322005219409663039690797)
                      ·
                        rfl

theorem cell23_4522089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 4, 3].length) (baseStart_4522089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522089 prefixEnd_4522089 := by exact prefixLift 4522089
  have htrace : WordTrace (prefixWord ++ tailWord_4522089) baseStart_4522089 baseEnd_4522089 := by
    simpa [prefixWord, tailWord_4522089, baseEnd_4522089] using wordTrace_append hprefix tailTrace_4522089
  have hstable : (prefixWord ++ tailWord_4522089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522089).length < 2 ^ (prefixWord ++ tailWord_4522089).sum := by decide
  have hdescent : baseEnd_4522089 < baseStart_4522089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522096 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 3, 4]
def baseStart_4522096 : Nat := 118140960795 + 4522096 * 2 ^ 59
def prefixEnd_4522096 : Nat := 4983230072969 + 3 ^ 40 * 4522096 * 2
def baseEnd_4522096 : Nat := 774002937924748170767755

theorem tailTrace_4522096 : CollatzResearch.WordTrace tailWord_4522096 prefixEnd_4522096 774002937924748170767755 := by
  unfold tailWord_4522096
  simp only [CollatzResearch.WordTrace]
  refine ⟨82467195512612989677485071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109956260683483986236646761 82467195512612989677485071)
  ·
    refine ⟨123700793268919484516227607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82467195512612989677485071 123700793268919484516227607)
    ·
      refine ⟨185551189903379226774341411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123700793268919484516227607 185551189903379226774341411)
      ·
        refine ⟨278326784855068840161512117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185551189903379226774341411 278326784855068840161512117)
        ·
          refine ⟨26093136080162703765141761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 278326784855068840161512117 26093136080162703765141761)
          ·
            refine ⟨19569852060122027823856321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26093136080162703765141761 19569852060122027823856321)
            ·
              refine ⟨14677389045091520867892241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19569852060122027823856321 14677389045091520867892241)
              ·
                refine ⟨11008041783818640650919181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14677389045091520867892241 11008041783818640650919181)
                ·
                  refine ⟨4128015668931990244094693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11008041783818640650919181 4128015668931990244094693)
                  ·
                    refine ⟨774002937924748170767755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4128015668931990244094693 774002937924748170767755)
                    ·
                      rfl

theorem cell23_4522096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 3, 4].length) (baseStart_4522096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522096 prefixEnd_4522096 := by exact prefixLift 4522096
  have htrace : WordTrace (prefixWord ++ tailWord_4522096) baseStart_4522096 baseEnd_4522096 := by
    simpa [prefixWord, tailWord_4522096, baseEnd_4522096] using wordTrace_append hprefix tailTrace_4522096
  have hstable : (prefixWord ++ tailWord_4522096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522096).length < 2 ^ (prefixWord ++ tailWord_4522096).sum := by decide
  have hdescent : baseEnd_4522096 < baseStart_4522096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522109 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 8]
def baseStart_4522109 : Nat := 118140960795 + 4522109 * 2 ^ 59
def prefixEnd_4522109 : Nat := 4983230072969 + 3 ^ 40 * 4522109 * 2
def baseEnd_4522109 : Nat := 258001721002528106826745

theorem tailTrace_4522109 : CollatzResearch.WordTrace tailWord_4522109 prefixEnd_4522109 258001721002528106826745 := by
  unfold tailWord_4522109
  simp only [CollatzResearch.WordTrace]
  refine ⟨164934865174178882575193381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109956576782785921716795587 164934865174178882575193381)
  ·
    refine ⟨30925287220158540482848759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164934865174178882575193381 30925287220158540482848759)
    ·
      refine ⟨46387930830237810724273139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30925287220158540482848759 46387930830237810724273139)
      ·
        refine ⟨69581896245356716086409709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46387930830237810724273139 69581896245356716086409709)
        ·
          refine ⟨26093211092008768532403641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69581896245356716086409709 26093211092008768532403641)
          ·
            refine ⟨19569908319006576399302731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26093211092008768532403641 19569908319006576399302731)
            ·
              refine ⟨29354862478509864598954097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19569908319006576399302731 29354862478509864598954097)
              ·
                refine ⟨22016146858882398449215573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29354862478509864598954097 22016146858882398449215573)
                ·
                  refine ⟨258001721002528106826745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22016146858882398449215573 258001721002528106826745)
                  ·
                    rfl

theorem cell23_4522109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_4522109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522109 prefixEnd_4522109 := by exact prefixLift 4522109
  have htrace : WordTrace (prefixWord ++ tailWord_4522109) baseStart_4522109 baseEnd_4522109 := by
    simpa [prefixWord, tailWord_4522109, baseEnd_4522109] using wordTrace_append hprefix tailTrace_4522109
  have hstable : (prefixWord ++ tailWord_4522109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522109).length < 2 ^ (prefixWord ++ tailWord_4522109).sum := by decide
  have hdescent : baseEnd_4522109 < baseStart_4522109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522143 : List Nat := [1, 1, 2, 6, 1, 1, 4, 1, 6]
def baseStart_4522143 : Nat := 118140960795 + 4522143 * 2 ^ 59
def prefixEnd_4522143 : Nat := 4983230072969 + 3 ^ 40 * 4522143 * 2
def baseEnd_4522143 : Nat := 258003660818333980935061

theorem tailTrace_4522143 : CollatzResearch.WordTrace tailWord_4522143 prefixEnd_4522143 258003660818333980935061 := by
  unfold tailWord_4522143
  simp only [CollatzResearch.WordTrace]
  refine ⟨164936105256055706381931083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109957403504037137587954055 164936105256055706381931083)
  ·
    refine ⟨247404157884083559572896625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164936105256055706381931083 247404157884083559572896625)
    ·
      refine ⟨185553118413062669679672469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247404157884083559572896625 185553118413062669679672469)
      ·
        refine ⟨8697802425612312641234647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 185553118413062669679672469 8697802425612312641234647)
        ·
          refine ⟨13046703638418468961851971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8697802425612312641234647 13046703638418468961851971)
          ·
            refine ⟨19570055457627703442777957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13046703638418468961851971 19570055457627703442777957)
            ·
              refine ⟨3669385398305194395520867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19570055457627703442777957 3669385398305194395520867)
              ·
                refine ⟨5504078097457791593281301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3669385398305194395520867 5504078097457791593281301)
                ·
                  refine ⟨258003660818333980935061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5504078097457791593281301 258003660818333980935061)
                  ·
                    rfl

theorem cell23_4522143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 6].length) (baseStart_4522143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522143 prefixEnd_4522143 := by exact prefixLift 4522143
  have htrace : WordTrace (prefixWord ++ tailWord_4522143) baseStart_4522143 baseEnd_4522143 := by
    simpa [prefixWord, tailWord_4522143, baseEnd_4522143] using wordTrace_append hprefix tailTrace_4522143
  have hstable : (prefixWord ++ tailWord_4522143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522143).length < 2 ^ (prefixWord ++ tailWord_4522143).sum := by decide
  have hdescent : baseEnd_4522143 < baseStart_4522143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522180 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_4522180 : Nat := 118140960795 + 4522180 * 2 ^ 59
def prefixEnd_4522180 : Nat := 4983230072969 + 3 ^ 40 * 4522180 * 2
def baseEnd_4522180 : Nat := 2322051946149222183652879

theorem tailTrace_4522180 : CollatzResearch.WordTrace tailWord_4522180 prefixEnd_4522180 2322051946149222183652879 := by
  unfold tailWord_4522180
  simp only [CollatzResearch.WordTrace]
  refine ⟨82468727378460830850513997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109958303171281107800685329 82468727378460830850513997)
  ·
    refine ⟨30925772766922811568942749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82468727378460830850513997 30925772766922811568942749)
    ·
      refine ⟨11597164787596054338353531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30925772766922811568942749 11597164787596054338353531)
      ·
        refine ⟨17395747181394081507530297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11597164787596054338353531 17395747181394081507530297)
        ·
          refine ⟨13046810386045561130647723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17395747181394081507530297 13046810386045561130647723)
          ·
            refine ⟨19570215579068341695971585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13046810386045561130647723 19570215579068341695971585)
            ·
              refine ⟨14677661684301256271978689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19570215579068341695971585 14677661684301256271978689)
              ·
                refine ⟨11008246263225942203984017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14677661684301256271978689 11008246263225942203984017)
                ·
                  refine ⟨8256184697419456652988013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11008246263225942203984017 8256184697419456652988013)
                  ·
                    refine ⟨3096069261532296244870505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8256184697419456652988013 3096069261532296244870505)
                    ·
                      refine ⟨2322051946149222183652879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3096069261532296244870505 2322051946149222183652879)
                      ·
                        rfl

theorem cell23_4522180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_4522180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522180 prefixEnd_4522180 := by exact prefixLift 4522180
  have htrace : WordTrace (prefixWord ++ tailWord_4522180) baseStart_4522180 baseEnd_4522180 := by
    simpa [prefixWord, tailWord_4522180, baseEnd_4522180] using wordTrace_append hprefix tailTrace_4522180
  have hstable : (prefixWord ++ tailWord_4522180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522180).length < 2 ^ (prefixWord ++ tailWord_4522180).sum := by decide
  have hdescent : baseEnd_4522180 < baseStart_4522180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522213 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 3, 2, 3]
def baseStart_4522213 : Nat := 118140960795 + 4522213 * 2 ^ 59
def prefixEnd_4522213 : Nat := 4983230072969 + 3 ^ 40 * 4522213 * 2
def baseEnd_4522213 : Nat := 2322068891010820554540227

theorem tailTrace_4522213 : CollatzResearch.WordTrace tailWord_4522213 prefixEnd_4522213 2322068891010820554540227 := by
  unfold tailWord_4522213
  simp only [CollatzResearch.WordTrace]
  refine ⟨164938658365802108336979293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109959105577201405557986195 164938658365802108336979293)
  ·
    refine ⟨61851996887175790626367235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164938658365802108336979293 61851996887175790626367235)
    ·
      refine ⟨92777995330763685939550853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61851996887175790626367235 92777995330763685939550853)
      ·
        refine ⟨17395874124518191113665785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92777995330763685939550853 17395874124518191113665785)
        ·
          refine ⟨13046905593388643335249339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17395874124518191113665785 13046905593388643335249339)
          ·
            refine ⟨19570358390082965002874009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13046905593388643335249339 19570358390082965002874009)
            ·
              refine ⟨14677768792562223752155507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19570358390082965002874009 14677768792562223752155507)
              ·
                refine ⟨22016653188843335628233261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14677768792562223752155507 22016653188843335628233261)
                ·
                  refine ⟨8256244945816250860587473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22016653188843335628233261 8256244945816250860587473)
                  ·
                    refine ⟨6192183709362188145440605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8256244945816250860587473 6192183709362188145440605)
                    ·
                      refine ⟨2322068891010820554540227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6192183709362188145440605 2322068891010820554540227)
                      ·
                        rfl

theorem cell23_4522213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_4522213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522213 prefixEnd_4522213 := by exact prefixLift 4522213
  have htrace : WordTrace (prefixWord ++ tailWord_4522213) baseStart_4522213 baseEnd_4522213 := by
    simpa [prefixWord, tailWord_4522213, baseEnd_4522213] using wordTrace_append hprefix tailTrace_4522213
  have hstable : (prefixWord ++ tailWord_4522213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522213).length < 2 ^ (prefixWord ++ tailWord_4522213).sum := by decide
  have hdescent : baseEnd_4522213 < baseStart_4522213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522227 : List Nat := [1, 1, 1, 2, 2, 4, 4, 3, 1, 2, 2]
def baseStart_4522227 : Nat := 118140960795 + 4522227 * 2 ^ 59
def prefixEnd_4522227 : Nat := 4983230072969 + 3 ^ 40 * 4522227 * 2
def baseEnd_4522227 : Nat := 2322076079739983499765163

theorem tailTrace_4522227 : CollatzResearch.WordTrace tailWord_4522227 prefixEnd_4522227 2322076079739983499765163 := by
  unfold tailWord_4522227
  simp only [CollatzResearch.WordTrace]
  refine ⟨164939168987751388727988935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109959445991834259151992623 164939168987751388727988935)
  ·
    refine ⟨247408753481627083091983403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164939168987751388727988935 247408753481627083091983403)
    ·
      refine ⟨371113130222440624637975105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247408753481627083091983403 371113130222440624637975105)
      ·
        refine ⟨278334847666830468478481329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371113130222440624637975105 278334847666830468478481329)
        ·
          refine ⟨208751135750122851358860997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278334847666830468478481329 208751135750122851358860997)
          ·
            refine ⟨39140837953148034629786437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 208751135750122851358860997 39140837953148034629786437)
            ·
              refine ⟨7338907116215256493084957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39140837953148034629786437 7338907116215256493084957)
              ·
                refine ⟨2752090168580721184906859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7338907116215256493084957 2752090168580721184906859)
                ·
                  refine ⟨4128135252871081777360289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2752090168580721184906859 4128135252871081777360289)
                  ·
                    refine ⟨3096101439653311333020217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4128135252871081777360289 3096101439653311333020217)
                    ·
                      refine ⟨2322076079739983499765163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3096101439653311333020217 2322076079739983499765163)
                      ·
                        rfl

theorem cell23_4522227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 1, 2, 2].length) (baseStart_4522227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522227 prefixEnd_4522227 := by exact prefixLift 4522227
  have htrace : WordTrace (prefixWord ++ tailWord_4522227) baseStart_4522227 baseEnd_4522227 := by
    simpa [prefixWord, tailWord_4522227, baseEnd_4522227] using wordTrace_append hprefix tailTrace_4522227
  have hstable : (prefixWord ++ tailWord_4522227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522227).length < 2 ^ (prefixWord ++ tailWord_4522227).sum := by decide
  have hdescent : baseEnd_4522227 < baseStart_4522227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522243 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 4, 1, 3]
def baseStart_4522243 : Nat := 118140960795 + 4522243 * 2 ^ 59
def prefixEnd_4522243 : Nat := 4983230072969 + 3 ^ 40 * 4522243 * 2
def baseEnd_4522243 : Nat := 2322084295430455437165089

theorem tailTrace_4522243 : CollatzResearch.WordTrace tailWord_4522243 prefixEnd_4522243 2322084295430455437165089 := by
  unfold tailWord_4522243
  simp only [CollatzResearch.WordTrace]
  refine ⟨164939752555693423460571383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109959835037128948973714255 164939752555693423460571383)
  ·
    refine ⟨247409628833540135190857075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164939752555693423460571383 247409628833540135190857075)
    ·
      refine ⟨371114443250310202786285613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247409628833540135190857075 371114443250310202786285613)
      ·
        refine ⟨139167916218866326044857105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 371114443250310202786285613 139167916218866326044857105)
        ·
          refine ⟨104375937164149744533642829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139167916218866326044857105 104375937164149744533642829)
          ·
            refine ⟨39140976436556154200116061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104375937164149744533642829 39140976436556154200116061)
            ·
              refine ⟨14677866163708557825043523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39140976436556154200116061 14677866163708557825043523)
              ·
                refine ⟨22016799245562836737565285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14677866163708557825043523 22016799245562836737565285)
                ·
                  refine ⟨4128149858543031888293491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22016799245562836737565285 4128149858543031888293491)
                  ·
                    refine ⟨6192224787814547832440237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4128149858543031888293491 6192224787814547832440237)
                    ·
                      refine ⟨2322084295430455437165089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6192224787814547832440237 2322084295430455437165089)
                      ·
                        rfl

theorem cell23_4522243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_4522243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522243 prefixEnd_4522243 := by exact prefixLift 4522243
  have htrace : WordTrace (prefixWord ++ tailWord_4522243) baseStart_4522243 baseEnd_4522243 := by
    simpa [prefixWord, tailWord_4522243, baseEnd_4522243] using wordTrace_append hprefix tailTrace_4522243
  have hstable : (prefixWord ++ tailWord_4522243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522243).length < 2 ^ (prefixWord ++ tailWord_4522243).sum := by decide
  have hdescent : baseEnd_4522243 < baseStart_4522243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522296 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_4522296 : Nat := 118140960795 + 4522296 * 2 ^ 59
def prefixEnd_4522296 : Nat := 4983230072969 + 3 ^ 40 * 4522296 * 2
def baseEnd_4522296 : Nat := 2322111509905143729802345

theorem tailTrace_4522296 : CollatzResearch.WordTrace tailWord_4522296 prefixEnd_4522296 2322111509905143729802345 := by
  unfold tailWord_4522296
  simp only [CollatzResearch.WordTrace]
  refine ⟨82470842812250706756125371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109961123749667609008167161 82470842812250706756125371)
  ·
    refine ⟨123706264218376060134188057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82470842812250706756125371 123706264218376060134188057)
    ·
      refine ⟨92779698163782045100641043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123706264218376060134188057 92779698163782045100641043)
      ·
        refine ⟨139169547245673067650961565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92779698163782045100641043 139169547245673067650961565)
        ·
          refine ⟨52188580217127400369110587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139169547245673067650961565 52188580217127400369110587)
          ·
            refine ⟨78282870325691100553665881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52188580217127400369110587 78282870325691100553665881)
            ·
              refine ⟨58712152744268325415249411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78282870325691100553665881 58712152744268325415249411)
              ·
                refine ⟨88068229116402488122874117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58712152744268325415249411 88068229116402488122874117)
                ·
                  refine ⟨16512792959325466523038897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88068229116402488122874117 16512792959325466523038897)
                  ·
                    refine ⟨12384594719494099892279173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16512792959325466523038897 12384594719494099892279173)
                    ·
                      refine ⟨2322111509905143729802345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12384594719494099892279173 2322111509905143729802345)
                      ·
                        rfl

theorem cell23_4522296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_4522296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522296 prefixEnd_4522296 := by exact prefixLift 4522296
  have htrace : WordTrace (prefixWord ++ tailWord_4522296) baseStart_4522296 baseEnd_4522296 := by
    simpa [prefixWord, tailWord_4522296, baseEnd_4522296] using wordTrace_append hprefix tailTrace_4522296
  have hstable : (prefixWord ++ tailWord_4522296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522296).length < 2 ^ (prefixWord ++ tailWord_4522296).sum := by decide
  have hdescent : baseEnd_4522296 < baseStart_4522296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522300 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 4, 2, 2]
def baseStart_4522300 : Nat := 118140960795 + 4522300 * 2 ^ 59
def prefixEnd_4522300 : Nat := 4983230072969 + 3 ^ 40 * 4522300 * 2
def baseEnd_4522300 : Nat := 2322113563827761714152327

theorem tailTrace_4522300 : CollatzResearch.WordTrace tailWord_4522300 prefixEnd_4522300 2322113563827761714152327 := by
  unfold tailWord_4522300
  simp only [CollatzResearch.WordTrace]
  refine ⟨82470915758243461097698177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109961221010991281463597569 82470915758243461097698177)
  ·
    refine ⟨61853186818682595823273633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82470915758243461097698177 61853186818682595823273633)
    ·
      refine ⟨46389890114011946867455225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61853186818682595823273633 46389890114011946867455225)
      ·
        refine ⟨34792417585508960150591419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46389890114011946867455225 34792417585508960150591419)
        ·
          refine ⟨52188626378263440225887129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34792417585508960150591419 52188626378263440225887129)
          ·
            refine ⟨39141469783697580169415347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52188626378263440225887129 39141469783697580169415347)
            ·
              refine ⟨58712204675546370254123021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39141469783697580169415347 58712204675546370254123021)
              ·
                refine ⟨22017076753329888845296133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58712204675546370254123021 22017076753329888845296133)
                ·
                  refine ⟨4128201891249354158493025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22017076753329888845296133 4128201891249354158493025)
                  ·
                    refine ⟨3096151418437015618869769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4128201891249354158493025 3096151418437015618869769)
                    ·
                      refine ⟨2322113563827761714152327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3096151418437015618869769 2322113563827761714152327)
                      ·
                        rfl

theorem cell23_4522300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_4522300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522300 prefixEnd_4522300 := by exact prefixLift 4522300
  have htrace : WordTrace (prefixWord ++ tailWord_4522300) baseStart_4522300 baseEnd_4522300 := by
    simpa [prefixWord, tailWord_4522300, baseEnd_4522300] using wordTrace_append hprefix tailTrace_4522300
  have hstable : (prefixWord ++ tailWord_4522300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522300).length < 2 ^ (prefixWord ++ tailWord_4522300).sum := by decide
  have hdescent : baseEnd_4522300 < baseStart_4522300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522357 : List Nat := [1, 3, 4, 1, 2, 1, 4, 2, 5]
def baseStart_4522357 : Nat := 118140960795 + 4522357 * 2 ^ 59
def prefixEnd_4522357 : Nat := 4983230072969 + 3 ^ 40 * 4522357 * 2
def baseEnd_4522357 : Nat := 258015870247229776793285

theorem tailTrace_4522357 : CollatzResearch.WordTrace tailWord_4522357 prefixEnd_4522357 258015870247229776793285 := by
  unfold tailWord_4522357
  simp only [CollatzResearch.WordTrace]
  refine ⟨164943910477280420930221325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109962606984853613953480883 164943910477280420930221325)
  ·
    refine ⟨61853966428980157848832997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164943910477280420930221325 61853966428980157848832997)
    ·
      refine ⟨11597618705433779596656187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61853966428980157848832997 11597618705433779596656187)
      ·
        refine ⟨17396428058150669394984281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11597618705433779596656187 17396428058150669394984281)
        ·
          refine ⟨13047321043613002046238211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17396428058150669394984281 13047321043613002046238211)
          ·
            refine ⟨19570981565419503069357317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13047321043613002046238211 19570981565419503069357317)
            ·
              refine ⟨3669559043516156825504497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19570981565419503069357317 3669559043516156825504497)
              ·
                refine ⟨2752169282637117619128373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3669559043516156825504497 2752169282637117619128373)
                ·
                  refine ⟨258015870247229776793285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2752169282637117619128373 258015870247229776793285)
                  ·
                    rfl

theorem cell23_4522357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 5].length) (baseStart_4522357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522357 prefixEnd_4522357 := by exact prefixLift 4522357
  have htrace : WordTrace (prefixWord ++ tailWord_4522357) baseStart_4522357 baseEnd_4522357 := by
    simpa [prefixWord, tailWord_4522357, baseEnd_4522357] using wordTrace_append hprefix tailTrace_4522357
  have hstable : (prefixWord ++ tailWord_4522357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522357).length < 2 ^ (prefixWord ++ tailWord_4522357).sum := by decide
  have hdescent : baseEnd_4522357 < baseStart_4522357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522393 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 1, 4, 3]
def baseStart_4522393 : Nat := 118140960795 + 4522393 * 2 ^ 59
def prefixEnd_4522393 : Nat := 4983230072969 + 3 ^ 40 * 4522393 * 2
def baseEnd_4522393 : Nat := 2322161317528629850289399

theorem tailTrace_4522393 : CollatzResearch.WordTrace tailWord_4522393 prefixEnd_4522393 2322161317528629850289399 := by
  unfold tailWord_4522393
  simp only [CollatzResearch.WordTrace]
  refine ⟨164945223505149999078531833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109963482336766666052354555 164945223505149999078531833)
  ·
    refine ⟨123708917628862499308898875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164945223505149999078531833 123708917628862499308898875)
    ·
      refine ⟨185563376443293748963348313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123708917628862499308898875 185563376443293748963348313)
      ·
        refine ⟨139172532332470311722511235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185563376443293748963348313 139172532332470311722511235)
        ·
          refine ⟨208758798498705467583766853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139172532332470311722511235 208758798498705467583766853)
          ·
            refine ⟨39142274718507275171956285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 208758798498705467583766853 39142274718507275171956285)
            ·
              refine ⟨14678353019440228189483607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39142274718507275171956285 14678353019440228189483607)
              ·
                refine ⟨22017529529160342284225411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14678353019440228189483607 22017529529160342284225411)
                ·
                  refine ⟨33026294293740513426338117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22017529529160342284225411 33026294293740513426338117)
                  ·
                    refine ⟨6192430180076346267438397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33026294293740513426338117 6192430180076346267438397)
                    ·
                      refine ⟨2322161317528629850289399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6192430180076346267438397 2322161317528629850289399)
                      ·
                        rfl

theorem cell23_4522393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_4522393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522393 prefixEnd_4522393 := by exact prefixLift 4522393
  have htrace : WordTrace (prefixWord ++ tailWord_4522393) baseStart_4522393 baseEnd_4522393 := by
    simpa [prefixWord, tailWord_4522393, baseEnd_4522393] using wordTrace_append hprefix tailTrace_4522393
  have hstable : (prefixWord ++ tailWord_4522393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522393).length < 2 ^ (prefixWord ++ tailWord_4522393).sum := by decide
  have hdescent : baseEnd_4522393 < baseStart_4522393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522417 : List Nat := [1, 2, 2, 4, 1, 2, 2, 4, 1, 4]
def baseStart_4522417 : Nat := 118140960795 + 4522417 * 2 ^ 59
def prefixEnd_4522417 : Nat := 4983230072969 + 3 ^ 40 * 4522417 * 2
def baseEnd_4522417 : Nat := 774057880354779252129763

theorem tailTrace_4522417 : CollatzResearch.WordTrace tailWord_4522417 prefixEnd_4522417 774057880354779252129763 := by
  unfold tailWord_4522417
  simp only [CollatzResearch.WordTrace]
  refine ⟨164946098857063051177405505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109964065904708700784937003 164946098857063051177405505)
  ·
    refine ⟨123709574142797288383054129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164946098857063051177405505 123709574142797288383054129)
    ·
      refine ⟨92782180607097966287290597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123709574142797288383054129 92782180607097966287290597)
      ·
        refine ⟨17396658863830868678866987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92782180607097966287290597 17396658863830868678866987)
        ·
          refine ⟨26094988295746303018300481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17396658863830868678866987 26094988295746303018300481)
          ·
            refine ⟨19571241221809727263725361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26094988295746303018300481 19571241221809727263725361)
            ·
              refine ⟨14678430916357295447794021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19571241221809727263725361 14678430916357295447794021)
              ·
                refine ⟨2752205796816992896461379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14678430916357295447794021 2752205796816992896461379)
                ·
                  refine ⟨4128308695225489344692069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2752205796816992896461379 4128308695225489344692069)
                  ·
                    refine ⟨774057880354779252129763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4128308695225489344692069 774057880354779252129763)
                    ·
                      rfl

theorem cell23_4522417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_4522417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522417 prefixEnd_4522417 := by exact prefixLift 4522417
  have htrace : WordTrace (prefixWord ++ tailWord_4522417) baseStart_4522417 baseEnd_4522417 := by
    simpa [prefixWord, tailWord_4522417, baseEnd_4522417] using wordTrace_append hprefix tailTrace_4522417
  have hstable : (prefixWord ++ tailWord_4522417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522417).length < 2 ^ (prefixWord ++ tailWord_4522417).sum := by decide
  have hdescent : baseEnd_4522417 < baseStart_4522417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522474 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_4522474 : Nat := 118140960795 + 4522474 * 2 ^ 59
def prefixEnd_4522474 : Nat := 4983230072969 + 3 ^ 40 * 4522474 * 2
def baseEnd_4522474 : Nat := 2322202909461644033376527

theorem tailTrace_4522474 : CollatzResearch.WordTrace tailWord_4522474 prefixEnd_4522474 2322202909461644033376527 := by
  unfold tailWord_4522474
  simp only [CollatzResearch.WordTrace]
  refine ⟨41237044454464137478057619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109965451878571033274820317 41237044454464137478057619)
  ·
    refine ⟨61855566681696206217086429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41237044454464137478057619 61855566681696206217086429)
    ·
      refine ⟨23195837505636077331407411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61855566681696206217086429 23195837505636077331407411)
      ·
        refine ⟨34793756258454115997111117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23195837505636077331407411 34793756258454115997111117)
        ·
          refine ⟨13047658596920293498916669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34793756258454115997111117 13047658596920293498916669)
          ·
            refine ⟨4892871973845110062093751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13047658596920293498916669 4892871973845110062093751)
            ·
              refine ⟨7339307960767665093140627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4892871973845110062093751 7339307960767665093140627)
              ·
                refine ⟨11008961941151497639710941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7339307960767665093140627 11008961941151497639710941)
                ·
                  refine ⟨4128360727931811614891603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11008961941151497639710941 4128360727931811614891603)
                  ·
                    refine ⟨6192541091897717422337405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4128360727931811614891603 6192541091897717422337405)
                    ·
                      refine ⟨2322202909461644033376527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6192541091897717422337405 2322202909461644033376527)
                      ·
                        rfl

theorem cell23_4522474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_4522474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522474 prefixEnd_4522474 := by exact prefixLift 4522474
  have htrace : WordTrace (prefixWord ++ tailWord_4522474) baseStart_4522474 baseEnd_4522474 := by
    simpa [prefixWord, tailWord_4522474, baseEnd_4522474] using wordTrace_append hprefix tailTrace_4522474
  have hstable : (prefixWord ++ tailWord_4522474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522474).length < 2 ^ (prefixWord ++ tailWord_4522474).sum := by decide
  have hdescent : baseEnd_4522474 < baseStart_4522474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522483 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 5]
def baseStart_4522483 : Nat := 118140960795 + 4522483 * 2 ^ 59
def prefixEnd_4522483 : Nat := 4983230072969 + 3 ^ 40 * 4522483 * 2
def baseEnd_4522483 : Nat := 2322207530787534498163985

theorem tailTrace_4522483 : CollatzResearch.WordTrace tailWord_4522483 prefixEnd_4522483 2322207530787534498163985 := by
  unfold tailWord_4522483
  simp only [CollatzResearch.WordTrace]
  refine ⟨164948506074823944449308103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109965670716549296299538735 164948506074823944449308103)
  ·
    refine ⟨247422759112235916673962155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164948506074823944449308103 247422759112235916673962155)
    ·
      refine ⟨371134138668353875010943233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247422759112235916673962155 371134138668353875010943233)
      ·
        refine ⟨278350604001265406258207425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371134138668353875010943233 278350604001265406258207425)
        ·
          refine ⟨208762953000949054693655569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278350604001265406258207425 208762953000949054693655569)
          ·
            refine ⟨156572214750711791020241677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208762953000949054693655569 156572214750711791020241677)
            ·
              refine ⟨58714580531516921632590629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156572214750711791020241677 58714580531516921632590629)
              ·
                refine ⟨11008983849659422806110743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58714580531516921632590629 11008983849659422806110743)
                ·
                  refine ⟨16513475774489134209166115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11008983849659422806110743 16513475774489134209166115)
                  ·
                    refine ⟨24770213661733701313749173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16513475774489134209166115 24770213661733701313749173)
                    ·
                      refine ⟨2322207530787534498163985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24770213661733701313749173 2322207530787534498163985)
                      ·
                        rfl

theorem cell23_4522483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_4522483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522483 prefixEnd_4522483 := by exact prefixLift 4522483
  have htrace : WordTrace (prefixWord ++ tailWord_4522483) baseStart_4522483 baseEnd_4522483 := by
    simpa [prefixWord, tailWord_4522483, baseEnd_4522483] using wordTrace_append hprefix tailTrace_4522483
  have hstable : (prefixWord ++ tailWord_4522483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522483).length < 2 ^ (prefixWord ++ tailWord_4522483).sum := by decide
  have hdescent : baseEnd_4522483 < baseStart_4522483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522493 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_4522493 : Nat := 118140960795 + 4522493 * 2 ^ 59
def prefixEnd_4522493 : Nat := 4983230072969 + 3 ^ 40 * 4522493 * 2
def baseEnd_4522493 : Nat := 2322212665594079459038939

theorem tailTrace_4522493 : CollatzResearch.WordTrace tailWord_4522493 prefixEnd_4522493 2322212665594079459038939 := by
  unfold tailWord_4522493
  simp only [CollatzResearch.WordTrace]
  refine ⟨164948870804787716157172133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109965913869858477438114755 164948870804787716157172133)
  ·
    refine ⟨30927913275897696779469775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164948870804787716157172133 30927913275897696779469775)
    ·
      refine ⟨46391869913846545169204663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30927913275897696779469775 46391869913846545169204663)
      ·
        refine ⟨69587804870769817753806995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46391869913846545169204663 69587804870769817753806995)
        ·
          refine ⟨104381707306154726630710493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69587804870769817753806995 104381707306154726630710493)
          ·
            refine ⟨39143140239808022486516435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104381707306154726630710493 39143140239808022486516435)
            ·
              refine ⟨58714710359712033729774653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39143140239808022486516435 58714710359712033729774653)
              ·
                refine ⟨22018016384892012648665495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58714710359712033729774653 22018016384892012648665495)
                ·
                  refine ⟨33027024577338018972998243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22018016384892012648665495 33027024577338018972998243)
                  ·
                    refine ⟨49540536866007028459497365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33027024577338018972998243 49540536866007028459497365)
                    ·
                      refine ⟨2322212665594079459038939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49540536866007028459497365 2322212665594079459038939)
                      ·
                        rfl

theorem cell23_4522493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_4522493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522493 prefixEnd_4522493 := by exact prefixLift 4522493
  have htrace : WordTrace (prefixWord ++ tailWord_4522493) baseStart_4522493 baseEnd_4522493 := by
    simpa [prefixWord, tailWord_4522493, baseEnd_4522493] using wordTrace_append hprefix tailTrace_4522493
  have hstable : (prefixWord ++ tailWord_4522493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522493).length < 2 ^ (prefixWord ++ tailWord_4522493).sum := by decide
  have hdescent : baseEnd_4522493 < baseStart_4522493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522497 : List Nat := [1, 2, 4, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_4522497 : Nat := 118140960795 + 4522497 * 2 ^ 59
def prefixEnd_4522497 : Nat := 4983230072969 + 3 ^ 40 * 4522497 * 2
def baseEnd_4522497 : Nat := 2322214719516697443388921

theorem tailTrace_4522497 : CollatzResearch.WordTrace tailWord_4522497 prefixEnd_4522497 2322214719516697443388921 := by
  unfold tailWord_4522497
  simp only [CollatzResearch.WordTrace]
  refine ⟨164949016696773224840317745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109966011131182149893545163 164949016696773224840317745)
  ·
    refine ⟨123711762522579918630238309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164949016696773224840317745 123711762522579918630238309)
    ·
      refine ⟨23195955472983734743169683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123711762522579918630238309 23195955472983734743169683)
      ·
        refine ⟨34793933209475602114754525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23195955472983734743169683 34793933209475602114754525)
        ·
          refine ⟨13047724953553350793032947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34793933209475602114754525 13047724953553350793032947)
          ·
            refine ⟨19571587430330026189549421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13047724953553350793032947 19571587430330026189549421)
            ·
              refine ⟨7339345286373759821081033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19571587430330026189549421 7339345286373759821081033)
              ·
                refine ⟨5504508964780319865810775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7339345286373759821081033 5504508964780319865810775)
                ·
                  refine ⟨8256763447170479798716163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5504508964780319865810775 8256763447170479798716163)
                  ·
                    refine ⟨12385145170755719698074245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8256763447170479798716163 12385145170755719698074245)
                    ·
                      refine ⟨2322214719516697443388921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12385145170755719698074245 2322214719516697443388921)
                      ·
                        rfl

theorem cell23_4522497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_4522497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522497 prefixEnd_4522497 := by exact prefixLift 4522497
  have htrace : WordTrace (prefixWord ++ tailWord_4522497) baseStart_4522497 baseEnd_4522497 := by
    simpa [prefixWord, tailWord_4522497, baseEnd_4522497] using wordTrace_append hprefix tailTrace_4522497
  have hstable : (prefixWord ++ tailWord_4522497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522497).length < 2 ^ (prefixWord ++ tailWord_4522497).sum := by decide
  have hdescent : baseEnd_4522497 < baseStart_4522497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522510 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_4522510 : Nat := 118140960795 + 4522510 * 2 ^ 59
def prefixEnd_4522510 : Nat := 4983230072969 + 3 ^ 40 * 4522510 * 2
def baseEnd_4522510 : Nat := 2322221394765205892526361

theorem tailTrace_4522510 : CollatzResearch.WordTrace tailWord_4522510 prefixEnd_4522510 2322221394765205892526361 := by
  unfold tailWord_4522510
  simp only [CollatzResearch.WordTrace]
  refine ⟨20618686355715766007567623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109966327230484085373693989 20618686355715766007567623)
  ·
    refine ⟨30928029533573649011351435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20618686355715766007567623 30928029533573649011351435)
    ·
      refine ⟨46392044300360473517027153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30928029533573649011351435 46392044300360473517027153)
      ·
        refine ⟨34794033225270355137770365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46392044300360473517027153 34794033225270355137770365)
        ·
          refine ⟨13047762459476383176663887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34794033225270355137770365 13047762459476383176663887)
          ·
            refine ⟨19571643689214574764995831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13047762459476383176663887 19571643689214574764995831)
            ·
              refine ⟨29357465533821862147493747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19571643689214574764995831 29357465533821862147493747)
              ·
                refine ⟨44036198300732793221240621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29357465533821862147493747 44036198300732793221240621)
                ·
                  refine ⟨16513574362774797457965233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44036198300732793221240621 16513574362774797457965233)
                  ·
                    refine ⟨12385180772081098093473925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16513574362774797457965233 12385180772081098093473925)
                    ·
                      refine ⟨2322221394765205892526361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12385180772081098093473925 2322221394765205892526361)
                      ·
                        rfl

theorem cell23_4522510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_4522510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522510 prefixEnd_4522510 := by exact prefixLift 4522510
  have htrace : WordTrace (prefixWord ++ tailWord_4522510) baseStart_4522510 baseEnd_4522510 := by
    simpa [prefixWord, tailWord_4522510, baseEnd_4522510] using wordTrace_append hprefix tailTrace_4522510
  have hstable : (prefixWord ++ tailWord_4522510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522510).length < 2 ^ (prefixWord ++ tailWord_4522510).sum := by decide
  have hdescent : baseEnd_4522510 < baseStart_4522510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522530 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_4522530 : Nat := 118140960795 + 4522530 * 2 ^ 59
def prefixEnd_4522530 : Nat := 4983230072969 + 3 ^ 40 * 4522530 * 2
def baseEnd_4522530 : Nat := 2322231664378295814276269

theorem tailTrace_4522530 : CollatzResearch.WordTrace tailWord_4522530 prefixEnd_4522530 2322231664378295814276269 := by
  unfold tailWord_4522530
  simp only [CollatzResearch.WordTrace]
  refine ⟨41237555076413417869067261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109966813537102447650846029 41237555076413417869067261)
  ·
    refine ⟨15464083153655031700900223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41237555076413417869067261 15464083153655031700900223)
    ·
      refine ⟨23196124730482547551350335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15464083153655031700900223 23196124730482547551350335)
      ·
        refine ⟨34794187095723821327025503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23196124730482547551350335 34794187095723821327025503)
        ·
          refine ⟨52191280643585731990538255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34794187095723821327025503 52191280643585731990538255)
          ·
            refine ⟨78286920965378597985807383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52191280643585731990538255 78286920965378597985807383)
            ·
              refine ⟨117430381448067896978711075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78286920965378597985807383 117430381448067896978711075)
              ·
                refine ⟨176145572172101845468066613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117430381448067896978711075 176145572172101845468066613)
                ·
                  refine ⟨16513647391134548012631245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176145572172101845468066613 16513647391134548012631245)
                  ·
                    refine ⟨6192617771675455504736717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16513647391134548012631245 6192617771675455504736717)
                    ·
                      refine ⟨2322231664378295814276269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6192617771675455504736717 2322231664378295814276269)
                      ·
                        rfl

theorem cell23_4522530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_4522530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522530 prefixEnd_4522530 := by exact prefixLift 4522530
  have htrace : WordTrace (prefixWord ++ tailWord_4522530) baseStart_4522530 baseEnd_4522530 := by
    simpa [prefixWord, tailWord_4522530, baseEnd_4522530] using wordTrace_append hprefix tailTrace_4522530
  have hstable : (prefixWord ++ tailWord_4522530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522530).length < 2 ^ (prefixWord ++ tailWord_4522530).sum := by decide
  have hdescent : baseEnd_4522530 < baseStart_4522530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522531 : List Nat := [1, 1, 1, 4, 4, 2, 1, 4, 1, 2, 2]
def baseStart_4522531 : Nat := 118140960795 + 4522531 * 2 ^ 59
def prefixEnd_4522531 : Nat := 4983230072969 + 3 ^ 40 * 4522531 * 2
def baseEnd_4522531 : Nat := 2322232177858950310363765

theorem tailTrace_4522531 : CollatzResearch.WordTrace tailWord_4522531 prefixEnd_4522531 2322232177858950310363765 := by
  unfold tailWord_4522531
  simp only [CollatzResearch.WordTrace]
  refine ⟨164950256778650048647055447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109966837852433365764703631 164950256778650048647055447)
  ·
    refine ⟨247425385167975072970583171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164950256778650048647055447 247425385167975072970583171)
    ·
      refine ⟨371138077751962609455874757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247425385167975072970583171 371138077751962609455874757)
      ·
        refine ⟨69588389578492989272976517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 371138077751962609455874757 69588389578492989272976517)
        ·
          refine ⟨13047823045967435488683097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69588389578492989272976517 13047823045967435488683097)
          ·
            refine ⟨9785867284475576616512323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13047823045967435488683097 9785867284475576616512323)
            ·
              refine ⟨14678800926713364924768485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9785867284475576616512323 14678800926713364924768485)
              ·
                refine ⟨2752275173758755923394091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14678800926713364924768485 2752275173758755923394091)
                ·
                  refine ⟨4128412760638133885091137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2752275173758755923394091 4128412760638133885091137)
                  ·
                    refine ⟨3096309570478600413818353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4128412760638133885091137 3096309570478600413818353)
                    ·
                      refine ⟨2322232177858950310363765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3096309570478600413818353 2322232177858950310363765)
                      ·
                        rfl

theorem cell23_4522531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_4522531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522531 prefixEnd_4522531 := by exact prefixLift 4522531
  have htrace : WordTrace (prefixWord ++ tailWord_4522531) baseStart_4522531 baseEnd_4522531 := by
    simpa [prefixWord, tailWord_4522531, baseEnd_4522531] using wordTrace_append hprefix tailTrace_4522531
  have hstable : (prefixWord ++ tailWord_4522531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522531).length < 2 ^ (prefixWord ++ tailWord_4522531).sum := by decide
  have hdescent : baseEnd_4522531 < baseStart_4522531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522533 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 2, 7]
def baseStart_4522533 : Nat := 118140960795 + 4522533 * 2 ^ 59
def prefixEnd_4522533 : Nat := 4983230072969 + 3 ^ 40 * 4522533 * 2
def baseEnd_4522533 : Nat := 774077734940086434179585

theorem tailTrace_4522533 : CollatzResearch.WordTrace tailWord_4522533 prefixEnd_4522533 774077734940086434179585 := by
  unfold tailWord_4522533
  simp only [CollatzResearch.WordTrace]
  refine ⟨164950329724642802988628253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109966886483095201992418835 164950329724642802988628253)
  ·
    refine ⟨61856373646741051120735595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164950329724642802988628253 61856373646741051120735595)
    ·
      refine ⟨92784560470111576681103393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61856373646741051120735595 92784560470111576681103393)
      ·
        refine ⟨69588420352583682510827545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92784560470111576681103393 69588420352583682510827545)
        ·
          refine ⟨52191315264437761883120659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69588420352583682510827545 52191315264437761883120659)
          ·
            refine ⟨78286972896656642824680989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52191315264437761883120659 78286972896656642824680989)
            ·
              refine ⟨29357614836246241059255371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78286972896656642824680989 29357614836246241059255371)
              ·
                refine ⟨44036422254369361588883057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29357614836246241059255371 44036422254369361588883057)
                ·
                  refine ⟨33027316690777021191662293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44036422254369361588883057 33027316690777021191662293)
                  ·
                    refine ⟨774077734940086434179585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33027316690777021191662293 774077734940086434179585)
                    ·
                      rfl

theorem cell23_4522533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_4522533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522533 prefixEnd_4522533 := by exact prefixLift 4522533
  have htrace : WordTrace (prefixWord ++ tailWord_4522533) baseStart_4522533 baseEnd_4522533 := by
    simpa [prefixWord, tailWord_4522533, baseEnd_4522533] using wordTrace_append hprefix tailTrace_4522533
  have hstable : (prefixWord ++ tailWord_4522533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522533).length < 2 ^ (prefixWord ++ tailWord_4522533).sum := by decide
  have hdescent : baseEnd_4522533 < baseStart_4522533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522541 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4522541 : Nat := 118140960795 + 4522541 * 2 ^ 59
def prefixEnd_4522541 : Nat := 4983230072969 + 3 ^ 40 * 4522541 * 2
def baseEnd_4522541 : Nat := 774079104221831757079573

theorem tailTrace_4522541 : CollatzResearch.WordTrace tailWord_4522541 prefixEnd_4522541 774079104221831757079573 := by
  unfold tailWord_4522541
  simp only [CollatzResearch.WordTrace]
  refine ⟨164950621508613820354919477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109967081005742546903279651 164950621508613820354919477)
  ·
    refine ⟨15464120766432545658273701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164950621508613820354919477 15464120766432545658273701)
    ·
      refine ⟨2899522643706102310926319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15464120766432545658273701 2899522643706102310926319)
      ·
        refine ⟨4349283965559153466389479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2899522643706102310926319 4349283965559153466389479)
        ·
          refine ⟨6523925948338730199584219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4349283965559153466389479 6523925948338730199584219)
          ·
            refine ⟨9785888922508095299376329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6523925948338730199584219 9785888922508095299376329)
            ·
              refine ⟨7339416691881071474532247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9785888922508095299376329 7339416691881071474532247)
              ·
                refine ⟨11009125037821607211798371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7339416691881071474532247 11009125037821607211798371)
                ·
                  refine ⟨16513687556732410817697557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11009125037821607211798371 16513687556732410817697557)
                  ·
                    refine ⟨774079104221831757079573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16513687556732410817697557 774079104221831757079573)
                    ·
                      rfl

theorem cell23_4522541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4522541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522541 prefixEnd_4522541 := by exact prefixLift 4522541
  have htrace : WordTrace (prefixWord ++ tailWord_4522541) baseStart_4522541 baseEnd_4522541 := by
    simpa [prefixWord, tailWord_4522541, baseEnd_4522541] using wordTrace_append hprefix tailTrace_4522541
  have hstable : (prefixWord ++ tailWord_4522541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522541).length < 2 ^ (prefixWord ++ tailWord_4522541).sum := by decide
  have hdescent : baseEnd_4522541 < baseStart_4522541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522547 : List Nat := [1, 1, 1, 2, 4, 2, 1, 5, 2, 1, 3]
def baseStart_4522547 : Nat := 118140960795 + 4522547 * 2 ^ 59
def prefixEnd_4522547 : Nat := 4983230072969 + 3 ^ 40 * 4522547 * 2
def baseEnd_4522547 : Nat := 2322240393549422247763691

theorem tailTrace_4522547 : CollatzResearch.WordTrace tailWord_4522547 prefixEnd_4522547 2322240393549422247763691 := by
  unfold tailWord_4522547
  simp only [CollatzResearch.WordTrace]
  refine ⟨164950840346592083379637895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109967226897728055586425263 164950840346592083379637895)
  ·
    refine ⟨247426260519888125069456843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164950840346592083379637895 247426260519888125069456843)
    ·
      refine ⟨371139390779832187604185265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247426260519888125069456843 371139390779832187604185265)
      ·
        refine ⟨278354543084874140703138949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371139390779832187604185265 278354543084874140703138949)
        ·
          refine ⟨52191476828413901381838553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 278354543084874140703138949 52191476828413901381838553)
          ·
            refine ⟨39143607621310426036378915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52191476828413901381838553 39143607621310426036378915)
            ·
              refine ⟨58715411431965639054568373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39143607621310426036378915 58715411431965639054568373)
              ·
                refine ⟨5504569821746778661365785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58715411431965639054568373 5504569821746778661365785)
                ·
                  refine ⟨4128427366310083996024339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5504569821746778661365785 4128427366310083996024339)
                  ·
                    refine ⟨6192641049465125994036509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4128427366310083996024339 6192641049465125994036509)
                    ·
                      refine ⟨2322240393549422247763691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6192641049465125994036509 2322240393549422247763691)
                      ·
                        rfl

theorem cell23_4522547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 1, 3].length) (baseStart_4522547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522547 prefixEnd_4522547 := by exact prefixLift 4522547
  have htrace : WordTrace (prefixWord ++ tailWord_4522547) baseStart_4522547 baseEnd_4522547 := by
    simpa [prefixWord, tailWord_4522547, baseEnd_4522547] using wordTrace_append hprefix tailTrace_4522547
  have hstable : (prefixWord ++ tailWord_4522547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522547).length < 2 ^ (prefixWord ++ tailWord_4522547).sum := by decide
  have hdescent : baseEnd_4522547 < baseStart_4522547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522548 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_4522548 : Nat := 118140960795 + 4522548 * 2 ^ 59
def prefixEnd_4522548 : Nat := 4983230072969 + 3 ^ 40 * 4522548 * 2
def baseEnd_4522548 : Nat := 2322240907030076743851187

theorem tailTrace_4522548 : CollatzResearch.WordTrace tailWord_4522548 prefixEnd_4522548 2322240907030076743851187 := by
  unfold tailWord_4522548
  simp only [CollatzResearch.WordTrace]
  refine ⟨82475438409794230275212149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109967251213058973700282865 82475438409794230275212149)
  ·
    refine ⟨7732072350918209088301139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82475438409794230275212149 7732072350918209088301139)
    ·
      refine ⟨11598108526377313632451709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7732072350918209088301139 11598108526377313632451709)
      ·
        refine ⟨4349290697391492612169391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11598108526377313632451709 4349290697391492612169391)
        ·
          refine ⟨6523936046087238918254087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4349290697391492612169391 6523936046087238918254087)
          ·
            refine ⟨9785904069130858377381131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6523936046087238918254087 9785904069130858377381131)
            ·
              refine ⟨14678856103696287566071697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9785904069130858377381131 14678856103696287566071697)
              ·
                refine ⟨11009142077772215674553773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14678856103696287566071697 11009142077772215674553773)
                ·
                  refine ⟨4128428279164580877957665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11009142077772215674553773 4128428279164580877957665)
                  ·
                    refine ⟨3096321209373435658468249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4128428279164580877957665 3096321209373435658468249)
                    ·
                      refine ⟨2322240907030076743851187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3096321209373435658468249 2322240907030076743851187)
                      ·
                        rfl

theorem cell23_4522548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_4522548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522548 prefixEnd_4522548 := by exact prefixLift 4522548
  have htrace : WordTrace (prefixWord ++ tailWord_4522548) baseStart_4522548 baseEnd_4522548 := by
    simpa [prefixWord, tailWord_4522548, baseEnd_4522548] using wordTrace_append hprefix tailTrace_4522548
  have hstable : (prefixWord ++ tailWord_4522548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522548).length < 2 ^ (prefixWord ++ tailWord_4522548).sum := by decide
  have hdescent : baseEnd_4522548 < baseStart_4522548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522580 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_4522580 : Nat := 118140960795 + 4522580 * 2 ^ 59
def prefixEnd_4522580 : Nat := 4983230072969 + 3 ^ 40 * 4522580 * 2
def baseEnd_4522580 : Nat := 774085779470340206217013

theorem tailTrace_4522580 : CollatzResearch.WordTrace tailWord_4522580 prefixEnd_4522580 774085779470340206217013 := by
  unfold tailWord_4522580
  simp only [CollatzResearch.WordTrace]
  refine ⟨82476021977736265007794597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109968029303648353343726129 82476021977736265007794597)
  ·
    refine ⟨15464254120825549688961487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82476021977736265007794597 15464254120825549688961487)
    ·
      refine ⟨23196381181238324533442231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15464254120825549688961487 23196381181238324533442231)
      ·
        refine ⟨34794571771857486800163347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23196381181238324533442231 34794571771857486800163347)
        ·
          refine ⟨52191857657786230200245021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34794571771857486800163347 52191857657786230200245021)
          ·
            refine ⟨19571946621669836325091883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52191857657786230200245021 19571946621669836325091883)
            ·
              refine ⟨29357919932504754487637825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19571946621669836325091883 29357919932504754487637825)
              ·
                refine ⟨22018439949378565865728369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29357919932504754487637825 22018439949378565865728369)
                ·
                  refine ⟨16513829962033924399296277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22018439949378565865728369 16513829962033924399296277)
                  ·
                    refine ⟨774085779470340206217013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16513829962033924399296277 774085779470340206217013)
                    ·
                      rfl

theorem cell23_4522580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_4522580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522580 prefixEnd_4522580 := by exact prefixLift 4522580
  have htrace : WordTrace (prefixWord ++ tailWord_4522580) baseStart_4522580 baseEnd_4522580 := by
    simpa [prefixWord, tailWord_4522580, baseEnd_4522580] using wordTrace_append hprefix tailTrace_4522580
  have hstable : (prefixWord ++ tailWord_4522580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522580).length < 2 ^ (prefixWord ++ tailWord_4522580).sum := by decide
  have hdescent : baseEnd_4522580 < baseStart_4522580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522604 : List Nat := [2, 2, 1, 1, 3, 1, 2, 5, 2, 2, 2]
def baseStart_4522604 : Nat := 118140960795 + 4522604 * 2 ^ 59
def prefixEnd_4522604 : Nat := 4983230072969 + 3 ^ 40 * 4522604 * 2
def baseEnd_4522604 : Nat := 2322269661946728524750929

theorem tailTrace_4522604 : CollatzResearch.WordTrace tailWord_4522604 prefixEnd_4522604 2322269661946728524750929 := by
  unfold tailWord_4522604
  simp only [CollatzResearch.WordTrace]
  refine ⟨82476459653692791057231433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109968612871590388076308577 82476459653692791057231433)
  ·
    refine ⟨61857344740269593292923575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82476459653692791057231433 61857344740269593292923575)
    ·
      refine ⟨92786017110404389939385363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61857344740269593292923575 92786017110404389939385363)
      ·
        refine ⟨139179025665606584909078045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92786017110404389939385363 139179025665606584909078045)
        ·
          refine ⟨52192134624602469340904267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139179025665606584909078045 52192134624602469340904267)
          ·
            refine ⟨78288201936903704011356401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52192134624602469340904267 78288201936903704011356401)
            ·
              refine ⟨58716151452677778008517301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78288201936903704011356401 58716151452677778008517301)
              ·
                refine ⟨5504639198688541688298497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58716151452677778008517301 5504639198688541688298497)
                ·
                  refine ⟨4128479399016406266223873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5504639198688541688298497 4128479399016406266223873)
                  ·
                    refine ⟨3096359549262304699667905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4128479399016406266223873 3096359549262304699667905)
                    ·
                      refine ⟨2322269661946728524750929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3096359549262304699667905 2322269661946728524750929)
                      ·
                        rfl

theorem cell23_4522604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 2, 2].length) (baseStart_4522604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522604 prefixEnd_4522604 := by exact prefixLift 4522604
  have htrace : WordTrace (prefixWord ++ tailWord_4522604) baseStart_4522604 baseEnd_4522604 := by
    simpa [prefixWord, tailWord_4522604, baseEnd_4522604] using wordTrace_append hprefix tailTrace_4522604
  have hstable : (prefixWord ++ tailWord_4522604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522604).length < 2 ^ (prefixWord ++ tailWord_4522604).sum := by decide
  have hdescent : baseEnd_4522604 < baseStart_4522604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522620 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_4522620 : Nat := 118140960795 + 4522620 * 2 ^ 59
def prefixEnd_4522620 : Nat := 4983230072969 + 3 ^ 40 * 4522620 * 2
def baseEnd_4522620 : Nat := 2322277877637200462150855

theorem tailTrace_4522620 : CollatzResearch.WordTrace tailWord_4522620 prefixEnd_4522620 2322277877637200462150855 := by
  unfold tailWord_4522620
  simp only [CollatzResearch.WordTrace]
  refine ⟨82476751437663808423522657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109969001916885077898030209 82476751437663808423522657)
  ·
    refine ⟨61857563578247856317641993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82476751437663808423522657 61857563578247856317641993)
    ·
      refine ⟨46393172683685892238231495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61857563578247856317641993 46393172683685892238231495)
      ·
        refine ⟨69589759025528838357347243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46393172683685892238231495 69589759025528838357347243)
        ·
          refine ⟨104384638538293257536020865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69589759025528838357347243 104384638538293257536020865)
          ·
            refine ⟨78288478903719943152015649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104384638538293257536020865 78288478903719943152015649)
            ·
              refine ⟨58716359177789957364011737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78288478903719943152015649 58716359177789957364011737)
              ·
                refine ⟨44037269383342468023008803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58716359177789957364011737 44037269383342468023008803)
                ·
                  refine ⟨66055904075013702034513205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44037269383342468023008803 66055904075013702034513205)
                  ·
                    refine ⟨6192741007032534565735613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66055904075013702034513205 6192741007032534565735613)
                    ·
                      refine ⟨2322277877637200462150855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6192741007032534565735613 2322277877637200462150855)
                      ·
                        rfl

theorem cell23_4522620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_4522620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522620 prefixEnd_4522620 := by exact prefixLift 4522620
  have htrace : WordTrace (prefixWord ++ tailWord_4522620) baseStart_4522620 baseEnd_4522620 := by
    simpa [prefixWord, tailWord_4522620, baseEnd_4522620] using wordTrace_append hprefix tailTrace_4522620
  have hstable : (prefixWord ++ tailWord_4522620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522620).length < 2 ^ (prefixWord ++ tailWord_4522620).sum := by decide
  have hdescent : baseEnd_4522620 < baseStart_4522620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522627 : List Nat := [1, 1, 1, 3, 3, 1, 5, 3, 5]
def baseStart_4522627 : Nat := 118140960795 + 4522627 * 2 ^ 59
def prefixEnd_4522627 : Nat := 4983230072969 + 3 ^ 40 * 4522627 * 2
def baseEnd_4522627 : Nat := 258031274666864659418147

theorem tailTrace_4522627 : CollatzResearch.WordTrace tailWord_4522627 prefixEnd_4522627 258031274666864659418147 := by
  unfold tailWord_4522627
  simp only [CollatzResearch.WordTrace]
  refine ⟨164953758186302257042550135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109969172124201504695033423 164953758186302257042550135)
  ·
    refine ⟨247430637279453385563825203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164953758186302257042550135 247430637279453385563825203)
    ·
      refine ⟨371145955919180078345737805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247430637279453385563825203 371145955919180078345737805)
      ·
        refine ⟨139179733469692529379651677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 371145955919180078345737805 139179733469692529379651677)
        ·
          refine ⟨52192400051134698517369379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139179733469692529379651677 52192400051134698517369379)
          ·
            refine ⟨78288600076702047776054069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52192400051134698517369379 78288600076702047776054069)
            ·
              refine ⟨7339556257190816979005069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78288600076702047776054069 7339556257190816979005069)
              ·
                refine ⟨2752333596446556367126901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7339556257190816979005069 2752333596446556367126901)
                ·
                  refine ⟨258031274666864659418147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2752333596446556367126901 258031274666864659418147)
                  ·
                    rfl

theorem cell23_4522627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 5].length) (baseStart_4522627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522627 prefixEnd_4522627 := by exact prefixLift 4522627
  have htrace : WordTrace (prefixWord ++ tailWord_4522627) baseStart_4522627 baseEnd_4522627 := by
    simpa [prefixWord, tailWord_4522627, baseEnd_4522627] using wordTrace_append hprefix tailTrace_4522627
  have hstable : (prefixWord ++ tailWord_4522627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522627).length < 2 ^ (prefixWord ++ tailWord_4522627).sum := by decide
  have hdescent : baseEnd_4522627 < baseStart_4522627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522644 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 7]
def baseStart_4522644 : Nat := 118140960795 + 4522644 * 2 ^ 59
def prefixEnd_4522644 : Nat := 4983230072969 + 3 ^ 40 * 4522644 * 2
def baseEnd_4522644 : Nat := 258032244574767596472305

theorem tailTrace_4522644 : CollatzResearch.WordTrace tailWord_4522644 prefixEnd_4522644 258032244574767596472305 := by
  unfold tailWord_4522644
  simp only [CollatzResearch.WordTrace]
  refine ⟨82477189113620334472959493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109969585484827112630612657 82477189113620334472959493)
  ·
    refine ⟨15464472958803812713679905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82477189113620334472959493 15464472958803812713679905)
    ·
      refine ⟨11598354719102859535259929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15464472958803812713679905 11598354719102859535259929)
      ·
        refine ⟨8698766039327144651444947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11598354719102859535259929 8698766039327144651444947)
        ·
          refine ⟨13048149058990716977167421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8698766039327144651444947 13048149058990716977167421)
          ·
            refine ⟨4893055897121518866437783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13048149058990716977167421 4893055897121518866437783)
            ·
              refine ⟨7339583845682278299656675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4893055897121518866437783 7339583845682278299656675)
              ·
                refine ⟨11009375768523417449485013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7339583845682278299656675 11009375768523417449485013)
                ·
                  refine ⟨258032244574767596472305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11009375768523417449485013 258032244574767596472305)
                  ·
                    rfl

theorem cell23_4522644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_4522644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522644 prefixEnd_4522644 := by exact prefixLift 4522644
  have htrace : WordTrace (prefixWord ++ tailWord_4522644) baseStart_4522644 baseEnd_4522644 := by
    simpa [prefixWord, tailWord_4522644, baseEnd_4522644] using wordTrace_append hprefix tailTrace_4522644
  have hstable : (prefixWord ++ tailWord_4522644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522644).length < 2 ^ (prefixWord ++ tailWord_4522644).sum := by decide
  have hdescent : baseEnd_4522644 < baseStart_4522644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522647 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 2, 5, 2]
def baseStart_4522647 : Nat := 118140960795 + 4522647 * 2 ^ 59
def prefixEnd_4522647 : Nat := 4983230072969 + 3 ^ 40 * 4522647 * 2
def baseEnd_4522647 : Nat := 2322291741614871856513231

theorem tailTrace_4522647 : CollatzResearch.WordTrace tailWord_4522647 prefixEnd_4522647 2322291741614871856513231 := by
  unfold tailWord_4522647
  simp only [CollatzResearch.WordTrace]
  refine ⟨164954487646229800458278195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109969658430819866972185463 164954487646229800458278195)
  ·
    refine ⟨247431731469344700687417293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164954487646229800458278195 247431731469344700687417293)
    ·
      refine ⟨92786899301004262757781485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247431731469344700687417293 92786899301004262757781485)
      ·
        refine ⟨34795087237876598534168057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92786899301004262757781485 34795087237876598534168057)
        ·
          refine ⟨26096315428407448900626043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34795087237876598534168057 26096315428407448900626043)
          ·
            refine ⟨39144473142611173350939065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26096315428407448900626043 39144473142611173350939065)
            ·
              refine ⟨29358354856958380013204299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39144473142611173350939065 29358354856958380013204299)
              ·
                refine ⟨44037532285437570019806449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29358354856958380013204299 44037532285437570019806449)
                ·
                  refine ⟨33028149214078177514854837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44037532285437570019806449 33028149214078177514854837)
                  ·
                    refine ⟨3096388988819829142017641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33028149214078177514854837 3096388988819829142017641)
                    ·
                      refine ⟨2322291741614871856513231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3096388988819829142017641 2322291741614871856513231)
                      ·
                        rfl

theorem cell23_4522647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_4522647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522647 prefixEnd_4522647 := by exact prefixLift 4522647
  have htrace : WordTrace (prefixWord ++ tailWord_4522647) baseStart_4522647 baseEnd_4522647 := by
    simpa [prefixWord, tailWord_4522647, baseEnd_4522647] using wordTrace_append hprefix tailTrace_4522647
  have hstable : (prefixWord ++ tailWord_4522647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522647).length < 2 ^ (prefixWord ++ tailWord_4522647).sum := by decide
  have hdescent : baseEnd_4522647 < baseStart_4522647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522761 : List Nat := [1, 2, 1, 1, 3, 2, 4, 4, 1, 1, 3]
def baseStart_4522761 : Nat := 118140960795 + 4522761 * 2 ^ 59
def prefixEnd_4522761 : Nat := 4983230072969 + 3 ^ 40 * 4522761 * 2
def baseEnd_4522761 : Nat := 2322350278409484410487707

theorem tailTrace_4522761 : CollatzResearch.WordTrace tailWord_4522761 prefixEnd_4522761 2322350278409484410487707 := by
  unfold tailWord_4522761
  simp only [CollatzResearch.WordTrace]
  refine ⟨164958645567816797927928137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109972430378544531951952091 164958645567816797927928137)
  ·
    refine ⟨123718984175862598445946103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164958645567816797927928137 123718984175862598445946103)
    ·
      refine ⟨185578476263793897668919155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123718984175862598445946103 185578476263793897668919155)
      ·
        refine ⟨278367714395690846503378733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185578476263793897668919155 278367714395690846503378733)
        ·
          refine ⟨104387892898384067438767025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278367714395690846503378733 104387892898384067438767025)
          ·
            refine ⟨78290919673788050579075269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104387892898384067438767025 78290919673788050579075269)
            ·
              refine ⟨14679547438835259483576613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78290919673788050579075269 14679547438835259483576613)
              ·
                refine ⟨2752415144781611153170615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14679547438835259483576613 2752415144781611153170615)
                ·
                  refine ⟨4128622717172416729755923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2752415144781611153170615 4128622717172416729755923)
                  ·
                    refine ⟨6192934075758625094633885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4128622717172416729755923 6192934075758625094633885)
                    ·
                      refine ⟨2322350278409484410487707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6192934075758625094633885 2322350278409484410487707)
                      ·
                        rfl

theorem cell23_4522761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 1, 1, 3].length) (baseStart_4522761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522761 prefixEnd_4522761 := by exact prefixLift 4522761
  have htrace : WordTrace (prefixWord ++ tailWord_4522761) baseStart_4522761 baseEnd_4522761 := by
    simpa [prefixWord, tailWord_4522761, baseEnd_4522761] using wordTrace_append hprefix tailTrace_4522761
  have hstable : (prefixWord ++ tailWord_4522761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522761).length < 2 ^ (prefixWord ++ tailWord_4522761).sum := by decide
  have hdescent : baseEnd_4522761 < baseStart_4522761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522784 : List Nat := [2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 4]
def baseStart_4522784 : Nat := 118140960795 + 4522784 * 2 ^ 59
def prefixEnd_4522784 : Nat := 4983230072969 + 3 ^ 40 * 4522784 * 2
def baseEnd_4522784 : Nat := 2322362088464537820500101

theorem tailTrace_4522784 : CollatzResearch.WordTrace tailWord_4522784 prefixEnd_4522784 2322362088464537820500101 := by
  unfold tailWord_4522784
  simp only [CollatzResearch.WordTrace]
  refine ⟨82479742223366736428007703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109972989631155648570676937 82479742223366736428007703)
  ·
    refine ⟨123719613335050104642011555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82479742223366736428007703 123719613335050104642011555)
    ·
      refine ⟨185579420002575156963017333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123719613335050104642011555 185579420002575156963017333)
      ·
        refine ⟨17398070625241420965282875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 185579420002575156963017333 17398070625241420965282875)
        ·
          refine ⟨26097105937862131447924313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17398070625241420965282875 26097105937862131447924313)
          ·
            refine ⟨19572829453396598585943235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26097105937862131447924313 19572829453396598585943235)
            ·
              refine ⟨29359244180094897878914853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19572829453396598585943235 29359244180094897878914853)
              ·
                refine ⟨5504858283767793352296535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29359244180094897878914853 5504858283767793352296535)
                ·
                  refine ⟨8257287425651690028444803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5504858283767793352296535 8257287425651690028444803)
                  ·
                    refine ⟨12385931138477535042667205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8257287425651690028444803 12385931138477535042667205)
                    ·
                      refine ⟨2322362088464537820500101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12385931138477535042667205 2322362088464537820500101)
                      ·
                        rfl

theorem cell23_4522784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_4522784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522784 prefixEnd_4522784 := by exact prefixLift 4522784
  have htrace : WordTrace (prefixWord ++ tailWord_4522784) baseStart_4522784 baseEnd_4522784 := by
    simpa [prefixWord, tailWord_4522784, baseEnd_4522784] using wordTrace_append hprefix tailTrace_4522784
  have hstable : (prefixWord ++ tailWord_4522784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522784).length < 2 ^ (prefixWord ++ tailWord_4522784).sum := by decide
  have hdescent : baseEnd_4522784 < baseStart_4522784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522828 : List Nat := [2, 2, 1, 3, 3, 3, 2, 1, 2, 4]
def baseStart_4522828 : Nat := 118140960795 + 4522828 * 2 ^ 59
def prefixEnd_4522828 : Nat := 4983230072969 + 3 ^ 40 * 4522828 * 2
def baseEnd_4522828 : Nat := 774128227204445216116633

theorem tailTrace_4522828 : CollatzResearch.WordTrace tailWord_4522828 prefixEnd_4522828 774128227204445216116633 := by
  unfold tailWord_4522828
  simp only [CollatzResearch.WordTrace]
  refine ⟨82480544629287034185308569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109974059505716045580411425 82480544629287034185308569)
  ·
    refine ⟨61860408471965275638981427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82480544629287034185308569 61860408471965275638981427)
    ·
      refine ⟨92790612707947913458472141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61860408471965275638981427 92790612707947913458472141)
      ·
        refine ⟨34796479765480467546927053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92790612707947913458472141 34796479765480467546927053)
        ·
          refine ⟨13048679912055175330097645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34796479765480467546927053 13048679912055175330097645)
          ·
            refine ⟨4893254967020690748786617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13048679912055175330097645 4893254967020690748786617)
            ·
              refine ⟨3669941225265518061589963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4893254967020690748786617 3669941225265518061589963)
              ·
                refine ⟨5504911837898277092384945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3669941225265518061589963 5504911837898277092384945)
                ·
                  refine ⟨4128683878423707819288709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5504911837898277092384945 4128683878423707819288709)
                  ·
                    refine ⟨774128227204445216116633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4128683878423707819288709 774128227204445216116633)
                    ·
                      rfl

theorem cell23_4522828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_4522828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522828 prefixEnd_4522828 := by exact prefixLift 4522828
  have htrace : WordTrace (prefixWord ++ tailWord_4522828) baseStart_4522828 baseEnd_4522828 := by
    simpa [prefixWord, tailWord_4522828, baseEnd_4522828] using wordTrace_append hprefix tailTrace_4522828
  have hstable : (prefixWord ++ tailWord_4522828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522828).length < 2 ^ (prefixWord ++ tailWord_4522828).sum := by decide
  have hdescent : baseEnd_4522828 < baseStart_4522828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522834 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_4522834 : Nat := 118140960795 + 4522834 * 2 ^ 59
def prefixEnd_4522834 : Nat := 4983230072969 + 3 ^ 40 * 4522834 * 2
def baseEnd_4522834 : Nat := 2322387762497262624874871

theorem tailTrace_4522834 : CollatzResearch.WordTrace tailWord_4522834 prefixEnd_4522834 2322387762497262624874871 := by
  unfold tailWord_4522834
  simp only [CollatzResearch.WordTrace]
  refine ⟨41240327024138082848833889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109974205397701554263557037 41240327024138082848833889)
  ·
    refine ⟨30930245268103562136625417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41240327024138082848833889 30930245268103562136625417)
    ·
      refine ⟨23197683951077671602469063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30930245268103562136625417 23197683951077671602469063)
      ·
        refine ⟨34796525926616507403703595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23197683951077671602469063 34796525926616507403703595)
        ·
          refine ⟨52194788889924761105555393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34796525926616507403703595 52194788889924761105555393)
          ·
            refine ⟨39146091667443570829166545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52194788889924761105555393 39146091667443570829166545)
            ·
              refine ⟨29359568750582678121874909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39146091667443570829166545 29359568750582678121874909)
              ·
                refine ⟨11009838281468504295703091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29359568750582678121874909 11009838281468504295703091)
                ·
                  refine ⟨16514757422202756443554637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11009838281468504295703091 16514757422202756443554637)
                  ·
                    refine ⟨6193034033326033666332989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16514757422202756443554637 6193034033326033666332989)
                    ·
                      refine ⟨2322387762497262624874871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6193034033326033666332989 2322387762497262624874871)
                      ·
                        rfl

theorem cell23_4522834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_4522834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522834 prefixEnd_4522834 := by exact prefixLift 4522834
  have htrace : WordTrace (prefixWord ++ tailWord_4522834) baseStart_4522834 baseEnd_4522834 := by
    simpa [prefixWord, tailWord_4522834, baseEnd_4522834] using wordTrace_append hprefix tailTrace_4522834
  have hstable : (prefixWord ++ tailWord_4522834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522834).length < 2 ^ (prefixWord ++ tailWord_4522834).sum := by decide
  have hdescent : baseEnd_4522834 < baseStart_4522834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522874 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2]
def baseStart_4522874 : Nat := 118140960795 + 4522874 * 2 ^ 59
def prefixEnd_4522874 : Nat := 4983230072969 + 3 ^ 40 * 4522874 * 2
def baseEnd_4522874 : Nat := 2322408301723442468374687

theorem tailTrace_4522874 : CollatzResearch.WordTrace tailWord_4522874 prefixEnd_4522874 2322408301723442468374687 := by
  unfold tailWord_4522874
  simp only [CollatzResearch.WordTrace]
  refine ⟨41240691754101854556697919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109975178010938278817861117 41240691754101854556697919)
  ·
    refine ⟨61861037631152781835046879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41240691754101854556697919 61861037631152781835046879)
    ·
      refine ⟨92791556446729172752570319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61861037631152781835046879 92791556446729172752570319)
      ·
        refine ⟨139187334670093759128855479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92791556446729172752570319 139187334670093759128855479)
        ·
          refine ⟨208781002005140638693283219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139187334670093759128855479 208781002005140638693283219)
          ·
            refine ⟨313171503007710958039924829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208781002005140638693283219 313171503007710958039924829)
            ·
              refine ⟨117439313627891609264971811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 313171503007710958039924829 117439313627891609264971811)
              ·
                refine ⟨176158970441837413897457717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117439313627891609264971811 176158970441837413897457717)
                ·
                  refine ⟨16514903478922257552886661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176158970441837413897457717 16514903478922257552886661)
                  ·
                    refine ⟨3096544402297923291166249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16514903478922257552886661 3096544402297923291166249)
                    ·
                      refine ⟨2322408301723442468374687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3096544402297923291166249 2322408301723442468374687)
                      ·
                        rfl

theorem cell23_4522874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2].length) (baseStart_4522874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522874 prefixEnd_4522874 := by exact prefixLift 4522874
  have htrace : WordTrace (prefixWord ++ tailWord_4522874) baseStart_4522874 baseEnd_4522874 := by
    simpa [prefixWord, tailWord_4522874, baseEnd_4522874] using wordTrace_append hprefix tailTrace_4522874
  have hstable : (prefixWord ++ tailWord_4522874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522874).length < 2 ^ (prefixWord ++ tailWord_4522874).sum := by decide
  have hdescent : baseEnd_4522874 < baseStart_4522874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522877 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_4522877 : Nat := 118140960795 + 4522877 * 2 ^ 59
def prefixEnd_4522877 : Nat := 4983230072969 + 3 ^ 40 * 4522877 * 2
def baseEnd_4522877 : Nat := 2322409842165405956637173

theorem tailTrace_4522877 : CollatzResearch.WordTrace tailWord_4522877 prefixEnd_4522877 2322409842165405956637173 := by
  unfold tailWord_4522877
  simp only [CollatzResearch.WordTrace]
  refine ⟨164962876435396549739150885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109975250956931033159433923 164962876435396549739150885)
  ·
    refine ⟨30930539331636853076090791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164962876435396549739150885 30930539331636853076090791)
    ·
      refine ⟨46395808997455279614136187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30930539331636853076090791 46395808997455279614136187)
      ·
        refine ⟨69593713496182919421204281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46395808997455279614136187 69593713496182919421204281)
        ·
          refine ⟨52195285122137189565903211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69593713496182919421204281 52195285122137189565903211)
          ·
            refine ⟨78292927683205784348854817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52195285122137189565903211 78292927683205784348854817)
            ·
              refine ⟨58719695762404338261641113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78292927683205784348854817 58719695762404338261641113)
              ·
                refine ⟨44039771821803253696230835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58719695762404338261641113 44039771821803253696230835)
                ·
                  refine ⟨66059657732704880544346253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44039771821803253696230835 66059657732704880544346253)
                  ·
                    refine ⟨24772371649764330204129845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66059657732704880544346253 24772371649764330204129845)
                    ·
                      refine ⟨2322409842165405956637173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24772371649764330204129845 2322409842165405956637173)
                      ·
                        rfl

theorem cell23_4522877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_4522877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522877 prefixEnd_4522877 := by exact prefixLift 4522877
  have htrace : WordTrace (prefixWord ++ tailWord_4522877) baseStart_4522877 baseEnd_4522877 := by
    simpa [prefixWord, tailWord_4522877, baseEnd_4522877] using wordTrace_append hprefix tailTrace_4522877
  have hstable : (prefixWord ++ tailWord_4522877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522877).length < 2 ^ (prefixWord ++ tailWord_4522877).sum := by decide
  have hdescent : baseEnd_4522877 < baseStart_4522877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522965 : List Nat := [1, 3, 2, 3, 4, 1, 1, 3, 5]
def baseStart_4522965 : Nat := 118140960795 + 4522965 * 2 ^ 59
def prefixEnd_4522965 : Nat := 4983230072969 + 3 ^ 40 * 4522965 * 2
def baseEnd_4522965 : Nat := 258050558718111290259641

theorem tailTrace_4522965 : CollatzResearch.WordTrace tailWord_4522965 prefixEnd_4522965 258050558718111290259641 := by
  unfold tailWord_4522965
  simp only [CollatzResearch.WordTrace]
  refine ⟨164966086059077740768354349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109977390706051827178902899 164966086059077740768354349)
  ·
    refine ⟨61862282272154152788132881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164966086059077740768354349 61862282272154152788132881)
    ·
      refine ⟨46396711704115614591099661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61862282272154152788132881 46396711704115614591099661)
      ·
        refine ⟨17398766889043355471662373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46396711704115614591099661 17398766889043355471662373)
        ·
          refine ⟨3262268791695629150936695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17398766889043355471662373 3262268791695629150936695)
          ·
            refine ⟨4893403187543443726405043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3262268791695629150936695 4893403187543443726405043)
            ·
              refine ⟨7340104781315165589607565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4893403187543443726405043 7340104781315165589607565)
              ·
                refine ⟨2752539292993187096102837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7340104781315165589607565 2752539292993187096102837)
                ·
                  refine ⟨258050558718111290259641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2752539292993187096102837 258050558718111290259641)
                  ·
                    rfl

theorem cell23_4522965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 5].length) (baseStart_4522965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522965 prefixEnd_4522965 := by exact prefixLift 4522965
  have htrace : WordTrace (prefixWord ++ tailWord_4522965) baseStart_4522965 baseEnd_4522965 := by
    simpa [prefixWord, tailWord_4522965, baseEnd_4522965] using wordTrace_append hprefix tailTrace_4522965
  have hstable : (prefixWord ++ tailWord_4522965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522965).length < 2 ^ (prefixWord ++ tailWord_4522965).sum := by decide
  have hdescent : baseEnd_4522965 < baseStart_4522965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522978 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_4522978 : Nat := 118140960795 + 4522978 * 2 ^ 59
def prefixEnd_4522978 : Nat := 4983230072969 + 3 ^ 40 * 4522978 * 2
def baseEnd_4522978 : Nat := 774153901237170020491403

theorem tailTrace_4522978 : CollatzResearch.WordTrace tailWord_4522978 prefixEnd_4522978 774153901237170020491403 := by
  unfold tailWord_4522978
  simp only [CollatzResearch.WordTrace]
  refine ⟨41241640052007660997144397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109977706805353762659051725 41241640052007660997144397)
  ·
    refine ⟨15465615019502872873929149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41241640052007660997144397 15465615019502872873929149)
    ·
      refine ⟨5799605632313577327723431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15465615019502872873929149 5799605632313577327723431)
      ·
        refine ⟨8699408448470365991585147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5799605632313577327723431 8699408448470365991585147)
        ·
          refine ⟨13049112672705548987377721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8699408448470365991585147 13049112672705548987377721)
          ·
            refine ⟨9786834504529161740533291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13049112672705548987377721 9786834504529161740533291)
            ·
              refine ⟨14680251756793742610799937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9786834504529161740533291 14680251756793742610799937)
              ·
                refine ⟨11010188817595306958099953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14680251756793742610799937 11010188817595306958099953)
                ·
                  refine ⟨8257641613196480218574965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11010188817595306958099953 8257641613196480218574965)
                  ·
                    refine ⟨774153901237170020491403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8257641613196480218574965 774153901237170020491403)
                    ·
                      rfl

theorem cell23_4522978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_4522978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522978 prefixEnd_4522978 := by exact prefixLift 4522978
  have htrace : WordTrace (prefixWord ++ tailWord_4522978) baseStart_4522978 baseEnd_4522978 := by
    simpa [prefixWord, tailWord_4522978, baseEnd_4522978] using wordTrace_append hprefix tailTrace_4522978
  have hstable : (prefixWord ++ tailWord_4522978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522978).length < 2 ^ (prefixWord ++ tailWord_4522978).sum := by decide
  have hdescent : baseEnd_4522978 < baseStart_4522978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4522991 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 3, 4]
def baseStart_4522991 : Nat := 118140960795 + 4522991 * 2 ^ 59
def prefixEnd_4522991 : Nat := 4983230072969 + 3 ^ 40 * 4522991 * 2
def baseEnd_4522991 : Nat := 774156126320006170203883

theorem tailTrace_4522991 : CollatzResearch.WordTrace tailWord_4522991 prefixEnd_4522991 774156126320006170203883 := by
  unfold tailWord_4522991
  simp only [CollatzResearch.WordTrace]
  refine ⟨164967034356983547208800827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109978022904655698139200551 164967034356983547208800827)
  ·
    refine ⟨247450551535475320813201241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164967034356983547208800827 247450551535475320813201241)
    ·
      refine ⟨185587913651606490609900931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247450551535475320813201241 185587913651606490609900931)
      ·
        refine ⟨278381870477409735914851397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185587913651606490609900931 278381870477409735914851397)
        ·
          refine ⟨52196600714514325484034637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 278381870477409735914851397 52196600714514325484034637)
          ·
            refine ⟨19573725267942872056512989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52196600714514325484034637 19573725267942872056512989)
            ·
              refine ⟨7340146975478577021192371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19573725267942872056512989 7340146975478577021192371)
              ·
                refine ⟨11010220463217865531788557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7340146975478577021192371 11010220463217865531788557)
                ·
                  refine ⟨4128832673706699574420709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11010220463217865531788557 4128832673706699574420709)
                  ·
                    refine ⟨774156126320006170203883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4128832673706699574420709 774156126320006170203883)
                    ·
                      rfl

theorem cell23_4522991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 4].length) (baseStart_4522991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4522991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4522991 prefixEnd_4522991 := by exact prefixLift 4522991
  have htrace : WordTrace (prefixWord ++ tailWord_4522991) baseStart_4522991 baseEnd_4522991 := by
    simpa [prefixWord, tailWord_4522991, baseEnd_4522991] using wordTrace_append hprefix tailTrace_4522991
  have hstable : (prefixWord ++ tailWord_4522991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4522991).length < 2 ^ (prefixWord ++ tailWord_4522991).sum := by decide
  have hdescent : baseEnd_4522991 < baseStart_4522991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4522991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523018 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_4523018 : Nat := 118140960795 + 4523018 * 2 ^ 59
def prefixEnd_4523018 : Nat := 4983230072969 + 3 ^ 40 * 4523018 * 2
def baseEnd_4523018 : Nat := 2322482242937689904974025

theorem tailTrace_4523018 : CollatzResearch.WordTrace tailWord_4523018 prefixEnd_4523018 2322482242937689904974025 := by
  unfold tailWord_4523018
  simp only [CollatzResearch.WordTrace]
  refine ⟨41242004781971432705008427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109978679418590487213355805 41242004781971432705008427)
  ·
    refine ⟨61863007172957149057512641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41242004781971432705008427 61863007172957149057512641)
    ·
      refine ⟨46397255379717861793134481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61863007172957149057512641 46397255379717861793134481)
      ·
        refine ⟨34797941534788396344850861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46397255379717861793134481 34797941534788396344850861)
        ·
          refine ⟨13049228075545648629319073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34797941534788396344850861 13049228075545648629319073)
          ·
            refine ⟨9786921056659236471989305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13049228075545648629319073 9786921056659236471989305)
            ·
              refine ⟨7340190792494427353991979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9786921056659236471989305 7340190792494427353991979)
              ·
                refine ⟨11010286188741641030987969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7340190792494427353991979 11010286188741641030987969)
                ·
                  refine ⟨8257714641556230773240977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11010286188741641030987969 8257714641556230773240977)
                  ·
                    refine ⟨6193285981167173079930733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8257714641556230773240977 6193285981167173079930733)
                    ·
                      refine ⟨2322482242937689904974025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6193285981167173079930733 2322482242937689904974025)
                      ·
                        rfl

theorem cell23_4523018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_4523018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523018 prefixEnd_4523018 := by exact prefixLift 4523018
  have htrace : WordTrace (prefixWord ++ tailWord_4523018) baseStart_4523018 baseEnd_4523018 := by
    simpa [prefixWord, tailWord_4523018, baseEnd_4523018] using wordTrace_append hprefix tailTrace_4523018
  have hstable : (prefixWord ++ tailWord_4523018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523018).length < 2 ^ (prefixWord ++ tailWord_4523018).sum := by decide
  have hdescent : baseEnd_4523018 < baseStart_4523018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523042 : List Nat := [3, 3, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_4523042 : Nat := 118140960795 + 4523042 * 2 ^ 59
def prefixEnd_4523042 : Nat := 4983230072969 + 3 ^ 40 * 4523042 * 2
def baseEnd_4523042 : Nat := 774164855491132603691305

theorem tailTrace_4523042 : CollatzResearch.WordTrace tailWord_4523042 prefixEnd_4523042 774164855491132603691305 := by
  unfold tailWord_4523042
  simp only [CollatzResearch.WordTrace]
  refine ⟨41242223619949695729726845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109979262986532521945938253 41242223619949695729726845)
  ·
    refine ⟨15465833857481135898647567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41242223619949695729726845 15465833857481135898647567)
    ·
      refine ⟨23198750786221703847971351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15465833857481135898647567 23198750786221703847971351)
      ·
        refine ⟨34798126179332555771957027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23198750786221703847971351 34798126179332555771957027)
        ·
          refine ⟨52197189268998833657935541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34798126179332555771957027 52197189268998833657935541)
          ·
            refine ⟨4893486493968640655431457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52197189268998833657935541 4893486493968640655431457)
            ·
              refine ⟨3670114870476480491573593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4893486493968640655431457 3670114870476480491573593)
              ·
                refine ⟨2752586152857360368680195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3670114870476480491573593 2752586152857360368680195)
                ·
                  refine ⟨4128879229286040553020293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2752586152857360368680195 4128879229286040553020293)
                  ·
                    refine ⟨774164855491132603691305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4128879229286040553020293 774164855491132603691305)
                    ·
                      rfl

theorem cell23_4523042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_4523042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523042 prefixEnd_4523042 := by exact prefixLift 4523042
  have htrace : WordTrace (prefixWord ++ tailWord_4523042) baseStart_4523042 baseEnd_4523042 := by
    simpa [prefixWord, tailWord_4523042, baseEnd_4523042] using wordTrace_append hprefix tailTrace_4523042
  have hstable : (prefixWord ++ tailWord_4523042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523042).length < 2 ^ (prefixWord ++ tailWord_4523042).sum := by decide
  have hdescent : baseEnd_4523042 < baseStart_4523042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523071 : List Nat := [1, 1, 2, 2, 3, 1, 1, 6, 1, 1, 4]
def baseStart_4523071 : Nat := 118140960795 + 4523071 * 2 ^ 59
def prefixEnd_4523071 : Nat := 4983230072969 + 3 ^ 40 * 4523071 * 2
def baseEnd_4523071 : Nat := 2322509457412378197611281

theorem tailTrace_4523071 : CollatzResearch.WordTrace tailWord_4523071 prefixEnd_4523071 2322509457412378197611281 := by
  unfold tailWord_4523071
  simp only [CollatzResearch.WordTrace]
  refine ⟨164969952196693720871713067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109979968131129147247808711 164969952196693720871713067)
  ·
    refine ⟨247454928295040581307569601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164969952196693720871713067 247454928295040581307569601)
    ·
      refine ⟨185591196221280435980677201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247454928295040581307569601 185591196221280435980677201)
      ·
        refine ⟨139193397165960326985507901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185591196221280435980677201 139193397165960326985507901)
        ·
          refine ⟨52197523937235122619565463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139193397165960326985507901 52197523937235122619565463)
          ·
            refine ⟨78296285905852683929348195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52197523937235122619565463 78296285905852683929348195)
            ·
              refine ⟨117444428858779025894022293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78296285905852683929348195 117444428858779025894022293)
              ·
                refine ⟨5505207602755266838782295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117444428858779025894022293 5505207602755266838782295)
                ·
                  refine ⟨8257811404132900258173443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5505207602755266838782295 8257811404132900258173443)
                  ·
                    refine ⟨12386717106199350387260165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8257811404132900258173443 12386717106199350387260165)
                    ·
                      refine ⟨2322509457412378197611281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12386717106199350387260165 2322509457412378197611281)
                      ·
                        rfl

theorem cell23_4523071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_4523071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523071 prefixEnd_4523071 := by exact prefixLift 4523071
  have htrace : WordTrace (prefixWord ++ tailWord_4523071) baseStart_4523071 baseEnd_4523071 := by
    simpa [prefixWord, tailWord_4523071, baseEnd_4523071] using wordTrace_append hprefix tailTrace_4523071
  have hstable : (prefixWord ++ tailWord_4523071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523071).length < 2 ^ (prefixWord ++ tailWord_4523071).sum := by decide
  have hdescent : baseEnd_4523071 < baseStart_4523071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523084 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_4523084 : Nat := 118140960795 + 4523084 * 2 ^ 59
def prefixEnd_4523084 : Nat := 4983230072969 + 3 ^ 40 * 4523084 * 2
def baseEnd_4523084 : Nat := 2322516132660886646748721

theorem tailTrace_4523084 : CollatzResearch.WordTrace tailWord_4523084 prefixEnd_4523084 2322516132660886646748721 := by
  unfold tailWord_4523084
  simp only [CollatzResearch.WordTrace]
  refine ⟨82485213172823312045968153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109980284230431082727957537 82485213172823312045968153)
  ·
    refine ⟨61863909879617484034476115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82485213172823312045968153 61863909879617484034476115)
    ·
      refine ⟨92795864819426226051714173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61863909879617484034476115 92795864819426226051714173)
      ·
        refine ⟨34798449307284834769392815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92795864819426226051714173 34798449307284834769392815)
        ·
          refine ⟨52197673960927252154089223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34798449307284834769392815 52197673960927252154089223)
          ·
            refine ⟨78296510941390878231133835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52197673960927252154089223 78296510941390878231133835)
            ·
              refine ⟨117444766412086317346700753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78296510941390878231133835 117444766412086317346700753)
              ·
                refine ⟨88083574809064738010025565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117444766412086317346700753 88083574809064738010025565)
                ·
                  refine ⟨33031340553399276753759587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88083574809064738010025565 33031340553399276753759587)
                  ·
                    refine ⟨49547010830098915130639381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33031340553399276753759587 49547010830098915130639381)
                    ·
                      refine ⟨2322516132660886646748721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49547010830098915130639381 2322516132660886646748721)
                      ·
                        rfl

theorem cell23_4523084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_4523084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523084 prefixEnd_4523084 := by exact prefixLift 4523084
  have htrace : WordTrace (prefixWord ++ tailWord_4523084) baseStart_4523084 baseEnd_4523084 := by
    simpa [prefixWord, tailWord_4523084, baseEnd_4523084] using wordTrace_append hprefix tailTrace_4523084
  have hstable : (prefixWord ++ tailWord_4523084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523084).length < 2 ^ (prefixWord ++ tailWord_4523084).sum := by decide
  have hdescent : baseEnd_4523084 < baseStart_4523084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523085 : List Nat := [1, 6, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_4523085 : Nat := 118140960795 + 4523085 * 2 ^ 59
def prefixEnd_4523085 : Nat := 4983230072969 + 3 ^ 40 * 4523085 * 2
def baseEnd_4523085 : Nat := 774172215380513714278739

theorem tailTrace_4523085 : CollatzResearch.WordTrace tailWord_4523085 prefixEnd_4523085 774172215380513714278739 := by
  unfold tailWord_4523085
  simp only [CollatzResearch.WordTrace]
  refine ⟨164970462818643001262722709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109980308545762000841815139 164970462818643001262722709)
  ·
    refine ⟨7732990444623890684190127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 164970462818643001262722709 7732990444623890684190127)
    ·
      refine ⟨11599485666935836026285191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7732990444623890684190127 11599485666935836026285191)
      ·
        refine ⟨17399228500403754039427787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11599485666935836026285191 17399228500403754039427787)
        ·
          refine ⟨26098842750605631059141681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17399228500403754039427787 26098842750605631059141681)
          ·
            refine ⟨19574132062954223294356261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26098842750605631059141681 19574132062954223294356261)
            ·
              refine ⟨3670149761803916867691799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19574132062954223294356261 3670149761803916867691799)
              ·
                refine ⟨5505224642705875301537699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3670149761803916867691799 5505224642705875301537699)
                ·
                  refine ⟨8257836964058812952306549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5505224642705875301537699 8257836964058812952306549)
                  ·
                    refine ⟨774172215380513714278739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8257836964058812952306549 774172215380513714278739)
                    ·
                      rfl

theorem cell23_4523085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_4523085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523085 prefixEnd_4523085 := by exact prefixLift 4523085
  have htrace : WordTrace (prefixWord ++ tailWord_4523085) baseStart_4523085 baseEnd_4523085 := by
    simpa [prefixWord, tailWord_4523085, baseEnd_4523085] using wordTrace_append hprefix tailTrace_4523085
  have hstable : (prefixWord ++ tailWord_4523085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523085).length < 2 ^ (prefixWord ++ tailWord_4523085).sum := by decide
  have hdescent : baseEnd_4523085 < baseStart_4523085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523118 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_4523118 : Nat := 118140960795 + 4523118 * 2 ^ 59
def prefixEnd_4523118 : Nat := 4983230072969 + 3 ^ 40 * 4523118 * 2
def baseEnd_4523118 : Nat := 2322533591003139513723565

theorem tailTrace_4523118 : CollatzResearch.WordTrace tailWord_4523118 prefixEnd_4523118 2322533591003139513723565 := by
  unfold tailWord_4523118
  simp only [CollatzResearch.WordTrace]
  refine ⟨20621458303440430987334251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109981110951682298599116005 20621458303440430987334251)
  ·
    refine ⟨30932187455160646481001377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20621458303440430987334251 30932187455160646481001377)
    ·
      refine ⟨23199140591370484860751033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30932187455160646481001377 23199140591370484860751033)
      ·
        refine ⟨17399355443527863645563275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23199140591370484860751033 17399355443527863645563275)
        ·
          refine ⟨26099033165291795468344913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17399355443527863645563275 26099033165291795468344913)
          ·
            refine ⟨19574274873968846601258685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26099033165291795468344913 19574274873968846601258685)
            ·
              refine ⟨7340353077738317475472007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19574274873968846601258685 7340353077738317475472007)
              ·
                refine ⟨11010529616607476213208011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7340353077738317475472007 11010529616607476213208011)
                ·
                  refine ⟨16515794424911214319812017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11010529616607476213208011 16515794424911214319812017)
                  ·
                    refine ⟨12386845818683410739859013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16515794424911214319812017 12386845818683410739859013)
                    ·
                      refine ⟨2322533591003139513723565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12386845818683410739859013 2322533591003139513723565)
                      ·
                        rfl

theorem cell23_4523118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_4523118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523118 prefixEnd_4523118 := by exact prefixLift 4523118
  have htrace : WordTrace (prefixWord ++ tailWord_4523118) baseStart_4523118 baseEnd_4523118 := by
    simpa [prefixWord, tailWord_4523118, baseEnd_4523118] using wordTrace_append hprefix tailTrace_4523118
  have hstable : (prefixWord ++ tailWord_4523118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523118).length < 2 ^ (prefixWord ++ tailWord_4523118).sum := by decide
  have hdescent : baseEnd_4523118 < baseStart_4523118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523121 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 1, 3, 3]
def baseStart_4523121 : Nat := 118140960795 + 4523121 * 2 ^ 59
def prefixEnd_4523121 : Nat := 4983230072969 + 3 ^ 40 * 4523121 * 2
def baseEnd_4523121 : Nat := 2322535131445103001986051

theorem tailTrace_4523121 : CollatzResearch.WordTrace tailWord_4523121 prefixEnd_4523121 2322535131445103001986051 := by
  unfold tailWord_4523121
  simp only [CollatzResearch.WordTrace]
  refine ⟨164971775846512579411033217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109981183897675052940688811 164971775846512579411033217)
  ·
    refine ⟨123728831884884434558274913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164971775846512579411033217 123728831884884434558274913)
    ·
      refine ⟨92796623913663325918706185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123728831884884434558274913 92796623913663325918706185)
      ·
        refine ⟨69597467935247494439029639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92796623913663325918706185 69597467935247494439029639)
        ·
          refine ⟨104396201902871241658544459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69597467935247494439029639 104396201902871241658544459)
          ·
            refine ⟨156594302854306862487816689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104396201902871241658544459 156594302854306862487816689)
            ·
              refine ⟨117445727140730146865862517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156594302854306862487816689 117445727140730146865862517)
              ·
                refine ⟨11010536919443451268674611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117445727140730146865862517 11010536919443451268674611)
                ·
                  refine ⟨16515805379165176903011917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11010536919443451268674611 16515805379165176903011917)
                  ·
                    refine ⟨6193427017186941338629469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16515805379165176903011917 6193427017186941338629469)
                    ·
                      refine ⟨2322535131445103001986051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6193427017186941338629469 2322535131445103001986051)
                      ·
                        rfl

theorem cell23_4523121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_4523121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523121 prefixEnd_4523121 := by exact prefixLift 4523121
  have htrace : WordTrace (prefixWord ++ tailWord_4523121) baseStart_4523121 baseEnd_4523121 := by
    simpa [prefixWord, tailWord_4523121, baseEnd_4523121] using wordTrace_append hprefix tailTrace_4523121
  have hstable : (prefixWord ++ tailWord_4523121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523121).length < 2 ^ (prefixWord ++ tailWord_4523121).sum := by decide
  have hdescent : baseEnd_4523121 < baseStart_4523121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523131 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 2, 7, 2]
def baseStart_4523131 : Nat := 118140960795 + 4523131 * 2 ^ 59
def prefixEnd_4523131 : Nat := 4983230072969 + 3 ^ 40 * 4523131 * 2
def baseEnd_4523131 : Nat := 2322540266251647962861005

theorem tailTrace_4523131 : CollatzResearch.WordTrace tailWord_4523131 prefixEnd_4523131 2322540266251647962861005 := by
  unfold tailWord_4523131
  simp only [CollatzResearch.WordTrace]
  refine ⟨164972140576476351118897247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109981427050984234079264831 164972140576476351118897247)
  ·
    refine ⟨247458210864714526678345871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164972140576476351118897247 247458210864714526678345871)
    ·
      refine ⟨371187316297071790017518807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247458210864714526678345871 371187316297071790017518807)
      ·
        refine ⟨556780974445607685026278211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371187316297071790017518807 556780974445607685026278211)
        ·
          refine ⟨835171461668411527539417317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556780974445607685026278211 835171461668411527539417317)
          ·
            refine ⟨156594649062827161413640747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 835171461668411527539417317 156594649062827161413640747)
            ·
              refine ⟨234891973594240742120461121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156594649062827161413640747 234891973594240742120461121)
              ·
                refine ⟨176168980195680556590345841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234891973594240742120461121 176168980195680556590345841)
                ·
                  refine ⟨132126735146760417442759381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176168980195680556590345841 132126735146760417442759381)
                  ·
                    refine ⟨3096720355002197283814673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 132126735146760417442759381 3096720355002197283814673)
                    ·
                      refine ⟨2322540266251647962861005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3096720355002197283814673 2322540266251647962861005)
                      ·
                        rfl

theorem cell23_4523131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 7, 2].length) (baseStart_4523131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523131 prefixEnd_4523131 := by exact prefixLift 4523131
  have htrace : WordTrace (prefixWord ++ tailWord_4523131) baseStart_4523131 baseEnd_4523131 := by
    simpa [prefixWord, tailWord_4523131, baseEnd_4523131] using wordTrace_append hprefix tailTrace_4523131
  have hstable : (prefixWord ++ tailWord_4523131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523131).length < 2 ^ (prefixWord ++ tailWord_4523131).sum := by decide
  have hdescent : baseEnd_4523131 < baseStart_4523131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523172 : List Nat := [2, 3, 1, 2, 3, 1, 4, 1, 2, 1, 3]
def baseStart_4523172 : Nat := 118140960795 + 4523172 * 2 ^ 59
def prefixEnd_4523172 : Nat := 4983230072969 + 3 ^ 40 * 4523172 * 2
def baseEnd_4523172 : Nat := 2322561318958482302448317

theorem tailTrace_4523172 : CollatzResearch.WordTrace tailWord_4523172 prefixEnd_4523172 2322561318958482302448317 := by
  unfold tailWord_4523172
  simp only [CollatzResearch.WordTrace]
  refine ⟨82486817984663907560569885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109982423979551876747426513 82486817984663907560569885)
  ·
    refine ⟨30932556744248965335213707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82486817984663907560569885 30932556744248965335213707)
    ·
      refine ⟨46398835116373448002820561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30932556744248965335213707 46398835116373448002820561)
      ·
        refine ⟨34799126337280086002115421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46398835116373448002820561 34799126337280086002115421)
        ·
          refine ⟨13049672376480032250793283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34799126337280086002115421 13049672376480032250793283)
          ·
            refine ⟨19574508564720048376189925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13049672376480032250793283 19574508564720048376189925)
            ·
              refine ⟨3670220355885009070535611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19574508564720048376189925 3670220355885009070535611)
              ·
                refine ⟨5505330533827513605803417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3670220355885009070535611 5505330533827513605803417)
                ·
                  refine ⟨4128997900370635204352563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5505330533827513605803417 4128997900370635204352563)
                  ·
                    refine ⟨6193496850555952806528845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4128997900370635204352563 6193496850555952806528845)
                    ·
                      refine ⟨2322561318958482302448317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6193496850555952806528845 2322561318958482302448317)
                      ·
                        rfl

theorem cell23_4523172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_4523172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523172 prefixEnd_4523172 := by exact prefixLift 4523172
  have htrace : WordTrace (prefixWord ++ tailWord_4523172) baseStart_4523172 baseEnd_4523172 := by
    simpa [prefixWord, tailWord_4523172, baseEnd_4523172] using wordTrace_append hprefix tailTrace_4523172
  have hstable : (prefixWord ++ tailWord_4523172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523172).length < 2 ^ (prefixWord ++ tailWord_4523172).sum := by decide
  have hdescent : baseEnd_4523172 < baseStart_4523172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523198 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_4523198 : Nat := 118140960795 + 4523198 * 2 ^ 59
def prefixEnd_4523198 : Nat := 4983230072969 + 3 ^ 40 * 4523198 * 2
def baseEnd_4523198 : Nat := 2322574669455499200723197

theorem tailTrace_4523198 : CollatzResearch.WordTrace tailWord_4523198 prefixEnd_4523198 2322574669455499200723197 := by
  unfold tailWord_4523198
  simp only [CollatzResearch.WordTrace]
  refine ⟨20621823033404202695198281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109983056178155747707724165 20621823033404202695198281)
  ·
    refine ⟨15466367275053152021398711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20621823033404202695198281 15466367275053152021398711)
    ·
      refine ⟨23199550912579728032098067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15466367275053152021398711 23199550912579728032098067)
      ·
        refine ⟨34799326368869592048147101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23199550912579728032098067 34799326368869592048147101)
        ·
          refine ⟨13049747388326097018055163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34799326368869592048147101 13049747388326097018055163)
          ·
            refine ⟨19574621082489145527082745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13049747388326097018055163 19574621082489145527082745)
            ·
              refine ⟨14680965811866859145312059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19574621082489145527082745 14680965811866859145312059)
              ·
                refine ⟨22021448717800288717968089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14680965811866859145312059 22021448717800288717968089)
                ·
                  refine ⟨16516086538350216538476067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22021448717800288717968089 16516086538350216538476067)
                  ·
                    refine ⟨24774129807525324807714101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16516086538350216538476067 24774129807525324807714101)
                    ·
                      refine ⟨2322574669455499200723197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24774129807525324807714101 2322574669455499200723197)
                      ·
                        rfl

theorem cell23_4523198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_4523198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523198 prefixEnd_4523198 := by exact prefixLift 4523198
  have htrace : WordTrace (prefixWord ++ tailWord_4523198) baseStart_4523198 baseEnd_4523198 := by
    simpa [prefixWord, tailWord_4523198, baseEnd_4523198] using wordTrace_append hprefix tailTrace_4523198
  have hstable : (prefixWord ++ tailWord_4523198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523198).length < 2 ^ (prefixWord ++ tailWord_4523198).sum := by decide
  have hdescent : baseEnd_4523198 < baseStart_4523198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523231 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 4, 5]
def baseStart_4523231 : Nat := 118140960795 + 4523231 * 2 ^ 59
def prefixEnd_4523231 : Nat := 4983230072969 + 3 ^ 40 * 4523231 * 2
def baseEnd_4523231 : Nat := 774197204772365857203515

theorem tailTrace_4523231 : CollatzResearch.WordTrace tailWord_4523231 prefixEnd_4523231 774197204772365857203515 := by
  unfold tailWord_4523231
  simp only [CollatzResearch.WordTrace]
  refine ⟨164975787876114068197537547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109983858584076045465025031 164975787876114068197537547)
  ·
    refine ⟨247463681814171102296306321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164975787876114068197537547 247463681814171102296306321)
    ·
      refine ⟨185597761360628326722229741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247463681814171102296306321 185597761360628326722229741)
      ·
        refine ⟨69599160510235622520836153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185597761360628326722229741 69599160510235622520836153)
        ·
          refine ⟨52199370382676716890627115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69599160510235622520836153 52199370382676716890627115)
          ·
            refine ⟨78299055574015075335940673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52199370382676716890627115 78299055574015075335940673)
            ·
              refine ⟨58724291680511306501955505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78299055574015075335940673 58724291680511306501955505)
              ·
                refine ⟨44043218760383479876466629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58724291680511306501955505 44043218760383479876466629)
                ·
                  refine ⟨8258103517571902476837493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44043218760383479876466629 8258103517571902476837493)
                  ·
                    refine ⟨774197204772365857203515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8258103517571902476837493 774197204772365857203515)
                    ·
                      rfl

theorem cell23_4523231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 5].length) (baseStart_4523231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523231 prefixEnd_4523231 := by exact prefixLift 4523231
  have htrace : WordTrace (prefixWord ++ tailWord_4523231) baseStart_4523231 baseEnd_4523231 := by
    simpa [prefixWord, tailWord_4523231, baseEnd_4523231] using wordTrace_append hprefix tailTrace_4523231
  have hstable : (prefixWord ++ tailWord_4523231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523231).length < 2 ^ (prefixWord ++ tailWord_4523231).sum := by decide
  have hdescent : baseEnd_4523231 < baseStart_4523231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523281 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_4523281 : Nat := 118140960795 + 4523281 * 2 ^ 59
def prefixEnd_4523281 : Nat := 4983230072969 + 3 ^ 40 * 4523281 * 2
def baseEnd_4523281 : Nat := 2322617288349822375985315

theorem tailTrace_4523281 : CollatzResearch.WordTrace tailWord_4523281 prefixEnd_4523281 2322617288349822375985315 := by
  unfold tailWord_4523281
  simp only [CollatzResearch.WordTrace]
  refine ⟨164977611525932926736857697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109985074350621951157905131 164977611525932926736857697)
  ·
    refine ⟨123733208644449695052643273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164977611525932926736857697 123733208644449695052643273)
    ·
      refine ⟨92799906483337271289482455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123733208644449695052643273 92799906483337271289482455)
      ·
        refine ⟨139199859725005906934223683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92799906483337271289482455 139199859725005906934223683)
        ·
          refine ⟨208799789587508860401335525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139199859725005906934223683 208799789587508860401335525)
          ·
            refine ⟨39149960547657911325250411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 208799789587508860401335525 39149960547657911325250411)
            ·
              refine ⟨58724940821486866987875617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39149960547657911325250411 58724940821486866987875617)
              ·
                refine ⟨44043705616115150240906713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58724940821486866987875617 44043705616115150240906713)
                ·
                  refine ⟨33032779212086362680680035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44043705616115150240906713 33032779212086362680680035)
                  ·
                    refine ⟨49549168818129544021020053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33032779212086362680680035 49549168818129544021020053)
                    ·
                      refine ⟨2322617288349822375985315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49549168818129544021020053 2322617288349822375985315)
                      ·
                        rfl

theorem cell23_4523281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_4523281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523281 prefixEnd_4523281 := by exact prefixLift 4523281
  have htrace : WordTrace (prefixWord ++ tailWord_4523281) baseStart_4523281 baseEnd_4523281 := by
    simpa [prefixWord, tailWord_4523281, baseEnd_4523281] using wordTrace_append hprefix tailTrace_4523281
  have hstable : (prefixWord ++ tailWord_4523281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523281).length < 2 ^ (prefixWord ++ tailWord_4523281).sum := by decide
  have hdescent : baseEnd_4523281 < baseStart_4523281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523288 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 1, 4, 3]
def baseStart_4523288 : Nat := 118140960795 + 4523288 * 2 ^ 59
def prefixEnd_4523288 : Nat := 4983230072969 + 3 ^ 40 * 4523288 * 2
def baseEnd_4523288 : Nat := 2322620882714403848597783

theorem tailTrace_4523288 : CollatzResearch.WordTrace tailWord_4523288 prefixEnd_4523288 2322620882714403848597783 := by
  unfold tailWord_4523288
  simp only [CollatzResearch.WordTrace]
  refine ⟨82488933418453783466181259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109985244557938377954908345 82488933418453783466181259)
  ·
    refine ⟨123733400127680675199271889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82488933418453783466181259 123733400127680675199271889)
    ·
      refine ⟨92800050095760506399453917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123733400127680675199271889 92800050095760506399453917)
      ·
        refine ⟨34800018785910189899795219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92800050095760506399453917 34800018785910189899795219)
        ·
          refine ⟨52200028178865284849692829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34800018785910189899795219 52200028178865284849692829)
          ·
            refine ⟨19575010567074481818634811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52200028178865284849692829 19575010567074481818634811)
            ·
              refine ⟨29362515850611722727952217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19575010567074481818634811 29362515850611722727952217)
              ·
                refine ⟨22021886887958792045964163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29362515850611722727952217 22021886887958792045964163)
                ·
                  refine ⟨33032830331938188068946245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22021886887958792045964163 33032830331938188068946245)
                  ·
                    refine ⟨6193655687238410262927421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33032830331938188068946245 6193655687238410262927421)
                    ·
                      refine ⟨2322620882714403848597783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6193655687238410262927421 2322620882714403848597783)
                      ·
                        rfl

theorem cell23_4523288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_4523288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523288 prefixEnd_4523288 := by exact prefixLift 4523288
  have htrace : WordTrace (prefixWord ++ tailWord_4523288) baseStart_4523288 baseEnd_4523288 := by
    simpa [prefixWord, tailWord_4523288, baseEnd_4523288] using wordTrace_append hprefix tailTrace_4523288
  have hstable : (prefixWord ++ tailWord_4523288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523288).length < 2 ^ (prefixWord ++ tailWord_4523288).sum := by decide
  have hdescent : baseEnd_4523288 < baseStart_4523288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523331 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 7]
def baseStart_4523331 : Nat := 118140960795 + 4523331 * 2 ^ 59
def prefixEnd_4523331 : Nat := 4983230072969 + 3 ^ 40 * 4523331 * 2
def baseEnd_4523331 : Nat := 2322642962382547180360085

theorem tailTrace_4523331 : CollatzResearch.WordTrace tailWord_4523331 prefixEnd_4523331 2322642962382547180360085 := by
  unfold tailWord_4523331
  simp only [CollatzResearch.WordTrace]
  refine ⟨164979435175751785276177847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109986290117167856850785231 164979435175751785276177847)
  ·
    refine ⟨247469152763627677914266771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164979435175751785276177847 247469152763627677914266771)
    ·
      refine ⟨371203729145441516871400157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247469152763627677914266771 371203729145441516871400157)
      ·
        refine ⟨139201398429540568826775059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 371203729145441516871400157 139201398429540568826775059)
        ·
          refine ⟨208802097644310853240162589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139201398429540568826775059 208802097644310853240162589)
          ·
            refine ⟨78300786616616569965060971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208802097644310853240162589 78300786616616569965060971)
            ·
              refine ⟨117451179924924854947591457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78300786616616569965060971 117451179924924854947591457)
              ·
                refine ⟨88088384943693641210693593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117451179924924854947591457 88088384943693641210693593)
                ·
                  refine ⟨66066288707770230908020195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88088384943693641210693593 66066288707770230908020195)
                  ·
                    refine ⟨99099433061655346362030293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66066288707770230908020195 99099433061655346362030293)
                    ·
                      refine ⟨2322642962382547180360085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99099433061655346362030293 2322642962382547180360085)
                      ·
                        rfl

theorem cell23_4523331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_4523331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523331 prefixEnd_4523331 := by exact prefixLift 4523331
  have htrace : WordTrace (prefixWord ++ tailWord_4523331) baseStart_4523331 baseEnd_4523331 := by
    simpa [prefixWord, tailWord_4523331, baseEnd_4523331] using wordTrace_append hprefix tailTrace_4523331
  have hstable : (prefixWord ++ tailWord_4523331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523331).length < 2 ^ (prefixWord ++ tailWord_4523331).sum := by decide
  have hdescent : baseEnd_4523331 < baseStart_4523331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523345 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 4, 3, 2]
def baseStart_4523345 : Nat := 118140960795 + 4523345 * 2 ^ 59
def prefixEnd_4523345 : Nat := 4983230072969 + 3 ^ 40 * 4523345 * 2
def baseEnd_4523345 : Nat := 2322650151111710125585021

theorem tailTrace_4523345 : CollatzResearch.WordTrace tailWord_4523345 prefixEnd_4523345 2322650151111710125585021 := by
  unfold tailWord_4523345
  simp only [CollatzResearch.WordTrace]
  refine ⟨164979945797701065667187489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109986630531800710444791659 164979945797701065667187489)
  ·
    refine ⟨123734959348275799250390617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164979945797701065667187489 123734959348275799250390617)
    ·
      refine ⟨92801219511206849437792963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123734959348275799250390617 92801219511206849437792963)
      ·
        refine ⟨139201829266810274156689445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92801219511206849437792963 139201829266810274156689445)
        ·
          refine ⟨26100342987526926404379271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139201829266810274156689445 26100342987526926404379271)
          ·
            refine ⟨39150514481290389606568907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26100342987526926404379271 39150514481290389606568907)
            ·
              refine ⟨58725771721935584409853361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39150514481290389606568907 58725771721935584409853361)
              ·
                refine ⟨44044328791451688307390021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58725771721935584409853361 44044328791451688307390021)
                ·
                  refine ⟨8258311648397191557635629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44044328791451688307390021 8258311648397191557635629)
                  ·
                    refine ⟨3096866868148946834113361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8258311648397191557635629 3096866868148946834113361)
                    ·
                      refine ⟨2322650151111710125585021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3096866868148946834113361 2322650151111710125585021)
                      ·
                        rfl

theorem cell23_4523345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 3, 2].length) (baseStart_4523345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523345 prefixEnd_4523345 := by exact prefixLift 4523345
  have htrace : WordTrace (prefixWord ++ tailWord_4523345) baseStart_4523345 baseEnd_4523345 := by
    simpa [prefixWord, tailWord_4523345, baseEnd_4523345] using wordTrace_append hprefix tailTrace_4523345
  have hstable : (prefixWord ++ tailWord_4523345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523345).length < 2 ^ (prefixWord ++ tailWord_4523345).sum := by decide
  have hdescent : baseEnd_4523345 < baseStart_4523345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523372 : List Nat := [2, 2, 1, 1, 5, 2, 3, 1, 1, 5]
def baseStart_4523372 : Nat := 118140960795 + 4523372 * 2 ^ 59
def prefixEnd_4523372 : Nat := 4983230072969 + 3 ^ 40 * 4523372 * 2
def baseEnd_4523372 : Nat := 774221338363127173315799

theorem tailTrace_4523372 : CollatzResearch.WordTrace tailWord_4523372 prefixEnd_4523372 774221338363127173315799 := by
  unfold tailWord_4523372
  simp only [CollatzResearch.WordTrace]
  refine ⟨82490465284301624639210185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109987287045735499518946913 82490465284301624639210185)
  ·
    refine ⟨61867848963226218479407639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82490465284301624639210185 61867848963226218479407639)
    ·
      refine ⟨92801773444839327719111459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61867848963226218479407639 92801773444839327719111459)
      ·
        refine ⟨139202660167258991578667189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92801773444839327719111459 139202660167258991578667189)
        ·
          refine ⟨13050249390680530460500049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139202660167258991578667189 13050249390680530460500049)
          ·
            refine ⟨9787687043010397845375037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13050249390680530460500049 9787687043010397845375037)
            ·
              refine ⟨3670382641128899192015639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9787687043010397845375037 3670382641128899192015639)
              ·
                refine ⟨5505573961693348788023459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3670382641128899192015639 5505573961693348788023459)
                ·
                  refine ⟨8258360942540023182035189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5505573961693348788023459 8258360942540023182035189)
                  ·
                    refine ⟨774221338363127173315799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8258360942540023182035189 774221338363127173315799)
                    ·
                      rfl

theorem cell23_4523372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_4523372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523372 prefixEnd_4523372 := by exact prefixLift 4523372
  have htrace : WordTrace (prefixWord ++ tailWord_4523372) baseStart_4523372 baseEnd_4523372 := by
    simpa [prefixWord, tailWord_4523372, baseEnd_4523372] using wordTrace_append hprefix tailTrace_4523372
  have hstable : (prefixWord ++ tailWord_4523372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523372).length < 2 ^ (prefixWord ++ tailWord_4523372).sum := by decide
  have hdescent : baseEnd_4523372 < baseStart_4523372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523385 : List Nat := [1, 2, 1, 3, 2, 1, 3, 4, 2, 4]
def baseStart_4523385 : Nat := 118140960795 + 4523385 * 2 ^ 59
def prefixEnd_4523385 : Nat := 4983230072969 + 3 ^ 40 * 4523385 * 2
def baseEnd_4523385 : Nat := 774223563445963323028279

theorem tailTrace_4523385 : CollatzResearch.WordTrace tailWord_4523385 prefixEnd_4523385 774223563445963323028279 := by
  unfold tailWord_4523385
  simp only [CollatzResearch.WordTrace]
  refine ⟨164981404717556152498643609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109987603145037434999095739 164981404717556152498643609)
  ·
    refine ⟨123736053538167114373982707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164981404717556152498643609 123736053538167114373982707)
    ·
      refine ⟨185604080307250671560974061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123736053538167114373982707 185604080307250671560974061)
      ·
        refine ⟨69601530115219001835365273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185604080307250671560974061 69601530115219001835365273)
        ·
          refine ⟨52201147586414251376523955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69601530115219001835365273 52201147586414251376523955)
          ·
            refine ⟨78301721379621377064785933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52201147586414251376523955 78301721379621377064785933)
            ·
              refine ⟨29363145517358016399294725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78301721379621377064785933 29363145517358016399294725)
              ·
                refine ⟨5505589784504628074867761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29363145517358016399294725 5505589784504628074867761)
                ·
                  refine ⟨4129192338378471056150821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5505589784504628074867761 4129192338378471056150821)
                  ·
                    refine ⟨774223563445963323028279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4129192338378471056150821 774223563445963323028279)
                    ·
                      rfl

theorem cell23_4523385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 4].length) (baseStart_4523385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523385 prefixEnd_4523385 := by exact prefixLift 4523385
  have htrace : WordTrace (prefixWord ++ tailWord_4523385) baseStart_4523385 baseEnd_4523385 := by
    simpa [prefixWord, tailWord_4523385, baseEnd_4523385] using wordTrace_append hprefix tailTrace_4523385
  have hstable : (prefixWord ++ tailWord_4523385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523385).length < 2 ^ (prefixWord ++ tailWord_4523385).sum := by decide
  have hdescent : baseEnd_4523385 < baseStart_4523385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523388 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_4523388 : Nat := 118140960795 + 4523388 * 2 ^ 59
def prefixEnd_4523388 : Nat := 4983230072969 + 3 ^ 40 * 4523388 * 2
def baseEnd_4523388 : Nat := 2322672230779853457347323

theorem tailTrace_4523388 : CollatzResearch.WordTrace tailWord_4523388 prefixEnd_4523388 2322672230779853457347323 := by
  unfold tailWord_4523388
  simp only [CollatzResearch.WordTrace]
  refine ⟨82490757068272642005501409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109987676091030189340668545 82490757068272642005501409)
  ·
    refine ⟨61868067801204481504126057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82490757068272642005501409 61868067801204481504126057)
    ·
      refine ⟨46401050850903361128094543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61868067801204481504126057 46401050850903361128094543)
      ·
        refine ⟨69601576276355041692141815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46401050850903361128094543 69601576276355041692141815)
        ·
          refine ⟨104402364414532562538212723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69601576276355041692141815 104402364414532562538212723)
          ·
            refine ⟨156603546621798843807319085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104402364414532562538212723 156603546621798843807319085)
            ·
              refine ⟨58726329983174566427744657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156603546621798843807319085 58726329983174566427744657)
              ·
                refine ⟨44044747487380924820808493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58726329983174566427744657 44044747487380924820808493)
                ·
                  refine ⟨16516780307767846807803185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44044747487380924820808493 16516780307767846807803185)
                  ·
                    refine ⟨12387585230825885105852389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16516780307767846807803185 12387585230825885105852389)
                    ·
                      refine ⟨2322672230779853457347323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12387585230825885105852389 2322672230779853457347323)
                      ·
                        rfl

theorem cell23_4523388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_4523388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523388 prefixEnd_4523388 := by exact prefixLift 4523388
  have htrace : WordTrace (prefixWord ++ tailWord_4523388) baseStart_4523388 baseEnd_4523388 := by
    simpa [prefixWord, tailWord_4523388, baseEnd_4523388] using wordTrace_append hprefix tailTrace_4523388
  have hstable : (prefixWord ++ tailWord_4523388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523388).length < 2 ^ (prefixWord ++ tailWord_4523388).sum := by decide
  have hdescent : baseEnd_4523388 < baseStart_4523388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523395 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 3]
def baseStart_4523395 : Nat := 118140960795 + 4523395 * 2 ^ 59
def prefixEnd_4523395 : Nat := 4983230072969 + 3 ^ 40 * 4523395 * 2
def baseEnd_4523395 : Nat := 2322675825144434929959791

theorem tailTrace_4523395 : CollatzResearch.WordTrace tailWord_4523395 prefixEnd_4523395 2322675825144434929959791 := by
  unfold tailWord_4523395
  simp only [CollatzResearch.WordTrace]
  refine ⟨164981769447519924206507639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109987846298346616137671759 164981769447519924206507639)
  ·
    refine ⟨247472654171279886309761459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164981769447519924206507639 247472654171279886309761459)
    ·
      refine ⟨371208981256919829464642189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247472654171279886309761459 371208981256919829464642189)
      ·
        refine ⟨139203367971344936049240821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 371208981256919829464642189 139203367971344936049240821)
        ·
          refine ⟨13050315747313587754616327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139203367971344936049240821 13050315747313587754616327)
          ·
            refine ⟨19575473620970381631924491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13050315747313587754616327 19575473620970381631924491)
            ·
              refine ⟨29363210431455572447886737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19575473620970381631924491 29363210431455572447886737)
              ·
                refine ⟨22022407823591679335915053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29363210431455572447886737 22022407823591679335915053)
                ·
                  refine ⟨8258402933846879750968145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22022407823591679335915053 8258402933846879750968145)
                  ·
                    refine ⟨6193802200385159813226109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8258402933846879750968145 6193802200385159813226109)
                    ·
                      refine ⟨2322675825144434929959791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6193802200385159813226109 2322675825144434929959791)
                      ·
                        rfl

theorem cell23_4523395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_4523395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523395 prefixEnd_4523395 := by exact prefixLift 4523395
  have htrace : WordTrace (prefixWord ++ tailWord_4523395) baseStart_4523395 baseEnd_4523395 := by
    simpa [prefixWord, tailWord_4523395, baseEnd_4523395] using wordTrace_append hprefix tailTrace_4523395
  have hstable : (prefixWord ++ tailWord_4523395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523395).length < 2 ^ (prefixWord ++ tailWord_4523395).sum := by decide
  have hdescent : baseEnd_4523395 < baseStart_4523395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523412 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_4523412 : Nat := 118140960795 + 4523412 * 2 ^ 59
def prefixEnd_4523412 : Nat := 4983230072969 + 3 ^ 40 * 4523412 * 2
def baseEnd_4523412 : Nat := 2322684554315561363447213

theorem tailTrace_4523412 : CollatzResearch.WordTrace tailWord_4523412 prefixEnd_4523412 2322684554315561363447213 := by
  unfold tailWord_4523412
  simp only [CollatzResearch.WordTrace]
  refine ⟨82491194744229168054938245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109988259658972224073250993 82491194744229168054938245)
  ·
    refine ⟨15467099014542969010300921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82491194744229168054938245 15467099014542969010300921)
    ·
      refine ⟨11600324260907226757725691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15467099014542969010300921 11600324260907226757725691)
      ·
        refine ⟨17400486391360840136588537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11600324260907226757725691 17400486391360840136588537)
        ·
          refine ⟨13050364793520630102441403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17400486391360840136588537 13050364793520630102441403)
          ·
            refine ⟨19575547190280945153662105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13050364793520630102441403 19575547190280945153662105)
            ·
              refine ⟨14681660392710708865246579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19575547190280945153662105 14681660392710708865246579)
              ·
                refine ⟨22022490589066063297869869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14681660392710708865246579 22022490589066063297869869)
                ·
                  refine ⟨8258433970899773736701201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22022490589066063297869869 8258433970899773736701201)
                  ·
                    refine ⟨6193825478174830302525901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8258433970899773736701201 6193825478174830302525901)
                    ·
                      refine ⟨2322684554315561363447213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6193825478174830302525901 2322684554315561363447213)
                      ·
                        rfl

theorem cell23_4523412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_4523412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523412 prefixEnd_4523412 := by exact prefixLift 4523412
  have htrace : WordTrace (prefixWord ++ tailWord_4523412) baseStart_4523412 baseEnd_4523412 := by
    simpa [prefixWord, tailWord_4523412, baseEnd_4523412] using wordTrace_append hprefix tailTrace_4523412
  have hstable : (prefixWord ++ tailWord_4523412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523412).length < 2 ^ (prefixWord ++ tailWord_4523412).sum := by decide
  have hdescent : baseEnd_4523412 < baseStart_4523412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523426 : List Nat := [3, 3, 1, 2, 1, 2, 1, 5, 1, 2, 2]
def baseStart_4523426 : Nat := 118140960795 + 4523426 * 2 ^ 59
def prefixEnd_4523426 : Nat := 4983230072969 + 3 ^ 40 * 4523426 * 2
def baseEnd_4523426 : Nat := 2322691743044724308672149

theorem tailTrace_4523426 : CollatzResearch.WordTrace tailWord_4523426 prefixEnd_4523426 2322691743044724308672149 := by
  unfold tailWord_4523426
  simp only [CollatzResearch.WordTrace]
  refine ⟨41245725027601904125221533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109988600073605077667257421 41245725027601904125221533)
  ·
    refine ⟨15467146885350714046958075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41245725027601904125221533 15467146885350714046958075)
    ·
      refine ⟨23200720328026071070437113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15467146885350714046958075 23200720328026071070437113)
      ·
        refine ⟨17400540246019553302827835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23200720328026071070437113 17400540246019553302827835)
        ·
          refine ⟨26100810369029329954241753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17400540246019553302827835 26100810369029329954241753)
          ·
            refine ⟨19575607776771997465681315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26100810369029329954241753 19575607776771997465681315)
            ·
              refine ⟨29363411665157996198521973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19575607776771997465681315 29363411665157996198521973)
              ·
                refine ⟨2752819843608562143611435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29363411665157996198521973 2752819843608562143611435)
                ·
                  refine ⟨4129229765412843215417153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2752819843608562143611435 4129229765412843215417153)
                  ·
                    refine ⟨3096922324059632411562865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4129229765412843215417153 3096922324059632411562865)
                    ·
                      refine ⟨2322691743044724308672149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3096922324059632411562865 2322691743044724308672149)
                      ·
                        rfl

theorem cell23_4523426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_4523426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523426 prefixEnd_4523426 := by exact prefixLift 4523426
  have htrace : WordTrace (prefixWord ++ tailWord_4523426) baseStart_4523426 baseEnd_4523426 := by
    simpa [prefixWord, tailWord_4523426, baseEnd_4523426] using wordTrace_append hprefix tailTrace_4523426
  have hstable : (prefixWord ++ tailWord_4523426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523426).length < 2 ^ (prefixWord ++ tailWord_4523426).sum := by decide
  have hdescent : baseEnd_4523426 < baseStart_4523426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523442 : List Nat := [3, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3]
def baseStart_4523442 : Nat := 118140960795 + 4523442 * 2 ^ 59
def prefixEnd_4523442 : Nat := 4983230072969 + 3 ^ 40 * 4523442 * 2
def baseEnd_4523442 : Nat := 2322699958735196246072075

theorem tailTrace_4523442 : CollatzResearch.WordTrace tailWord_4523442 prefixEnd_4523442 2322699958735196246072075 := by
  unfold tailWord_4523442
  simp only [CollatzResearch.WordTrace]
  refine ⟨41245870919587412808367145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109988989118899767488979053 41245870919587412808367145)
  ·
    refine ⟨30934403189690559606275359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41245870919587412808367145 30934403189690559606275359)
    ·
      refine ⟨46401604784535839409413039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30934403189690559606275359 46401604784535839409413039)
      ·
        refine ⟨69602407176803759114119559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46401604784535839409413039 69602407176803759114119559)
        ·
          refine ⟨104403610765205638671179339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69602407176803759114119559 104403610765205638671179339)
          ·
            refine ⟨156605416147808458006769009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104403610765205638671179339 156605416147808458006769009)
            ·
              refine ⟨117454062110856343505076757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156605416147808458006769009 117454062110856343505076757)
              ·
                refine ⟨5505659161446391101800473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117454062110856343505076757 5505659161446391101800473)
                ·
                  refine ⟨4129244371084793326350355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5505659161446391101800473 4129244371084793326350355)
                  ·
                    refine ⟨6193866556627189989525533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4129244371084793326350355 6193866556627189989525533)
                    ·
                      refine ⟨2322699958735196246072075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6193866556627189989525533 2322699958735196246072075)
                      ·
                        rfl

theorem cell23_4523442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_4523442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523442 prefixEnd_4523442 := by exact prefixLift 4523442
  have htrace : WordTrace (prefixWord ++ tailWord_4523442) baseStart_4523442 baseEnd_4523442 := by
    simpa [prefixWord, tailWord_4523442, baseEnd_4523442] using wordTrace_append hprefix tailTrace_4523442
  have hstable : (prefixWord ++ tailWord_4523442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523442).length < 2 ^ (prefixWord ++ tailWord_4523442).sum := by decide
  have hdescent : baseEnd_4523442 < baseStart_4523442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523448 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_4523448 : Nat := 118140960795 + 4523448 * 2 ^ 59
def prefixEnd_4523448 : Nat := 4983230072969 + 3 ^ 40 * 4523448 * 2
def baseEnd_4523448 : Nat := 2322703039619123222597047

theorem tailTrace_4523448 : CollatzResearch.WordTrace tailWord_4523448 prefixEnd_4523448 2322703039619123222597047 := by
  unfold tailWord_4523448
  simp only [CollatzResearch.WordTrace]
  refine ⟨82491851258163957129093499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109989135010885276172124665 82491851258163957129093499)
  ·
    refine ⟨123737776887245935693640249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82491851258163957129093499 123737776887245935693640249)
    ·
      refine ⟨92803332665434451770230187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123737776887245935693640249 92803332665434451770230187)
      ·
        refine ⟨139204998998151677655345281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92803332665434451770230187 139204998998151677655345281)
        ·
          refine ⟨104403749248613758241508961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139204998998151677655345281 104403749248613758241508961)
          ·
            refine ⟨78302811936460318681131721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104403749248613758241508961 78302811936460318681131721)
            ·
              refine ⟨58727108952345239010848791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78302811936460318681131721 58727108952345239010848791)
              ·
                refine ⟨88090663428517858516273187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58727108952345239010848791 88090663428517858516273187)
                ·
                  refine ⟨132135995142776787774409781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88090663428517858516273187 132135995142776787774409781)
                  ·
                    refine ⟨12387749544635323853850917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 132135995142776787774409781 12387749544635323853850917)
                    ·
                      refine ⟨2322703039619123222597047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12387749544635323853850917 2322703039619123222597047)
                      ·
                        rfl

theorem cell23_4523448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_4523448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523448 prefixEnd_4523448 := by exact prefixLift 4523448
  have htrace : WordTrace (prefixWord ++ tailWord_4523448) baseStart_4523448 baseEnd_4523448 := by
    simpa [prefixWord, tailWord_4523448, baseEnd_4523448] using wordTrace_append hprefix tailTrace_4523448
  have hstable : (prefixWord ++ tailWord_4523448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523448).length < 2 ^ (prefixWord ++ tailWord_4523448).sum := by decide
  have hdescent : baseEnd_4523448 < baseStart_4523448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523485 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_4523485 : Nat := 118140960795 + 4523485 * 2 ^ 59
def prefixEnd_4523485 : Nat := 4983230072969 + 3 ^ 40 * 4523485 * 2
def baseEnd_4523485 : Nat := 2322722038403339577834377

theorem tailTrace_4523485 : CollatzResearch.WordTrace tailWord_4523485 prefixEnd_4523485 2322722038403339577834377 := by
  unfold tailWord_4523485
  simp only [CollatzResearch.WordTrace]
  refine ⟨164985052017193869577283909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109990034678129246384855939 164985052017193869577283909)
  ·
    refine ⟨30934697253223850545740733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164985052017193869577283909 30934697253223850545740733)
    ·
      refine ⟨11600511469958943954652775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30934697253223850545740733 11600511469958943954652775)
      ·
        refine ⟨17400767204938415931979163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11600511469958943954652775 17400767204938415931979163)
        ·
          refine ⟨26101150807407623897968745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17400767204938415931979163 26101150807407623897968745)
          ·
            refine ⟨19575863105555717923476559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26101150807407623897968745 19575863105555717923476559)
            ·
              refine ⟨29363794658333576885214839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19575863105555717923476559 29363794658333576885214839)
              ·
                refine ⟨44045691987500365327822259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29363794658333576885214839 44045691987500365327822259)
                ·
                  refine ⟨66068537981250547991733389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44045691987500365327822259 66068537981250547991733389)
                  ·
                    refine ⟨24775701742968955496900021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66068537981250547991733389 24775701742968955496900021)
                    ·
                      refine ⟨2322722038403339577834377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24775701742968955496900021 2322722038403339577834377)
                      ·
                        rfl

theorem cell23_4523485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_4523485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523485 prefixEnd_4523485 := by exact prefixLift 4523485
  have htrace : WordTrace (prefixWord ++ tailWord_4523485) baseStart_4523485 baseEnd_4523485 := by
    simpa [prefixWord, tailWord_4523485, baseEnd_4523485] using wordTrace_append hprefix tailTrace_4523485
  have hstable : (prefixWord ++ tailWord_4523485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523485).length < 2 ^ (prefixWord ++ tailWord_4523485).sum := by decide
  have hdescent : baseEnd_4523485 < baseStart_4523485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523505 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 7]
def baseStart_4523505 : Nat := 118140960795 + 4523505 * 2 ^ 59
def prefixEnd_4523505 : Nat := 4983230072969 + 3 ^ 40 * 4523505 * 2
def baseEnd_4523505 : Nat := 258081367557381055509365

theorem tailTrace_4523505 : CollatzResearch.WordTrace tailWord_4523505 prefixEnd_4523505 258081367557381055509365 := by
  unfold tailWord_4523505
  simp only [CollatzResearch.WordTrace]
  refine ⟨164985781477121412993011969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109990520984747608662007979 164985781477121412993011969)
  ·
    refine ⟨123739336107841059744758977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164985781477121412993011969 123739336107841059744758977)
    ·
      refine ⟨92804502080880794808569233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123739336107841059744758977 92804502080880794808569233)
      ·
        refine ⟨69603376560660596106426925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92804502080880794808569233 69603376560660596106426925)
        ·
          refine ⟨26101266210247723539910097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69603376560660596106426925 26101266210247723539910097)
          ·
            refine ⟨19575949657685792654932573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26101266210247723539910097 19575949657685792654932573)
            ·
              refine ⟨7340981121632172245599715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19575949657685792654932573 7340981121632172245599715)
              ·
                refine ⟨11011471682448258368399573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7340981121632172245599715 11011471682448258368399573)
                ·
                  refine ⟨258081367557381055509365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11011471682448258368399573 258081367557381055509365)
                  ·
                    rfl

theorem cell23_4523505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 7].length) (baseStart_4523505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523505 prefixEnd_4523505 := by exact prefixLift 4523505
  have htrace : WordTrace (prefixWord ++ tailWord_4523505) baseStart_4523505 baseEnd_4523505 := by
    simpa [prefixWord, tailWord_4523505, baseEnd_4523505] using wordTrace_append hprefix tailTrace_4523505
  have hstable : (prefixWord ++ tailWord_4523505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523505).length < 2 ^ (prefixWord ++ tailWord_4523505).sum := by decide
  have hdescent : baseEnd_4523505 < baseStart_4523505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523516 : List Nat := [2, 2, 2, 1, 2, 1, 6, 1, 2, 2, 2]
def baseStart_4523516 : Nat := 118140960795 + 4523516 * 2 ^ 59
def prefixEnd_4523516 : Nat := 4983230072969 + 3 ^ 40 * 4523516 * 2
def baseEnd_4523516 : Nat := 2322737956303628956546735

theorem tailTrace_4523516 : CollatzResearch.WordTrace tailWord_4523516 prefixEnd_4523516 2322737956303628956546735 := by
  unfold tailWord_4523516
  simp only [CollatzResearch.WordTrace]
  refine ⟨82493091340040780935831201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109990788453387707914441601 82493091340040780935831201)
  ·
    refine ⟨61869818505030585701873401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82493091340040780935831201 61869818505030585701873401)
    ·
      refine ⟨46402363878772939276405051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61869818505030585701873401 46402363878772939276405051)
      ·
        refine ⟨69603545818159408914607577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46402363878772939276405051 69603545818159408914607577)
        ·
          refine ⟨52202659363619556685955683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69603545818159408914607577 52202659363619556685955683)
          ·
            refine ⟨78303989045429335028933525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52202659363619556685955683 78303989045429335028933525)
            ·
              refine ⟨3670499486504500079481259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78303989045429335028933525 3670499486504500079481259)
              ·
                refine ⟨5505749229756750119221889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3670499486504500079481259 5505749229756750119221889)
                ·
                  refine ⟨4129311922317562589416417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5505749229756750119221889 4129311922317562589416417)
                  ·
                    refine ⟨3096983941738171942062313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4129311922317562589416417 3096983941738171942062313)
                    ·
                      refine ⟨2322737956303628956546735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3096983941738171942062313 2322737956303628956546735)
                      ·
                        rfl

theorem cell23_4523516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_4523516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523516 prefixEnd_4523516 := by exact prefixLift 4523516
  have htrace : WordTrace (prefixWord ++ tailWord_4523516) baseStart_4523516 baseEnd_4523516 := by
    simpa [prefixWord, tailWord_4523516, baseEnd_4523516] using wordTrace_append hprefix tailTrace_4523516
  have hstable : (prefixWord ++ tailWord_4523516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523516).length < 2 ^ (prefixWord ++ tailWord_4523516).sum := by decide
  have hdescent : baseEnd_4523516 < baseStart_4523516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523533 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_4523533 : Nat := 118140960795 + 4523533 * 2 ^ 59
def prefixEnd_4523533 : Nat := 4983230072969 + 3 ^ 40 * 4523533 * 2
def baseEnd_4523533 : Nat := 2322746685474755390034157

theorem tailTrace_4523533 : CollatzResearch.WordTrace tailWord_4523533 prefixEnd_4523533 2322746685474755390034157 := by
  unfold tailWord_4523533
  simp only [CollatzResearch.WordTrace]
  refine ⟨164986802721019973775031253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109991201814013315850020835 164986802721019973775031253)
  ·
    refine ⟨3866878188773905635352295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 164986802721019973775031253 3866878188773905635352295)
    ·
      refine ⟨5800317283160858453028443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3866878188773905635352295 5800317283160858453028443)
      ·
        refine ⟨8700475924741287679542665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5800317283160858453028443 8700475924741287679542665)
        ·
          refine ⟨6525356943555965759656999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8700475924741287679542665 6525356943555965759656999)
          ·
            refine ⟨9788035415333948639485499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6525356943555965759656999 9788035415333948639485499)
            ·
              refine ⟨14682053123000922959228249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9788035415333948639485499 14682053123000922959228249)
              ·
                refine ⟨11011539842250692219421187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14682053123000922959228249 11011539842250692219421187)
                ·
                  refine ⟨16517309763376038329131781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11011539842250692219421187 16517309763376038329131781)
                  ·
                    refine ⟨3096995580633007186712209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16517309763376038329131781 3096995580633007186712209)
                    ·
                      refine ⟨2322746685474755390034157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3096995580633007186712209 2322746685474755390034157)
                      ·
                        rfl

theorem cell23_4523533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_4523533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523533 prefixEnd_4523533 := by exact prefixLift 4523533
  have htrace : WordTrace (prefixWord ++ tailWord_4523533) baseStart_4523533 baseEnd_4523533 := by
    simpa [prefixWord, tailWord_4523533, baseEnd_4523533] using wordTrace_append hprefix tailTrace_4523533
  have hstable : (prefixWord ++ tailWord_4523533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523533).length < 2 ^ (prefixWord ++ tailWord_4523533).sum := by decide
  have hdescent : baseEnd_4523533 < baseStart_4523533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523552 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 2, 5]
def baseStart_4523552 : Nat := 118140960795 + 4523552 * 2 ^ 59
def prefixEnd_4523552 : Nat := 4983230072969 + 3 ^ 40 * 4523552 * 2
def baseEnd_4523552 : Nat := 774252147202396938565523

theorem tailTrace_4523552 : CollatzResearch.WordTrace tailWord_4523552 prefixEnd_4523552 774252147202396938565523 := by
  unfold tailWord_4523552
  simp only [CollatzResearch.WordTrace]
  refine ⟨82493747853975570009986455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109991663805300760013315273 82493747853975570009986455)
  ·
    refine ⟨123740621780963355014979683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82493747853975570009986455 123740621780963355014979683)
    ·
      refine ⟨185610932671445032522469525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123740621780963355014979683 185610932671445032522469525)
      ·
        refine ⟨8700512468973985899490759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 185610932671445032522469525 8700512468973985899490759)
        ·
          refine ⟨13050768703460978849236139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8700512468973985899490759 13050768703460978849236139)
          ·
            refine ⟨19576153055191468273854209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13050768703460978849236139 19576153055191468273854209)
            ·
              refine ⟨14682114791393601205390657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19576153055191468273854209 14682114791393601205390657)
              ·
                refine ⟨11011586093545200904042993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14682114791393601205390657 11011586093545200904042993)
                ·
                  refine ⟨8258689570158900678032245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11011586093545200904042993 8258689570158900678032245)
                  ·
                    refine ⟨774252147202396938565523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8258689570158900678032245 774252147202396938565523)
                    ·
                      rfl

theorem cell23_4523552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 2, 5].length) (baseStart_4523552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523552 prefixEnd_4523552 := by exact prefixLift 4523552
  have htrace : WordTrace (prefixWord ++ tailWord_4523552) baseStart_4523552 baseEnd_4523552 := by
    simpa [prefixWord, tailWord_4523552, baseEnd_4523552] using wordTrace_append hprefix tailTrace_4523552
  have hstable : (prefixWord ++ tailWord_4523552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523552).length < 2 ^ (prefixWord ++ tailWord_4523552).sum := by decide
  have hdescent : baseEnd_4523552 < baseStart_4523552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523612 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 8]
def baseStart_4523612 : Nat := 118140960795 + 4523612 * 2 ^ 59
def prefixEnd_4523612 : Nat := 4983230072969 + 3 ^ 40 * 4523612 * 2
def baseEnd_4523612 : Nat := 258087472271828953438477

theorem tailTrace_4523612 : CollatzResearch.WordTrace tailWord_4523612 prefixEnd_4523612 258087472271828953438477 := by
  unfold tailWord_4523612
  simp only [CollatzResearch.WordTrace]
  refine ⟨82494842043866885133578545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109993122725155846844771393 82494842043866885133578545)
  ·
    refine ⟨61871131532900163850183909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82494842043866885133578545 61871131532900163850183909)
    ·
      refine ⟨11600837162418780721909483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61871131532900163850183909 11600837162418780721909483)
      ·
        refine ⟨17401255743628171082864225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11600837162418780721909483 17401255743628171082864225)
        ·
          refine ⟨13050941807721128312148169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17401255743628171082864225 13050941807721128312148169)
          ·
            refine ⟨9788206355790846234111127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13050941807721128312148169 9788206355790846234111127)
            ·
              refine ⟨14682309533686269351166691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9788206355790846234111127 14682309533686269351166691)
              ·
                refine ⟨22023464300529404026750037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14682309533686269351166691 22023464300529404026750037)
                ·
                  refine ⟨258087472271828953438477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22023464300529404026750037 258087472271828953438477)
                  ·
                    rfl

theorem cell23_4523612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_4523612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523612 prefixEnd_4523612 := by exact prefixLift 4523612
  have htrace : WordTrace (prefixWord ++ tailWord_4523612) baseStart_4523612 baseEnd_4523612 := by
    simpa [prefixWord, tailWord_4523612, baseEnd_4523612] using wordTrace_append hprefix tailTrace_4523612
  have hstable : (prefixWord ++ tailWord_4523612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523612).length < 2 ^ (prefixWord ++ tailWord_4523612).sum := by decide
  have hdescent : baseEnd_4523612 < baseStart_4523612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523625 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 5, 5]
def baseStart_4523625 : Nat := 118140960795 + 4523625 * 2 ^ 59
def prefixEnd_4523625 : Nat := 4983230072969 + 3 ^ 40 * 4523625 * 2
def baseEnd_4523625 : Nat := 774264641898323010027911

theorem tailTrace_4523625 : CollatzResearch.WordTrace tailWord_4523625 prefixEnd_4523625 774264641898323010027911 := by
  unfold tailWord_4523625
  simp only [CollatzResearch.WordTrace]
  refine ⟨164990158236686673487380329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109993438824457782324920219 164990158236686673487380329)
  ·
    refine ⟨123742618677515005115535247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164990158236686673487380329 123742618677515005115535247)
    ·
      refine ⟨185613928016272507673302871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123742618677515005115535247 185613928016272507673302871)
      ·
        refine ⟨278420892024408761509954307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185613928016272507673302871 278420892024408761509954307)
        ·
          refine ⟨417631338036613142264931461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278420892024408761509954307 417631338036613142264931461)
          ·
            refine ⟨78305875881864964174674649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 417631338036613142264931461 78305875881864964174674649)
            ·
              refine ⟨58729406911398723131005987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78305875881864964174674649 58729406911398723131005987)
              ·
                refine ⟨88094110367098084696508981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58729406911398723131005987 88094110367098084696508981)
                ·
                  refine ⟨8258822846915445440297717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88094110367098084696508981 8258822846915445440297717)
                  ·
                    refine ⟨774264641898323010027911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8258822846915445440297717 774264641898323010027911)
                    ·
                      rfl

theorem cell23_4523625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 5].length) (baseStart_4523625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523625 prefixEnd_4523625 := by exact prefixLift 4523625
  have htrace : WordTrace (prefixWord ++ tailWord_4523625) baseStart_4523625 baseEnd_4523625 := by
    simpa [prefixWord, tailWord_4523625, baseEnd_4523625] using wordTrace_append hprefix tailTrace_4523625
  have hstable : (prefixWord ++ tailWord_4523625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523625).length < 2 ^ (prefixWord ++ tailWord_4523625).sum := by decide
  have hdescent : baseEnd_4523625 < baseStart_4523625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523649 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_4523649 : Nat := 118140960795 + 4523649 * 2 ^ 59
def prefixEnd_4523649 : Nat := 4983230072969 + 3 ^ 40 * 4523649 * 2
def baseEnd_4523649 : Nat := 2322806249230676936183623

theorem tailTrace_4523649 : CollatzResearch.WordTrace tailWord_4523649 prefixEnd_4523649 2322806249230676936183623 := by
  unfold tailWord_4523649
  simp only [CollatzResearch.WordTrace]
  refine ⟨164991033588599725586254001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109994022392399817057502667 164991033588599725586254001)
  ·
    refine ⟨123743275191449794189690501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164991033588599725586254001 123743275191449794189690501)
    ·
      refine ⟨23201864098396836410566969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123743275191449794189690501 23201864098396836410566969)
      ·
        refine ⟨17401398073797627307925227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23201864098396836410566969 17401398073797627307925227)
        ·
          refine ⟨26102097110696440961887841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17401398073797627307925227 26102097110696440961887841)
          ·
            refine ⟨19576572833022330721415881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26102097110696440961887841 19576572833022330721415881)
            ·
              refine ⟨14682429624766748041061911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19576572833022330721415881 14682429624766748041061911)
              ·
                refine ⟨22023644437150122061592867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14682429624766748041061911 22023644437150122061592867)
                ·
                  refine ⟨33035466655725183092389301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22023644437150122061592867 33035466655725183092389301)
                  ·
                    refine ⟨3097074998974235914911497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33035466655725183092389301 3097074998974235914911497)
                    ·
                      refine ⟨2322806249230676936183623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097074998974235914911497 2322806249230676936183623)
                      ·
                        rfl

theorem cell23_4523649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_4523649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523649 prefixEnd_4523649 := by exact prefixLift 4523649
  have htrace : WordTrace (prefixWord ++ tailWord_4523649) baseStart_4523649 baseEnd_4523649 := by
    simpa [prefixWord, tailWord_4523649, baseEnd_4523649] using wordTrace_append hprefix tailTrace_4523649
  have hstable : (prefixWord ++ tailWord_4523649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523649).length < 2 ^ (prefixWord ++ tailWord_4523649).sum := by decide
  have hdescent : baseEnd_4523649 < baseStart_4523649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523685 : List Nat := [1, 3, 1, 2, 1, 2, 3, 10]
def baseStart_4523685 : Nat := 118140960795 + 4523685 * 2 ^ 59
def prefixEnd_4523685 : Nat := 4983230072969 + 3 ^ 40 * 4523685 * 2
def baseEnd_4523685 : Nat := 86030545723490325753091

theorem tailTrace_4523685 : CollatzResearch.WordTrace tailWord_4523685 prefixEnd_4523685 86030545723490325753091 := by
  unfold tailWord_4523685
  simp only [CollatzResearch.WordTrace]
  refine ⟨164992346616469303734564509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109994897744312869156376339 164992346616469303734564509)
  ·
    refine ⟨61872129981175988900461691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164992346616469303734564509 61872129981175988900461691)
    ·
      refine ⟨92808194971763983350692537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61872129981175988900461691 92808194971763983350692537)
      ·
        refine ⟨69606146228822987513019403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92808194971763983350692537 69606146228822987513019403)
        ·
          refine ⟨104409219343234481269529105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69606146228822987513019403 104409219343234481269529105)
          ·
            refine ⟨78306914507425860952146829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104409219343234481269529105 78306914507425860952146829)
            ·
              refine ⟨29365092940284697857055061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78306914507425860952146829 29365092940284697857055061)
              ·
                refine ⟨86030545723490325753091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29365092940284697857055061 86030545723490325753091)
                ·
                  rfl

theorem cell23_4523685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 10].length) (baseStart_4523685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523685 prefixEnd_4523685 := by exact prefixLift 4523685
  have htrace : WordTrace (prefixWord ++ tailWord_4523685) baseStart_4523685 baseEnd_4523685 := by
    simpa [prefixWord, tailWord_4523685, baseEnd_4523685] using wordTrace_append hprefix tailTrace_4523685
  have hstable : (prefixWord ++ tailWord_4523685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523685).length < 2 ^ (prefixWord ++ tailWord_4523685).sum := by decide
  have hdescent : baseEnd_4523685 < baseStart_4523685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523715 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 6, 7]
def baseStart_4523715 : Nat := 118140960795 + 4523715 * 2 ^ 59
def prefixEnd_4523715 : Nat := 4983230072969 + 3 ^ 40 * 4523715 * 2
def baseEnd_4523715 : Nat := 774280046317957892652773

theorem tailTrace_4523715 : CollatzResearch.WordTrace tailWord_4523715 prefixEnd_4523715 774280046317957892652773 := by
  unfold tailWord_4523715
  simp only [CollatzResearch.WordTrace]
  refine ⟨164993440806360618858156599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109995627204240412572104399 164993440806360618858156599)
  ·
    refine ⟨247490161209540928287234899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164993440806360618858156599 247490161209540928287234899)
    ·
      refine ⟨371235241814311392430852349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247490161209540928287234899 371235241814311392430852349)
      ·
        refine ⟨139213215680366772161569631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 371235241814311392430852349 139213215680366772161569631)
        ·
          refine ⟨208819823520550158242354447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139213215680366772161569631 208819823520550158242354447)
          ·
            refine ⟨313229735280825237363531671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208819823520550158242354447 313229735280825237363531671)
            ·
              refine ⟨469844602921237856045297507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313229735280825237363531671 469844602921237856045297507)
              ·
                refine ⟨704766904381856784067946261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469844602921237856045297507 704766904381856784067946261)
                ·
                  refine ⟨33035948642899536753184981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 704766904381856784067946261 33035948642899536753184981)
                  ·
                    refine ⟨774280046317957892652773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33035948642899536753184981 774280046317957892652773)
                    ·
                      rfl

theorem cell23_4523715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 7].length) (baseStart_4523715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523715 prefixEnd_4523715 := by exact prefixLift 4523715
  have htrace : WordTrace (prefixWord ++ tailWord_4523715) baseStart_4523715 baseEnd_4523715 := by
    simpa [prefixWord, tailWord_4523715, baseEnd_4523715] using wordTrace_append hprefix tailTrace_4523715
  have hstable : (prefixWord ++ tailWord_4523715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523715).length < 2 ^ (prefixWord ++ tailWord_4523715).sum := by decide
  have hdescent : baseEnd_4523715 < baseStart_4523715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523730 : List Nat := [3, 2, 2, 2, 2, 2, 1, 4, 1, 2, 2]
def baseStart_4523730 : Nat := 118140960795 + 4523730 * 2 ^ 59
def prefixEnd_4523730 : Nat := 4983230072969 + 3 ^ 40 * 4523730 * 2
def baseEnd_4523730 : Nat := 2322847841163691119270751

theorem tailTrace_4523730 : CollatzResearch.WordTrace tailWord_4523730 prefixEnd_4523730 2322847841163691119270751 := by
  unfold tailWord_4523730
  simp only [CollatzResearch.WordTrace]
  refine ⟨41248496975326569104988161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109995991934204184279968429 41248496975326569104988161)
  ·
    refine ⟨30936372731494926828741121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41248496975326569104988161 30936372731494926828741121)
    ·
      refine ⟨23202279548621195121555841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30936372731494926828741121 23202279548621195121555841)
      ·
        refine ⟨17401709661465896341166881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23202279548621195121555841 17401709661465896341166881)
        ·
          refine ⟨13051282246099422255875161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17401709661465896341166881 13051282246099422255875161)
          ·
            refine ⟨9788461684574566691906371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13051282246099422255875161 9788461684574566691906371)
            ·
              refine ⟨14682692526861850037859557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9788461684574566691906371 14682692526861850037859557)
              ·
                refine ⟨2753004848786596882098667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14682692526861850037859557 2753004848786596882098667)
                ·
                  refine ⟨4129507273179895323148001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2753004848786596882098667 4129507273179895323148001)
                  ·
                    refine ⟨3097130454884921492361001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4129507273179895323148001 3097130454884921492361001)
                    ·
                      refine ⟨2322847841163691119270751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097130454884921492361001 2322847841163691119270751)
                      ·
                        rfl

theorem cell23_4523730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_4523730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523730 prefixEnd_4523730 := by exact prefixLift 4523730
  have htrace : WordTrace (prefixWord ++ tailWord_4523730) baseStart_4523730 baseEnd_4523730 := by
    simpa [prefixWord, tailWord_4523730, baseEnd_4523730] using wordTrace_append hprefix tailTrace_4523730
  have hstable : (prefixWord ++ tailWord_4523730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523730).length < 2 ^ (prefixWord ++ tailWord_4523730).sum := by decide
  have hdescent : baseEnd_4523730 < baseStart_4523730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523762 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_4523762 : Nat := 118140960795 + 4523762 * 2 ^ 59
def prefixEnd_4523762 : Nat := 4983230072969 + 3 ^ 40 * 4523762 * 2
def baseEnd_4523762 : Nat := 774288090848211664690201

theorem tailTrace_4523762 : CollatzResearch.WordTrace tailWord_4523762 prefixEnd_4523762 774288090848211664690201 := by
  unfold tailWord_4523762
  simp only [CollatzResearch.WordTrace]
  refine ⟨41248788759297586471279385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109996770024793563923411693 41248788759297586471279385)
  ·
    refine ⟨30936591569473189853459539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41248788759297586471279385 30936591569473189853459539)
    ·
      refine ⟨46404887354209784780189309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30936591569473189853459539 46404887354209784780189309)
      ·
        refine ⟨17401832757828669292570991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46404887354209784780189309 17401832757828669292570991)
        ·
          refine ⟨26102749136743003938856487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17401832757828669292570991 26102749136743003938856487)
          ·
            refine ⟨39154123705114505908284731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26102749136743003938856487 39154123705114505908284731)
            ·
              refine ⟨58731185557671758862427097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39154123705114505908284731 58731185557671758862427097)
              ·
                refine ⟨44048389168253819146820323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58731185557671758862427097 44048389168253819146820323)
                ·
                  refine ⟨66072583752380728720230485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44048389168253819146820323 66072583752380728720230485)
                  ·
                    refine ⟨774288090848211664690201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66072583752380728720230485 774288090848211664690201)
                    ·
                      rfl

theorem cell23_4523762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_4523762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523762 prefixEnd_4523762 := by exact prefixLift 4523762
  have htrace : WordTrace (prefixWord ++ tailWord_4523762) baseStart_4523762 baseEnd_4523762 := by
    simpa [prefixWord, tailWord_4523762, baseEnd_4523762] using wordTrace_append hprefix tailTrace_4523762
  have hstable : (prefixWord ++ tailWord_4523762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523762).length < 2 ^ (prefixWord ++ tailWord_4523762).sum := by decide
  have hdescent : baseEnd_4523762 < baseStart_4523762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523764 : List Nat := [2, 6, 1, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_4523764 : Nat := 118140960795 + 4523764 * 2 ^ 59
def prefixEnd_4523764 : Nat := 4983230072969 + 3 ^ 40 * 4523764 * 2
def baseEnd_4523764 : Nat := 2322865299505943986245595

theorem tailTrace_4523764 : CollatzResearch.WordTrace tailWord_4523764 prefixEnd_4523764 2322865299505943986245595 := by
  unfold tailWord_4523764
  simp only [CollatzResearch.WordTrace]
  refine ⟨82497613991591550113345173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109996818655455400151126897 82497613991591550113345173)
  ·
    refine ⟨3867075655855853911563055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82497613991591550113345173 3867075655855853911563055)
    ·
      refine ⟨5800613483783780867344583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3867075655855853911563055 5800613483783780867344583)
      ·
        refine ⟨8700920225675671301016875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5800613483783780867344583 8700920225675671301016875)
        ·
          refine ⟨13051380338513506951525313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8700920225675671301016875 13051380338513506951525313)
          ·
            refine ⟨9788535253885130213643985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13051380338513506951525313 9788535253885130213643985)
            ·
              refine ⟨7341401440413847660232989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9788535253885130213643985 7341401440413847660232989)
              ·
                refine ⟨2753025540155192872587371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7341401440413847660232989 2753025540155192872587371)
                ·
                  refine ⟨4129538310232789308881057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2753025540155192872587371 4129538310232789308881057)
                  ·
                    refine ⟨3097153732674591981660793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4129538310232789308881057 3097153732674591981660793)
                    ·
                      refine ⟨2322865299505943986245595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097153732674591981660793 2322865299505943986245595)
                      ·
                        rfl

theorem cell23_4523764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_4523764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523764 prefixEnd_4523764 := by exact prefixLift 4523764
  have htrace : WordTrace (prefixWord ++ tailWord_4523764) baseStart_4523764 baseEnd_4523764 := by
    simpa [prefixWord, tailWord_4523764, baseEnd_4523764] using wordTrace_append hprefix tailTrace_4523764
  have hstable : (prefixWord ++ tailWord_4523764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523764).length < 2 ^ (prefixWord ++ tailWord_4523764).sum := by decide
  have hdescent : baseEnd_4523764 < baseStart_4523764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523772 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_4523772 : Nat := 118140960795 + 4523772 * 2 ^ 59
def prefixEnd_4523772 : Nat := 4983230072969 + 3 ^ 40 * 4523772 * 2
def baseEnd_4523772 : Nat := 2322869407351179954945557

theorem tailTrace_4523772 : CollatzResearch.WordTrace tailWord_4523772 prefixEnd_4523772 2322869407351179954945557 := by
  unfold tailWord_4523772
  simp only [CollatzResearch.WordTrace]
  refine ⟨82497759883577058796490785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109997013178102745061987713 82497759883577058796490785)
  ·
    refine ⟨61873319912682794097368089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82497759883577058796490785 61873319912682794097368089)
    ·
      refine ⟨46404989934512095573026067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61873319912682794097368089 46404989934512095573026067)
      ·
        refine ⟨69607484901768143359539101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46404989934512095573026067 69607484901768143359539101)
        ·
          refine ⟨26102806838163053759827163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69607484901768143359539101 26102806838163053759827163)
          ·
            refine ⟨39154210257244580639740745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26102806838163053759827163 39154210257244580639740745)
            ·
              refine ⟨29365657692933435479805559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39154210257244580639740745 29365657692933435479805559)
              ·
                refine ⟨44048486539400153219708339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29365657692933435479805559 44048486539400153219708339)
                ·
                  refine ⟨66072729809100229829562509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44048486539400153219708339 66072729809100229829562509)
                  ·
                    refine ⟨24777273678412586186085941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66072729809100229829562509 24777273678412586186085941)
                    ·
                      refine ⟨2322869407351179954945557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24777273678412586186085941 2322869407351179954945557)
                      ·
                        rfl

theorem cell23_4523772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_4523772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523772 prefixEnd_4523772 := by exact prefixLift 4523772
  have htrace : WordTrace (prefixWord ++ tailWord_4523772) baseStart_4523772 baseEnd_4523772 := by
    simpa [prefixWord, tailWord_4523772, baseEnd_4523772] using wordTrace_append hprefix tailTrace_4523772
  have hstable : (prefixWord ++ tailWord_4523772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523772).length < 2 ^ (prefixWord ++ tailWord_4523772).sum := by decide
  have hdescent : baseEnd_4523772 < baseStart_4523772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523799 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_4523799 : Nat := 118140960795 + 4523799 * 2 ^ 59
def prefixEnd_4523799 : Nat := 4983230072969 + 3 ^ 40 * 4523799 * 2
def baseEnd_4523799 : Nat := 2322883271328851349307933

theorem tailTrace_4523799 : CollatzResearch.WordTrace tailWord_4523799 prefixEnd_4523799 2322883271328851349307933 := by
  unfold tailWord_4523799
  simp only [CollatzResearch.WordTrace]
  refine ⟨164996504538056301204214451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109997669692037534136142967 164996504538056301204214451)
  ·
    refine ⟨247494756807084451806321677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164996504538056301204214451 247494756807084451806321677)
    ·
      refine ⟨92810533802656669427370629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247494756807084451806321677 92810533802656669427370629)
      ·
        refine ⟨17401975087998125517631993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92810533802656669427370629 17401975087998125517631993)
        ·
          refine ⟨13051481315998594138223995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17401975087998125517631993 13051481315998594138223995)
          ·
            refine ⟨19577221973997891207335993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13051481315998594138223995 19577221973997891207335993)
            ·
              refine ⟨14682916480498418405501995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19577221973997891207335993 14682916480498418405501995)
              ·
                refine ⟨22024374720747627608252993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14682916480498418405501995 22024374720747627608252993)
                ·
                  refine ⟨16518281040560720706189745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22024374720747627608252993 16518281040560720706189745)
                  ·
                    refine ⟨12388710780420540529642309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16518281040560720706189745 12388710780420540529642309)
                    ·
                      refine ⟨2322883271328851349307933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12388710780420540529642309 2322883271328851349307933)
                      ·
                        rfl

theorem cell23_4523799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_4523799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523799 prefixEnd_4523799 := by exact prefixLift 4523799
  have htrace : WordTrace (prefixWord ++ tailWord_4523799) baseStart_4523799 baseEnd_4523799 := by
    simpa [prefixWord, tailWord_4523799, baseEnd_4523799] using wordTrace_append hprefix tailTrace_4523799
  have hstable : (prefixWord ++ tailWord_4523799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523799).length < 2 ^ (prefixWord ++ tailWord_4523799).sum := by decide
  have hdescent : baseEnd_4523799 < baseStart_4523799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523826 : List Nat := [3, 2, 1, 1, 3, 2, 3, 3, 5]
def baseStart_4523826 : Nat := 118140960795 + 4523826 * 2 ^ 59
def prefixEnd_4523826 : Nat := 4983230072969 + 3 ^ 40 * 4523826 * 2
def baseEnd_4523826 : Nat := 258099681700724749296701

theorem tailTrace_4523826 : CollatzResearch.WordTrace tailWord_4523826 prefixEnd_4523826 258099681700724749296701 := by
  unfold tailWord_4523826
  simp only [CollatzResearch.WordTrace]
  refine ⟨41249372327239621203861833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109998326205972323210298221 41249372327239621203861833)
  ·
    refine ⟨30937029245429715902896375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41249372327239621203861833 30937029245429715902896375)
    ·
      refine ⟨46405543868144573854344563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30937029245429715902896375 46405543868144573854344563)
      ·
        refine ⟨69608315802216860781516845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46405543868144573854344563 69608315802216860781516845)
        ·
          refine ⟨26103118425831322793068817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69608315802216860781516845 26103118425831322793068817)
          ·
            refine ⟨19577338819373492094801613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26103118425831322793068817 19577338819373492094801613)
            ·
              refine ⟨7341502057265059535550605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19577338819373492094801613 7341502057265059535550605)
              ·
                refine ⟨2753063271474397325831477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7341502057265059535550605 2753063271474397325831477)
                ·
                  refine ⟨258099681700724749296701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2753063271474397325831477 258099681700724749296701)
                  ·
                    rfl

theorem cell23_4523826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_4523826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523826 prefixEnd_4523826 := by exact prefixLift 4523826
  have htrace : WordTrace (prefixWord ++ tailWord_4523826) baseStart_4523826 baseEnd_4523826 := by
    simpa [prefixWord, tailWord_4523826, baseEnd_4523826] using wordTrace_append hprefix tailTrace_4523826
  have hstable : (prefixWord ++ tailWord_4523826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523826).length < 2 ^ (prefixWord ++ tailWord_4523826).sum := by decide
  have hdescent : baseEnd_4523826 < baseStart_4523826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523929 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 3, 5]
def baseStart_4523929 : Nat := 118140960795 + 4523929 * 2 ^ 59
def prefixEnd_4523929 : Nat := 4983230072969 + 3 ^ 40 * 4523929 * 2
def baseEnd_4523929 : Nat := 774316674604645280227445

theorem tailTrace_4523929 : CollatzResearch.WordTrace tailWord_4523929 prefixEnd_4523929 774316674604645280227445 := by
  unfold tailWord_4523929
  simp only [CollatzResearch.WordTrace]
  refine ⟨165001246027585333406446841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110000830685056888937631227 165001246027585333406446841)
  ·
    refine ⟨123750934520689000054835131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165001246027585333406446841 123750934520689000054835131)
    ·
      refine ⟨185626401781033500082252697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123750934520689000054835131 185626401781033500082252697)
      ·
        refine ⟨139219801335775125061689523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185626401781033500082252697 139219801335775125061689523)
        ·
          refine ⟨208829702003662687592534285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139219801335775125061689523 208829702003662687592534285)
          ·
            refine ⟨78311138251373507847200357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208829702003662687592534285 78311138251373507847200357)
            ·
              refine ⟨14683338422132532721350067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78311138251373507847200357 14683338422132532721350067)
              ·
                refine ⟨22025007633198799082025101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14683338422132532721350067 22025007633198799082025101)
                ·
                  refine ⟨8259377862449549655759413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22025007633198799082025101 8259377862449549655759413)
                  ·
                    refine ⟨774316674604645280227445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8259377862449549655759413 774316674604645280227445)
                    ·
                      rfl

theorem cell23_4523929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 5].length) (baseStart_4523929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523929 prefixEnd_4523929 := by exact prefixLift 4523929
  have htrace : WordTrace (prefixWord ++ tailWord_4523929) baseStart_4523929 baseEnd_4523929 := by
    simpa [prefixWord, tailWord_4523929, baseEnd_4523929] using wordTrace_append hprefix tailTrace_4523929
  have hstable : (prefixWord ++ tailWord_4523929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523929).length < 2 ^ (prefixWord ++ tailWord_4523929).sum := by decide
  have hdescent : baseEnd_4523929 < baseStart_4523929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523950 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 8]
def baseStart_4523950 : Nat := 118140960795 + 4523950 * 2 ^ 59
def prefixEnd_4523950 : Nat := 4983230072969 + 3 ^ 40 * 4523950 * 2
def baseEnd_4523950 : Nat := 258106756323075584279971

theorem tailTrace_4523950 : CollatzResearch.WordTrace tailWord_4523950 prefixEnd_4523950 258106756323075584279971 := by
  unfold tailWord_4523950
  simp only [CollatzResearch.WordTrace]
  refine ⟨20625251495063656749120163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110001341307006169328640869 20625251495063656749120163)
  ·
    refine ⟨30937877242595485123680245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20625251495063656749120163 30937877242595485123680245)
    ·
      refine ⟨2900425991493326730345023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30937877242595485123680245 2900425991493326730345023)
      ·
        refine ⟨4350638987239990095517535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2900425991493326730345023 4350638987239990095517535)
        ·
          refine ⟨6525958480859985143276303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4350638987239990095517535 6525958480859985143276303)
          ·
            refine ⟨9788937721289977714914455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6525958480859985143276303 9788937721289977714914455)
            ·
              refine ⟨14683406581934966572371683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9788937721289977714914455 14683406581934966572371683)
              ·
                refine ⟨22025109872902449858557525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14683406581934966572371683 22025109872902449858557525)
                ·
                  refine ⟨258106756323075584279971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22025109872902449858557525 258106756323075584279971)
                  ·
                    rfl

theorem cell23_4523950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_4523950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523950 prefixEnd_4523950 := by exact prefixLift 4523950
  have htrace : WordTrace (prefixWord ++ tailWord_4523950) baseStart_4523950 baseEnd_4523950 := by
    simpa [prefixWord, tailWord_4523950, baseEnd_4523950] using wordTrace_append hprefix tailTrace_4523950
  have hstable : (prefixWord ++ tailWord_4523950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523950).length < 2 ^ (prefixWord ++ tailWord_4523950).sum := by decide
  have hdescent : baseEnd_4523950 < baseStart_4523950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523976 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 1, 6]
def baseStart_4523976 : Nat := 118140960795 + 4523976 * 2 ^ 59
def prefixEnd_4523976 : Nat := 4983230072969 + 3 ^ 40 * 4523976 * 2
def baseEnd_4523976 : Nat := 774324719134899052264873

theorem tailTrace_4523976 : CollatzResearch.WordTrace tailWord_4523976 prefixEnd_4523976 774324719134899052264873 := by
  unfold tailWord_4523976
  simp only [CollatzResearch.WordTrace]
  refine ⟨82501480129207530216703891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110001973505610040288938521 82501480129207530216703891)
  ·
    refine ⟨123752220193811295325055837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82501480129207530216703891 123752220193811295325055837)
    ·
      refine ⟨46407082572679235746895939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123752220193811295325055837 46407082572679235746895939)
      ·
        refine ⟨69610623859018853620343909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46407082572679235746895939 69610623859018853620343909)
        ·
          refine ⟨13051991973566035053814483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69610623859018853620343909 13051991973566035053814483)
          ·
            refine ⟨19577987960349052580721725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13051991973566035053814483 19577987960349052580721725)
            ·
              refine ⟨7341745485130894717770647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19577987960349052580721725 7341745485130894717770647)
              ·
                refine ⟨11012618227696342076655971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7341745485130894717770647 11012618227696342076655971)
                ·
                  refine ⟨16518927341544513114983957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11012618227696342076655971 16518927341544513114983957)
                  ·
                    refine ⟨774324719134899052264873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16518927341544513114983957 774324719134899052264873)
                    ·
                      rfl

theorem cell23_4523976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_4523976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523976 prefixEnd_4523976 := by exact prefixLift 4523976
  have htrace : WordTrace (prefixWord ++ tailWord_4523976) baseStart_4523976 baseEnd_4523976 := by
    simpa [prefixWord, tailWord_4523976, baseEnd_4523976] using wordTrace_append hprefix tailTrace_4523976
  have hstable : (prefixWord ++ tailWord_4523976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523976).length < 2 ^ (prefixWord ++ tailWord_4523976).sum := by decide
  have hdescent : baseEnd_4523976 < baseStart_4523976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523979 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 6]
def baseStart_4523979 : Nat := 118140960795 + 4523979 * 2 ^ 59
def prefixEnd_4523979 : Nat := 4983230072969 + 3 ^ 40 * 4523979 * 2
def baseEnd_4523979 : Nat := 2322975697846660645057105

theorem tailTrace_4523979 : CollatzResearch.WordTrace tailWord_4523979 prefixEnd_4523979 2322975697846660645057105 := by
  unfold tailWord_4523979
  simp only [CollatzResearch.WordTrace]
  refine ⟨165003069677404191945766991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110002046451602794630511327 165003069677404191945766991)
  ·
    refine ⟨247504604516106287918650487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165003069677404191945766991 247504604516106287918650487)
    ·
      refine ⟨371256906774159431877975731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247504604516106287918650487 371256906774159431877975731)
      ·
        refine ⟨556885360161239147816963597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371256906774159431877975731 556885360161239147816963597)
        ·
          refine ⟨208832010060464680431361349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 556885360161239147816963597 208832010060464680431361349)
          ·
            refine ⟨39156001886337127580880253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 208832010060464680431361349 39156001886337127580880253)
            ·
              refine ⟨14683500707376422842830095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39156001886337127580880253 14683500707376422842830095)
              ·
                refine ⟨22025251061064634264245143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14683500707376422842830095 22025251061064634264245143)
                ·
                  refine ⟨33037876591596951396367715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22025251061064634264245143 33037876591596951396367715)
                  ·
                    refine ⟨49556814887395427094551573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33037876591596951396367715 49556814887395427094551573)
                    ·
                      refine ⟨2322975697846660645057105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49556814887395427094551573 2322975697846660645057105)
                      ·
                        rfl

theorem cell23_4523979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 6].length) (baseStart_4523979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523979 prefixEnd_4523979 := by exact prefixLift 4523979
  have htrace : WordTrace (prefixWord ++ tailWord_4523979) baseStart_4523979 baseEnd_4523979 := by
    simpa [prefixWord, tailWord_4523979, baseEnd_4523979] using wordTrace_append hprefix tailTrace_4523979
  have hstable : (prefixWord ++ tailWord_4523979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523979).length < 2 ^ (prefixWord ++ tailWord_4523979).sum := by decide
  have hdescent : baseEnd_4523979 < baseStart_4523979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523983 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 3, 2, 2]
def baseStart_4523983 : Nat := 118140960795 + 4523983 * 2 ^ 59
def prefixEnd_4523983 : Nat := 4983230072969 + 3 ^ 40 * 4523983 * 2
def baseEnd_4523983 : Nat := 2322977751769278629407087

theorem tailTrace_4523983 : CollatzResearch.WordTrace tailWord_4523983 prefixEnd_4523983 2322977751769278629407087 := by
  unfold tailWord_4523983
  simp only [CollatzResearch.WordTrace]
  refine ⟨165003215569389700628912603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110002143712926467085941735 165003215569389700628912603)
  ·
    refine ⟨247504823354084550943368905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165003215569389700628912603 247504823354084550943368905)
    ·
      refine ⟨185628617515563413207526679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247504823354084550943368905 185628617515563413207526679)
      ·
        refine ⟨278442926273345119811290019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185628617515563413207526679 278442926273345119811290019)
        ·
          refine ⟨417664389410017679716935029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278442926273345119811290019 417664389410017679716935029)
          ·
            refine ⟨39156036507189157473462659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 417664389410017679716935029 39156036507189157473462659)
            ·
              refine ⟨58734054760783736210193989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39156036507189157473462659 58734054760783736210193989)
              ·
                refine ⟨11012635267646950539411373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58734054760783736210193989 11012635267646950539411373)
                ·
                  refine ⟨4129738225367606452279265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11012635267646950539411373 4129738225367606452279265)
                  ·
                    refine ⟨3097303669025704839209449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4129738225367606452279265 3097303669025704839209449)
                    ·
                      refine ⟨2322977751769278629407087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097303669025704839209449 2322977751769278629407087)
                      ·
                        rfl

theorem cell23_4523983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 2, 2].length) (baseStart_4523983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523983 prefixEnd_4523983 := by exact prefixLift 4523983
  have htrace : WordTrace (prefixWord ++ tailWord_4523983) baseStart_4523983 baseEnd_4523983 := by
    simpa [prefixWord, tailWord_4523983, baseEnd_4523983] using wordTrace_append hprefix tailTrace_4523983
  have hstable : (prefixWord ++ tailWord_4523983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523983).length < 2 ^ (prefixWord ++ tailWord_4523983).sum := by decide
  have hdescent : baseEnd_4523983 < baseStart_4523983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4523994 : List Nat := [3, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3]
def baseStart_4523994 : Nat := 118140960795 + 4523994 * 2 ^ 59
def prefixEnd_4523994 : Nat := 4983230072969 + 3 ^ 40 * 4523994 * 2
def baseEnd_4523994 : Nat := 2322983400056478086369537

theorem tailTrace_4523994 : CollatzResearch.WordTrace tailWord_4523994 prefixEnd_4523994 2322983400056478086369537 := by
  unfold tailWord_4523994
  simp only [CollatzResearch.WordTrace]
  refine ⟨41250904193087462376890759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110002411181566566338375357 41250904193087462376890759)
  ·
    refine ⟨61876356289631193565336139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41250904193087462376890759 61876356289631193565336139)
    ·
      refine ⟨92814534434446790348004209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61876356289631193565336139 92814534434446790348004209)
      ·
        refine ⟨69610900825835092761003157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92814534434446790348004209 69610900825835092761003157)
        ·
          refine ⟨3263010976211019973172023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69610900825835092761003157 3263010976211019973172023)
          ·
            refine ⟨4894516464316529959758035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263010976211019973172023 4894516464316529959758035)
            ·
              refine ⟨7341774696474794939637053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4894516464316529959758035 7341774696474794939637053)
              ·
                refine ⟨2753165511178048102363895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7341774696474794939637053 2753165511178048102363895)
                ·
                  refine ⟨4129748266767072153545843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2753165511178048102363895 4129748266767072153545843)
                  ·
                    refine ⟨6194622400150608230318765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4129748266767072153545843 6194622400150608230318765)
                    ·
                      refine ⟨2322983400056478086369537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6194622400150608230318765 2322983400056478086369537)
                      ·
                        rfl

theorem cell23_4523994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_4523994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4523994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4523994 prefixEnd_4523994 := by exact prefixLift 4523994
  have htrace : WordTrace (prefixWord ++ tailWord_4523994) baseStart_4523994 baseEnd_4523994 := by
    simpa [prefixWord, tailWord_4523994, baseEnd_4523994] using wordTrace_append hprefix tailTrace_4523994
  have hstable : (prefixWord ++ tailWord_4523994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4523994).length < 2 ^ (prefixWord ++ tailWord_4523994).sum := by decide
  have hdescent : baseEnd_4523994 < baseStart_4523994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4523994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524003 : List Nat := [1, 1, 1, 6, 1, 2, 2, 3, 1, 2, 3]
def baseStart_4524003 : Nat := 118140960795 + 4524003 * 2 ^ 59
def prefixEnd_4524003 : Nat := 4983230072969 + 3 ^ 40 * 4524003 * 2
def baseEnd_4524003 : Nat := 2322988021382368551156995

theorem tailTrace_4524003 : CollatzResearch.WordTrace tailWord_4524003 prefixEnd_4524003 2322988021382368551156995 := by
  unfold tailWord_4524003
  simp only [CollatzResearch.WordTrace]
  refine ⟨165003945029317244044640663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110002630019544829363093775 165003945029317244044640663)
  ·
    refine ⟨247505917543975866066960995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165003945029317244044640663 247505917543975866066960995)
    ·
      refine ⟨371258876315963799100441493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247505917543975866066960995 371258876315963799100441493)
      ·
        refine ⟨17402759827310803082833195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 371258876315963799100441493 17402759827310803082833195)
        ·
          refine ⟨26104139740966204624249793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17402759827310803082833195 26104139740966204624249793)
          ·
            refine ⟨19578104805724653468187345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26104139740966204624249793 19578104805724653468187345)
            ·
              refine ⟨14683578604293490101140509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19578104805724653468187345 14683578604293490101140509)
              ·
                refine ⟨5506341976610058787927691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14683578604293490101140509 5506341976610058787927691)
                ·
                  refine ⟨8259512964915088181891537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5506341976610058787927691 8259512964915088181891537)
                  ·
                    refine ⟨6194634723686316136418653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8259512964915088181891537 6194634723686316136418653)
                    ·
                      refine ⟨2322988021382368551156995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6194634723686316136418653 2322988021382368551156995)
                      ·
                        rfl

theorem cell23_4524003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_4524003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524003 prefixEnd_4524003 := by exact prefixLift 4524003
  have htrace : WordTrace (prefixWord ++ tailWord_4524003) baseStart_4524003 baseEnd_4524003 := by
    simpa [prefixWord, tailWord_4524003, baseEnd_4524003] using wordTrace_append hprefix tailTrace_4524003
  have hstable : (prefixWord ++ tailWord_4524003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524003).length < 2 ^ (prefixWord ++ tailWord_4524003).sum := by decide
  have hdescent : baseEnd_4524003 < baseStart_4524003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524017 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 3, 2, 2]
def baseStart_4524017 : Nat := 118140960795 + 4524017 * 2 ^ 59
def prefixEnd_4524017 : Nat := 4983230072969 + 3 ^ 40 * 4524017 * 2
def baseEnd_4524017 : Nat := 2322995210111531496381931

theorem tailTrace_4524017 : CollatzResearch.WordTrace tailWord_4524017 prefixEnd_4524017 2322995210111531496381931 := by
  unfold tailWord_4524017
  simp only [CollatzResearch.WordTrace]
  refine ⟨165004455651266524435650305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110002970434177682957100203 165004455651266524435650305)
  ·
    refine ⟨123753341738449893326737729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165004455651266524435650305 123753341738449893326737729)
    ·
      refine ⟨92815006303837419995053297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123753341738449893326737729 92815006303837419995053297)
      ·
        refine ⟨69611254727878064996289973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92815006303837419995053297 69611254727878064996289973)
        ·
          refine ⟨6526055130738568593402185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69611254727878064996289973 6526055130738568593402185)
          ·
            refine ⟨4894541348053926445051639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6526055130738568593402185 4894541348053926445051639)
            ·
              refine ⟨7341812022080889667577459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4894541348053926445051639 7341812022080889667577459)
              ·
                refine ⟨11012718033121334501366189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7341812022080889667577459 11012718033121334501366189)
                ·
                  refine ⟨4129769262420500438012321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11012718033121334501366189 4129769262420500438012321)
                  ·
                    refine ⟨3097326946815375328509241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4129769262420500438012321 3097326946815375328509241)
                    ·
                      refine ⟨2322995210111531496381931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097326946815375328509241 2322995210111531496381931)
                      ·
                        rfl

theorem cell23_4524017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_4524017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524017 prefixEnd_4524017 := by exact prefixLift 4524017
  have htrace : WordTrace (prefixWord ++ tailWord_4524017) baseStart_4524017 baseEnd_4524017 := by
    simpa [prefixWord, tailWord_4524017, baseEnd_4524017] using wordTrace_append hprefix tailTrace_4524017
  have hstable : (prefixWord ++ tailWord_4524017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524017).length < 2 ^ (prefixWord ++ tailWord_4524017).sum := by decide
  have hdescent : baseEnd_4524017 < baseStart_4524017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524026 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2]
def baseStart_4524026 : Nat := 118140960795 + 4524026 * 2 ^ 59
def prefixEnd_4524026 : Nat := 4983230072969 + 3 ^ 40 * 4524026 * 2
def baseEnd_4524026 : Nat := 2322999831437421961169389

theorem tailTrace_4524026 : CollatzResearch.WordTrace tailWord_4524026 prefixEnd_4524026 2322999831437421961169389 := by
  unfold tailWord_4524026
  simp only [CollatzResearch.WordTrace]
  refine ⟨41251195977058479743181983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110003189272155945981818621 41251195977058479743181983)
  ·
    refine ⟨61876793965587719614772975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41251195977058479743181983 61876793965587719614772975)
    ·
      refine ⟨92815190948381579422159463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61876793965587719614772975 92815190948381579422159463)
      ·
        refine ⟨139222786422572369133239195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92815190948381579422159463 139222786422572369133239195)
        ·
          refine ⟨208834179633858553699858793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139222786422572369133239195 208834179633858553699858793)
          ·
            refine ⟨156625634725393915274894095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208834179633858553699858793 156625634725393915274894095)
            ·
              refine ⟨234938452088090872912341143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156625634725393915274894095 234938452088090872912341143)
              ·
                refine ⟨352407678132136309368511715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234938452088090872912341143 352407678132136309368511715)
                ·
                  refine ⟨528611517198204464052767573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352407678132136309368511715 528611517198204464052767573)
                  ·
                    refine ⟨3097333108583229281559185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 528611517198204464052767573 3097333108583229281559185)
                    ·
                      refine ⟨2322999831437421961169389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097333108583229281559185 2322999831437421961169389)
                      ·
                        rfl

theorem cell23_4524026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2].length) (baseStart_4524026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524026 prefixEnd_4524026 := by exact prefixLift 4524026
  have htrace : WordTrace (prefixWord ++ tailWord_4524026) baseStart_4524026 baseEnd_4524026 := by
    simpa [prefixWord, tailWord_4524026, baseEnd_4524026] using wordTrace_append hprefix tailTrace_4524026
  have hstable : (prefixWord ++ tailWord_4524026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524026).length < 2 ^ (prefixWord ++ tailWord_4524026).sum := by decide
  have hdescent : baseEnd_4524026 < baseStart_4524026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524043 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 3, 3, 2]
def baseStart_4524043 : Nat := 118140960795 + 4524043 * 2 ^ 59
def prefixEnd_4524043 : Nat := 4983230072969 + 3 ^ 40 * 4524043 * 2
def baseEnd_4524043 : Nat := 2323008560608548394656811

theorem tailTrace_4524043 : CollatzResearch.WordTrace tailWord_4524043 prefixEnd_4524043 2323008560608548394656811 := by
  unfold tailWord_4524043
  simp only [CollatzResearch.WordTrace]
  refine ⟨165005403949172330876096783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110003602632781553917397855 165005403949172330876096783)
  ·
    refine ⟨247508105923758496314145175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165005403949172330876096783 247508105923758496314145175)
    ·
      refine ⟨371262158885637744471217763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247508105923758496314145175 371262158885637744471217763)
      ·
        refine ⟨556893238328456616706826645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371262158885637744471217763 556893238328456616706826645)
        ·
          refine ⟨26104370546646403908132499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 556893238328456616706826645 26104370546646403908132499)
          ·
            refine ⟨39156555819969605862198749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26104370546646403908132499 39156555819969605862198749)
            ·
              refine ⟨14683708432488602198324531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39156555819969605862198749 14683708432488602198324531)
              ·
                refine ⟨22025562648732903297486797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14683708432488602198324531 22025562648732903297486797)
                ·
                  refine ⟨8259585993274838736557549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22025562648732903297486797 8259585993274838736557549)
                  ·
                    refine ⟨3097344747478064526209081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8259585993274838736557549 3097344747478064526209081)
                    ·
                      refine ⟨2323008560608548394656811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097344747478064526209081 2323008560608548394656811)
                      ·
                        rfl

theorem cell23_4524043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 3, 2].length) (baseStart_4524043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524043 prefixEnd_4524043 := by exact prefixLift 4524043
  have htrace : WordTrace (prefixWord ++ tailWord_4524043) baseStart_4524043 baseEnd_4524043 := by
    simpa [prefixWord, tailWord_4524043, baseEnd_4524043] using wordTrace_append hprefix tailTrace_4524043
  have hstable : (prefixWord ++ tailWord_4524043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524043).length < 2 ^ (prefixWord ++ tailWord_4524043).sum := by decide
  have hdescent : baseEnd_4524043 < baseStart_4524043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524049 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 6, 6]
def baseStart_4524049 : Nat := 118140960795 + 4524049 * 2 ^ 59
def prefixEnd_4524049 : Nat := 4983230072969 + 3 ^ 40 * 4524049 * 2
def baseEnd_4524049 : Nat := 774337213830825123727261

theorem tailTrace_4524049 : CollatzResearch.WordTrace tailWord_4524049 prefixEnd_4524049 774337213830825123727261 := by
  unfold tailWord_4524049
  simp only [CollatzResearch.WordTrace]
  refine ⟨165005622787150593900815201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110003748524767062600543467 165005622787150593900815201)
  ·
    refine ⟨123754217090362945425611401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165005622787150593900815201 123754217090362945425611401)
    ·
      refine ⟨92815662817772209069208551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123754217090362945425611401 92815662817772209069208551)
      ·
        refine ⟨139223494226658313603812827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92815662817772209069208551 139223494226658313603812827)
        ·
          refine ⟨208835241339987470405719241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139223494226658313603812827 208835241339987470405719241)
          ·
            refine ⟨156626431004990602804289431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208835241339987470405719241 156626431004990602804289431)
            ·
              refine ⟨234939646507485904206434147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156626431004990602804289431 234939646507485904206434147)
              ·
                refine ⟨352409469761228856309651221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234939646507485904206434147 352409469761228856309651221)
                ·
                  refine ⟨16519193895057602639514901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 352409469761228856309651221 16519193895057602639514901)
                  ·
                    refine ⟨774337213830825123727261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16519193895057602639514901 774337213830825123727261)
                    ·
                      rfl

theorem cell23_4524049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_4524049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524049 prefixEnd_4524049 := by exact prefixLift 4524049
  have htrace : WordTrace (prefixWord ++ tailWord_4524049) baseStart_4524049 baseEnd_4524049 := by
    simpa [prefixWord, tailWord_4524049, baseEnd_4524049] using wordTrace_append hprefix tailTrace_4524049
  have hstable : (prefixWord ++ tailWord_4524049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524049).length < 2 ^ (prefixWord ++ tailWord_4524049).sum := by decide
  have hdescent : baseEnd_4524049 < baseStart_4524049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524059 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 5]
def baseStart_4524059 : Nat := 118140960795 + 4524059 * 2 ^ 59
def prefixEnd_4524059 : Nat := 4983230072969 + 3 ^ 40 * 4524059 * 2
def baseEnd_4524059 : Nat := 2323016776299020332056737

theorem tailTrace_4524059 : CollatzResearch.WordTrace tailWord_4524059 prefixEnd_4524059 2323016776299020332056737 := by
  unfold tailWord_4524059
  simp only [CollatzResearch.WordTrace]
  refine ⟨165005987517114365608679231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110003991678076243739119487 165005987517114365608679231)
  ·
    refine ⟨247508981275671548413018847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165005987517114365608679231 247508981275671548413018847)
    ·
      refine ⟨371263471913507322619528271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247508981275671548413018847 371263471913507322619528271)
      ·
        refine ⟨556895207870260983929292407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371263471913507322619528271 556895207870260983929292407)
        ·
          refine ⟨835342811805391475893938611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556895207870260983929292407 835342811805391475893938611)
          ·
            refine ⟨1253014217708087213840907917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835342811805391475893938611 1253014217708087213840907917)
            ·
              refine ⟨469880331640532705190340469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1253014217708087213840907917 469880331640532705190340469)
              ·
                refine ⟨44051281091299941111594419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 469880331640532705190340469 44051281091299941111594419)
                ·
                  refine ⟨66076921636949911667391629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44051281091299941111594419 66076921636949911667391629)
                  ·
                    refine ⟨24778845613856216875271861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66076921636949911667391629 24778845613856216875271861)
                    ·
                      refine ⟨2323016776299020332056737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24778845613856216875271861 2323016776299020332056737)
                      ·
                        rfl

theorem cell23_4524059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 5].length) (baseStart_4524059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524059 prefixEnd_4524059 := by exact prefixLift 4524059
  have htrace : WordTrace (prefixWord ++ tailWord_4524059) baseStart_4524059 baseEnd_4524059 := by
    simpa [prefixWord, tailWord_4524059, baseEnd_4524059] using wordTrace_append hprefix tailTrace_4524059
  have hstable : (prefixWord ++ tailWord_4524059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524059).length < 2 ^ (prefixWord ++ tailWord_4524059).sum := by decide
  have hdescent : baseEnd_4524059 < baseStart_4524059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524066 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_4524066 : Nat := 118140960795 + 4524066 * 2 ^ 59
def prefixEnd_4524066 : Nat := 4983230072969 + 3 ^ 40 * 4524066 * 2
def baseEnd_4524066 : Nat := 774340123554533934889735

theorem tailTrace_4524066 : CollatzResearch.WordTrace tailWord_4524066 prefixEnd_4524066 774340123554533934889735 := by
  unfold tailWord_4524066
  simp only [CollatzResearch.WordTrace]
  refine ⟨41251560707022251451046013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110004161885392670536122701 41251560707022251451046013)
  ·
    refine ⟨15469335265133344294142255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41251560707022251451046013 15469335265133344294142255)
    ·
      refine ⟨23204002897700016441213383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15469335265133344294142255 23204002897700016441213383)
      ·
        refine ⟨34806004346550024661820075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23204002897700016441213383 34806004346550024661820075)
        ·
          refine ⟨52209006519825036992730113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34806004346550024661820075 52209006519825036992730113)
          ·
            refine ⟨39156754889868777744547585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52209006519825036992730113 39156754889868777744547585)
            ·
              refine ⟨29367566167401583308410689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39156754889868777744547585 29367566167401583308410689)
              ·
                refine ⟨22025674625551187481308017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29367566167401583308410689 22025674625551187481308017)
                ·
                  refine ⟨16519255969163390610981013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22025674625551187481308017 16519255969163390610981013)
                  ·
                    refine ⟨774340123554533934889735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16519255969163390610981013 774340123554533934889735)
                    ·
                      rfl

theorem cell23_4524066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_4524066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524066 prefixEnd_4524066 := by exact prefixLift 4524066
  have htrace : WordTrace (prefixWord ++ tailWord_4524066) baseStart_4524066 baseEnd_4524066 := by
    simpa [prefixWord, tailWord_4524066, baseEnd_4524066] using wordTrace_append hprefix tailTrace_4524066
  have hstable : (prefixWord ++ tailWord_4524066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524066).length < 2 ^ (prefixWord ++ tailWord_4524066).sum := by decide
  have hdescent : baseEnd_4524066 < baseStart_4524066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524068 : List Nat := [2, 3, 1, 4, 3, 1, 2, 2, 1, 2, 2]
def baseStart_4524068 : Nat := 118140960795 + 4524068 * 2 ^ 59
def prefixEnd_4524068 : Nat := 4983230072969 + 3 ^ 40 * 4524068 * 2
def baseEnd_4524068 : Nat := 2323021397624910796844197

theorem tailTrace_4524068 : CollatzResearch.WordTrace tailWord_4524068 prefixEnd_4524068 2323021397624910796844197 := by
  unfold tailWord_4524068
  simp only [CollatzResearch.WordTrace]
  refine ⟨82503157887040880072878429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110004210516054506763837905 82503157887040880072878429)
  ·
    refine ⟨30938684207640330027329411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82503157887040880072878429 30938684207640330027329411)
    ·
      refine ⟨46408026311460495040994117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30938684207640330027329411 46408026311460495040994117)
      ·
        refine ⟨8701504933398842820186397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46408026311460495040994117 8701504933398842820186397)
        ·
          refine ⟨3263064350024566057569899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8701504933398842820186397 3263064350024566057569899)
          ·
            refine ⟨4894596525036849086354849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263064350024566057569899 4894596525036849086354849)
            ·
              refine ⟨3670947393777636814766137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4894596525036849086354849 3670947393777636814766137)
              ·
                refine ⟨2753210545333227611074603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3670947393777636814766137 2753210545333227611074603)
                ·
                  refine ⟨4129815817999841416611905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2753210545333227611074603 4129815817999841416611905)
                  ·
                    refine ⟨3097361863499881062458929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4129815817999841416611905 3097361863499881062458929)
                    ·
                      refine ⟨2323021397624910796844197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097361863499881062458929 2323021397624910796844197)
                      ·
                        rfl

theorem cell23_4524068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_4524068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524068 prefixEnd_4524068 := by exact prefixLift 4524068
  have htrace : WordTrace (prefixWord ++ tailWord_4524068) baseStart_4524068 baseEnd_4524068 := by
    simpa [prefixWord, tailWord_4524068, baseEnd_4524068] using wordTrace_append hprefix tailTrace_4524068
  have hstable : (prefixWord ++ tailWord_4524068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524068).length < 2 ^ (prefixWord ++ tailWord_4524068).sum := by decide
  have hdescent : baseEnd_4524068 < baseStart_4524068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524073 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 10, 2, 2]
def baseStart_4524073 : Nat := 118140960795 + 4524073 * 2 ^ 59
def prefixEnd_4524073 : Nat := 4983230072969 + 3 ^ 40 * 4524073 * 2
def baseEnd_4524073 : Nat := 2323023965028183277281673

theorem tailTrace_4524073 : CollatzResearch.WordTrace tailWord_4524073 prefixEnd_4524073 2323023965028183277281673 := by
  unfold tailWord_4524073
  simp only [CollatzResearch.WordTrace]
  refine ⟨165006498139063645999688873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110004332092709097333125915 165006498139063645999688873)
  ·
    refine ⟨123754873604297734499766655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165006498139063645999688873 123754873604297734499766655)
    ·
      refine ⟨185632310406446601749649983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123754873604297734499766655 185632310406446601749649983)
      ·
        refine ⟨278448465609669902624474975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185632310406446601749649983 278448465609669902624474975)
        ·
          refine ⟨417672698414504853936712463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278448465609669902624474975 417672698414504853936712463)
          ·
            refine ⟨626509047621757280905068695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417672698414504853936712463 626509047621757280905068695)
            ·
              refine ⟨939763571432635921357603043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626509047621757280905068695 939763571432635921357603043)
              ·
                refine ⟨1409645357148953882036404565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 939763571432635921357603043 1409645357148953882036404565)
                ·
                  refine ⟨4129820382272325826278529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1409645357148953882036404565 4129820382272325826278529)
                  ·
                    refine ⟨3097365286704244369708897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4129820382272325826278529 3097365286704244369708897)
                    ·
                      refine ⟨2323023965028183277281673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097365286704244369708897 2323023965028183277281673)
                      ·
                        rfl

theorem cell23_4524073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 2, 2].length) (baseStart_4524073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524073 prefixEnd_4524073 := by exact prefixLift 4524073
  have htrace : WordTrace (prefixWord ++ tailWord_4524073) baseStart_4524073 baseEnd_4524073 := by
    simpa [prefixWord, tailWord_4524073, baseEnd_4524073] using wordTrace_append hprefix tailTrace_4524073
  have hstable : (prefixWord ++ tailWord_4524073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524073).length < 2 ^ (prefixWord ++ tailWord_4524073).sum := by decide
  have hdescent : baseEnd_4524073 < baseStart_4524073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524096 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 7]
def baseStart_4524096 : Nat := 118140960795 + 4524096 * 2 ^ 59
def prefixEnd_4524096 : Nat := 4983230072969 + 3 ^ 40 * 4524096 * 2
def baseEnd_4524096 : Nat := 258115086120359631921563

theorem tailTrace_4524096 : CollatzResearch.WordTrace tailWord_4524096 prefixEnd_4524096 258115086120359631921563 := by
  unfold tailWord_4524096
  simp only [CollatzResearch.WordTrace]
  refine ⟨82503668508990160463888071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110004891345320213951850761 82503668508990160463888071)
  ·
    refine ⟨123755502763485240695832107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82503668508990160463888071 123755502763485240695832107)
    ·
      refine ⟨185633254145227861043748161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123755502763485240695832107 185633254145227861043748161)
      ·
        refine ⟨139224940608920895782811121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185633254145227861043748161 139224940608920895782811121)
        ·
          refine ⟨104418705456690671837108341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139224940608920895782811121 104418705456690671837108341)
          ·
            refine ⟨9789253636564750484728907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104418705456690671837108341 9789253636564750484728907)
            ·
              refine ⟨14683880454847125727093361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9789253636564750484728907 14683880454847125727093361)
              ·
                refine ⟨11012910341135344295320021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14683880454847125727093361 11012910341135344295320021)
                ·
                  refine ⟨258115086120359631921563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11012910341135344295320021 258115086120359631921563)
                  ·
                    rfl

theorem cell23_4524096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 7].length) (baseStart_4524096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524096 prefixEnd_4524096 := by exact prefixLift 4524096
  have htrace : WordTrace (prefixWord ++ tailWord_4524096) baseStart_4524096 baseEnd_4524096 := by
    simpa [prefixWord, tailWord_4524096, baseEnd_4524096] using wordTrace_append hprefix tailTrace_4524096
  have hstable : (prefixWord ++ tailWord_4524096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524096).length < 2 ^ (prefixWord ++ tailWord_4524096).sum := by decide
  have hdescent : baseEnd_4524096 < baseStart_4524096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524106 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_4524106 : Nat := 118140960795 + 4524106 * 2 ^ 59
def prefixEnd_4524106 : Nat := 4983230072969 + 3 ^ 40 * 4524106 * 2
def baseEnd_4524106 : Nat := 2323040909889781648169021

theorem tailTrace_4524106 : CollatzResearch.WordTrace tailWord_4524106 prefixEnd_4524106 2323040909889781648169021 := by
  unfold tailWord_4524106
  simp only [CollatzResearch.WordTrace]
  refine ⟨41251925436986023158910043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110005134498629395090426781 41251925436986023158910043)
  ·
    refine ⟨61877888155479034738365065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41251925436986023158910043 61877888155479034738365065)
    ·
      refine ⟨46408416116609276053773799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61877888155479034738365065 46408416116609276053773799)
      ·
        refine ⟨69612624174913914080660699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46408416116609276053773799 69612624174913914080660699)
        ·
          refine ⟨104418936262370871120991049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69612624174913914080660699 104418936262370871120991049)
          ·
            refine ⟨78314202196778153340743287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104418936262370871120991049 78314202196778153340743287)
            ·
              refine ⟨117471303295167230011114931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78314202196778153340743287 117471303295167230011114931)
              ·
                refine ⟨176206954942750845016672397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117471303295167230011114931 176206954942750845016672397)
                ·
                  refine ⟨66077608103531566881252149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176206954942750845016672397 66077608103531566881252149)
                  ·
                    refine ⟨6194775759706084395117389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66077608103531566881252149 6194775759706084395117389)
                    ·
                      refine ⟨2323040909889781648169021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6194775759706084395117389 2323040909889781648169021)
                      ·
                        rfl

theorem cell23_4524106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_4524106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524106 prefixEnd_4524106 := by exact prefixLift 4524106
  have htrace : WordTrace (prefixWord ++ tailWord_4524106) baseStart_4524106 baseEnd_4524106 := by
    simpa [prefixWord, tailWord_4524106, baseEnd_4524106] using wordTrace_append hprefix tailTrace_4524106
  have hstable : (prefixWord ++ tailWord_4524106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524106).length < 2 ^ (prefixWord ++ tailWord_4524106).sum := by decide
  have hdescent : baseEnd_4524106 < baseStart_4524106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524124 : List Nat := [2, 2, 4, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_4524124 : Nat := 118140960795 + 4524124 * 2 ^ 59
def prefixEnd_4524124 : Nat := 4983230072969 + 3 ^ 40 * 4524124 * 2
def baseEnd_4524124 : Nat := 2323050152541562577743939

theorem tailTrace_4524124 : CollatzResearch.WordTrace tailWord_4524124 prefixEnd_4524124 2323050152541562577743939 := by
  unfold tailWord_4524124
  simp only [CollatzResearch.WordTrace]
  refine ⟨82504179130939440854897713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110005572174585921139863617 82504179130939440854897713)
  ·
    refine ⟨61878134348204580641173285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82504179130939440854897713 61878134348204580641173285)
    ·
      refine ⟨11602150190288358870219991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61878134348204580641173285 11602150190288358870219991)
      ·
        refine ⟨17403225285432538305329987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11602150190288358870219991 17403225285432538305329987)
        ·
          refine ⟨26104837928148807457994981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17403225285432538305329987 26104837928148807457994981)
          ·
            refine ⟨4894657111527901398374059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26104837928148807457994981 4894657111527901398374059)
            ·
              refine ⟨7341985667291852097561089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4894657111527901398374059 7341985667291852097561089)
              ·
                refine ⟨5506489250468889073170817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7341985667291852097561089 5506489250468889073170817)
                ·
                  refine ⟨4129866937851666804878113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5506489250468889073170817 4129866937851666804878113)
                  ·
                    refine ⟨3097400203388750103658585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4129866937851666804878113 3097400203388750103658585)
                    ·
                      refine ⟨2323050152541562577743939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097400203388750103658585 2323050152541562577743939)
                      ·
                        rfl

theorem cell23_4524124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_4524124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524124 prefixEnd_4524124 := by exact prefixLift 4524124
  have htrace : WordTrace (prefixWord ++ tailWord_4524124) baseStart_4524124 baseEnd_4524124 := by
    simpa [prefixWord, tailWord_4524124, baseEnd_4524124] using wordTrace_append hprefix tailTrace_4524124
  have hstable : (prefixWord ++ tailWord_4524124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524124).length < 2 ^ (prefixWord ++ tailWord_4524124).sum := by decide
  have hdescent : baseEnd_4524124 < baseStart_4524124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524130 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 7]
def baseStart_4524130 : Nat := 118140960795 + 4524130 * 2 ^ 59
def prefixEnd_4524130 : Nat := 4983230072969 + 3 ^ 40 * 4524130 * 2
def baseEnd_4524130 : Nat := 258117025936165506029879

theorem tailTrace_4524130 : CollatzResearch.WordTrace tailWord_4524130 prefixEnd_4524130 258117025936165506029879 := by
  unfold tailWord_4524130
  simp only [CollatzResearch.WordTrace]
  refine ⟨41252144274964286183628461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110005718066571429823009229 41252144274964286183628461)
  ·
    refine ⟨15469554103111607318860673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41252144274964286183628461 15469554103111607318860673)
    ·
      refine ⟨11602165577333705489145505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15469554103111607318860673 11602165577333705489145505)
      ·
        refine ⟨8701624183000279116859129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11602165577333705489145505 8701624183000279116859129)
        ·
          refine ⟨6526218137250209337644347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8701624183000279116859129 6526218137250209337644347)
          ·
            refine ⟨9789327205875314006466521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6526218137250209337644347 9789327205875314006466521)
            ·
              refine ⟨7341995404406485504849891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9789327205875314006466521 7341995404406485504849891)
              ·
                refine ⟨11012993106609728257274837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7341995404406485504849891 11012993106609728257274837)
                ·
                  refine ⟨258117025936165506029879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11012993106609728257274837 258117025936165506029879)
                  ·
                    rfl

theorem cell23_4524130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_4524130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524130 prefixEnd_4524130 := by exact prefixLift 4524130
  have htrace : WordTrace (prefixWord ++ tailWord_4524130) baseStart_4524130 baseEnd_4524130 := by
    simpa [prefixWord, tailWord_4524130, baseEnd_4524130] using wordTrace_append hprefix tailTrace_4524130
  have hstable : (prefixWord ++ tailWord_4524130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524130).length < 2 ^ (prefixWord ++ tailWord_4524130).sum := by decide
  have hdescent : baseEnd_4524130 < baseStart_4524130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524270 : List Nat := [4, 1, 2, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_4524270 : Nat := 118140960795 + 4524270 * 2 ^ 59
def prefixEnd_4524270 : Nat := 4983230072969 + 3 ^ 40 * 4524270 * 2
def baseEnd_4524270 : Nat := 2323125120717119006518267

theorem tailTrace_4524270 : CollatzResearch.WordTrace tailWord_4524270 prefixEnd_4524270 2323125120717119006518267 := by
  unfold tailWord_4524270
  simp only [CollatzResearch.WordTrace]
  refine ⟨20626710414918743580576283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110009122212899965763073509 20626710414918743580576283)
  ·
    refine ⟨30940065622378115370864425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20626710414918743580576283 30940065622378115370864425)
    ·
      refine ⟨23205049216783586528148319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30940065622378115370864425 23205049216783586528148319)
      ·
        refine ⟨34807573825175379792222479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23205049216783586528148319 34807573825175379792222479)
        ·
          refine ⟨52211360737763069688333719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34807573825175379792222479 52211360737763069688333719)
          ·
            refine ⟨78317041106644604532500579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52211360737763069688333719 78317041106644604532500579)
            ·
              refine ⟨117475561659966906798750869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78317041106644604532500579 117475561659966906798750869)
              ·
                refine ⟨5506666952810948756191447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117475561659966906798750869 5506666952810948756191447)
                ·
                  refine ⟨8260000429216423134287171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5506666952810948756191447 8260000429216423134287171)
                  ·
                    refine ⟨12390000643824634701430757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8260000429216423134287171 12390000643824634701430757)
                    ·
                      refine ⟨2323125120717119006518267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12390000643824634701430757 2323125120717119006518267)
                      ·
                        rfl

theorem cell23_4524270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_4524270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524270 prefixEnd_4524270 := by exact prefixLift 4524270
  have htrace : WordTrace (prefixWord ++ tailWord_4524270) baseStart_4524270 baseEnd_4524270 := by
    simpa [prefixWord, tailWord_4524270, baseEnd_4524270] using wordTrace_append hprefix tailTrace_4524270
  have hstable : (prefixWord ++ tailWord_4524270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524270).length < 2 ^ (prefixWord ++ tailWord_4524270).sum := by decide
  have hdescent : baseEnd_4524270 < baseStart_4524270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524274 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 2, 3, 2]
def baseStart_4524274 : Nat := 118140960795 + 4524274 * 2 ^ 59
def prefixEnd_4524274 : Nat := 4983230072969 + 3 ^ 40 * 4524274 * 2
def baseEnd_4524274 : Nat := 2323127174639736990868249

theorem tailTrace_4524274 : CollatzResearch.WordTrace tailWord_4524274 prefixEnd_4524274 2323127174639736990868249 := by
  unfold tailWord_4524274
  simp only [CollatzResearch.WordTrace]
  refine ⟨41253457302833864331938969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110009219474223638218503917 41253457302833864331938969)
  ·
    refine ⟨30940092977125398248954227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41253457302833864331938969 30940092977125398248954227)
    ·
      refine ⟨46410139465688097373431341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30940092977125398248954227 46410139465688097373431341)
      ·
        refine ⟨17403802299633036515036753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46410139465688097373431341 17403802299633036515036753)
        ·
          refine ⟨13052851724724777386277565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17403802299633036515036753 13052851724724777386277565)
          ·
            refine ⟨4894819396771791519854087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13052851724724777386277565 4894819396771791519854087)
            ·
              refine ⟨7342229095157687279781131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4894819396771791519854087 7342229095157687279781131)
              ·
                refine ⟨11013343642736530919671697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7342229095157687279781131 11013343642736530919671697)
                ·
                  refine ⟨8260007732052398189753773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11013343642736530919671697 8260007732052398189753773)
                  ·
                    refine ⟨3097502899519649321157665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8260007732052398189753773 3097502899519649321157665)
                    ·
                      refine ⟨2323127174639736990868249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097502899519649321157665 2323127174639736990868249)
                      ·
                        rfl

theorem cell23_4524274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_4524274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524274 prefixEnd_4524274 := by exact prefixLift 4524274
  have htrace : WordTrace (prefixWord ++ tailWord_4524274) baseStart_4524274 baseEnd_4524274 := by
    simpa [prefixWord, tailWord_4524274, baseEnd_4524274] using wordTrace_append hprefix tailTrace_4524274
  have hstable : (prefixWord ++ tailWord_4524274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524274).length < 2 ^ (prefixWord ++ tailWord_4524274).sum := by decide
  have hdescent : baseEnd_4524274 < baseStart_4524274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524297 : List Nat := [1, 2, 1, 1, 3, 6, 1, 2, 2, 4]
def baseStart_4524297 : Nat := 118140960795 + 4524297 * 2 ^ 59
def prefixEnd_4524297 : Nat := 4983230072969 + 3 ^ 40 * 4524297 * 2
def baseEnd_4524297 : Nat := 774379661564930133626881

theorem tailTrace_4524297 : CollatzResearch.WordTrace tailWord_4524297 prefixEnd_4524297 774379661564930133626881 := by
  unfold tailWord_4524297
  simp only [CollatzResearch.WordTrace]
  refine ⟨165014668090252132255843145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110009778726834754837228763 165014668090252132255843145)
  ·
    refine ⟨123761001067689099191882359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165014668090252132255843145 123761001067689099191882359)
    ·
      refine ⟨185641501601533648787823539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123761001067689099191882359 185641501601533648787823539)
      ·
        refine ⟨278462252402300473181735309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185641501601533648787823539 278462252402300473181735309)
        ·
          refine ⟨104423344650862677443150741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278462252402300473181735309 104423344650862677443150741)
          ·
            refine ⟨4894844280509188005147691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 104423344650862677443150741 4894844280509188005147691)
            ·
              refine ⟨7342266420763782007721537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4894844280509188005147691 7342266420763782007721537)
              ·
                refine ⟨5506699815572836505791153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7342266420763782007721537 5506699815572836505791153)
                ·
                  refine ⟨4130024861679627379343365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5506699815572836505791153 4130024861679627379343365)
                  ·
                    refine ⟨774379661564930133626881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4130024861679627379343365 774379661564930133626881)
                    ·
                      rfl

theorem cell23_4524297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 4].length) (baseStart_4524297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524297 prefixEnd_4524297 := by exact prefixLift 4524297
  have htrace : WordTrace (prefixWord ++ tailWord_4524297) baseStart_4524297 baseEnd_4524297 := by
    simpa [prefixWord, tailWord_4524297, baseEnd_4524297] using wordTrace_append hprefix tailTrace_4524297
  have hstable : (prefixWord ++ tailWord_4524297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524297).length < 2 ^ (prefixWord ++ tailWord_4524297).sum := by decide
  have hdescent : baseEnd_4524297 < baseStart_4524297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524303 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 3]
def baseStart_4524303 : Nat := 118140960795 + 4524303 * 2 ^ 59
def prefixEnd_4524303 : Nat := 4983230072969 + 3 ^ 40 * 4524303 * 2
def baseEnd_4524303 : Nat := 2323142065578717377405615

theorem tailTrace_4524303 : CollatzResearch.WordTrace tailWord_4524303 prefixEnd_4524303 2323142065578717377405615 := by
  unfold tailWord_4524303
  simp only [CollatzResearch.WordTrace]
  refine ⟨165014886928230395280561563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110009924618820263520374375 165014886928230395280561563)
  ·
    refine ⟨247522330392345592920842345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165014886928230395280561563 247522330392345592920842345)
    ·
      refine ⟨185641747794259194690631759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247522330392345592920842345 185641747794259194690631759)
      ·
        refine ⟨278462621691388792035947639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185641747794259194690631759 278462621691388792035947639)
        ·
          refine ⟨417693932537083188053921459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278462621691388792035947639 417693932537083188053921459)
          ·
            refine ⟨626540898805624782080882189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417693932537083188053921459 626540898805624782080882189)
            ·
              refine ⟨234952837052109293280330821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 626540898805624782080882189 234952837052109293280330821)
              ·
                refine ⟨44053656947270492490062029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234952837052109293280330821 44053656947270492490062029)
                ·
                  refine ⟨16520121355226434683773261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44053656947270492490062029 16520121355226434683773261)
                  ·
                    refine ⟨6195045508209913006414973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16520121355226434683773261 6195045508209913006414973)
                    ·
                      refine ⟨2323142065578717377405615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6195045508209913006414973 2323142065578717377405615)
                      ·
                        rfl

theorem cell23_4524303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 3].length) (baseStart_4524303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524303 prefixEnd_4524303 := by exact prefixLift 4524303
  have htrace : WordTrace (prefixWord ++ tailWord_4524303) baseStart_4524303 baseEnd_4524303 := by
    simpa [prefixWord, tailWord_4524303, baseEnd_4524303] using wordTrace_append hprefix tailTrace_4524303
  have hstable : (prefixWord ++ tailWord_4524303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524303).length < 2 ^ (prefixWord ++ tailWord_4524303).sum := by decide
  have hdescent : baseEnd_4524303 < baseStart_4524303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524314 : List Nat := [3, 1, 1, 3, 4, 1, 3, 1, 2, 4]
def baseStart_4524314 : Nat := 118140960795 + 4524314 * 2 ^ 59
def prefixEnd_4524314 : Nat := 4983230072969 + 3 ^ 40 * 4524314 * 2
def baseEnd_4524314 : Nat := 774382571288638944789355

theorem tailTrace_4524314 : CollatzResearch.WordTrace tailWord_4524314 prefixEnd_4524314 774382571288638944789355 := by
  unfold tailWord_4524314
  simp only [CollatzResearch.WordTrace]
  refine ⟨41253822032797636039802999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110010192087460362772807997 41253822032797636039802999)
  ·
    refine ⟨61880733049196454059704499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41253822032797636039802999 61880733049196454059704499)
    ·
      refine ⟨92821099573794681089556749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61880733049196454059704499 92821099573794681089556749)
      ·
        refine ⟨34807912340173005408583781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92821099573794681089556749 34807912340173005408583781)
        ·
          refine ⟨6526483563782438514109459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34807912340173005408583781 6526483563782438514109459)
          ·
            refine ⟨9789725345673657771164189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6526483563782438514109459 9789725345673657771164189)
            ·
              refine ⟨3671147004627621664186571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9789725345673657771164189 3671147004627621664186571)
              ·
                refine ⟨5506720506941432496279857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3671147004627621664186571 5506720506941432496279857)
                ·
                  refine ⟨4130040380206074372209893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5506720506941432496279857 4130040380206074372209893)
                  ·
                    refine ⟨774382571288638944789355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4130040380206074372209893 774382571288638944789355)
                    ·
                      rfl

theorem cell23_4524314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_4524314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524314 prefixEnd_4524314 := by exact prefixLift 4524314
  have htrace : WordTrace (prefixWord ++ tailWord_4524314) baseStart_4524314 baseEnd_4524314 := by
    simpa [prefixWord, tailWord_4524314, baseEnd_4524314] using wordTrace_append hprefix tailTrace_4524314
  have hstable : (prefixWord ++ tailWord_4524314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524314).length < 2 ^ (prefixWord ++ tailWord_4524314).sum := by decide
  have hdescent : baseEnd_4524314 < baseStart_4524314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
