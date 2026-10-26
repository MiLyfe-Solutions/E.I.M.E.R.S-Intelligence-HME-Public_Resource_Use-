import V185TrunkScan23Chunk1075

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6370565 : List Nat := [1, 3, 1, 1, 2, 1, 6, 2, 2, 1, 3]
def baseStart_6370565 : Nat := 118140960795 + 6370565 * 2 ^ 59
def prefixEnd_6370565 : Nat := 4983230072969 + 3 ^ 40 * 6370565 * 2
def baseEnd_6370565 : Nat := 3271161885709972868839811

theorem tailTrace_6370565 : CollatzResearch.WordTrace tailWord_6370565 prefixEnd_6370565 3271161885709972868839811 := by
  unfold tailWord_6370565
  simp only [CollatzResearch.WordTrace]
  refine ⟨232353594165538485726537149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154902396110358990484358099 232353594165538485726537149)
  ·
    refine ⟨87132597812076932147451431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232353594165538485726537149 87132597812076932147451431)
    ·
      refine ⟨130698896718115398221177147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87132597812076932147451431 130698896718115398221177147)
      ·
        refine ⟨196048345077173097331765721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130698896718115398221177147 196048345077173097331765721)
        ·
          refine ⟨147036258807879822998824291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196048345077173097331765721 147036258807879822998824291)
          ·
            refine ⟨220554388211819734498236437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147036258807879822998824291 220554388211819734498236437)
            ·
              refine ⟨10338486947429050054604833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220554388211819734498236437 10338486947429050054604833)
              ·
                refine ⟨7753865210571787540953625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10338486947429050054604833 7753865210571787540953625)
                ·
                  refine ⟨5815398907928840655715219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7753865210571787540953625 5815398907928840655715219)
                  ·
                    refine ⟨8723098361893260983572829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5815398907928840655715219 8723098361893260983572829)
                    ·
                      refine ⟨3271161885709972868839811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8723098361893260983572829 3271161885709972868839811)
                      ·
                        rfl

theorem cell23_6370565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_6370565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370565 prefixEnd_6370565 := by exact prefixLift 6370565
  have htrace : WordTrace (prefixWord ++ tailWord_6370565) baseStart_6370565 baseEnd_6370565 := by
    simpa [prefixWord, tailWord_6370565, baseEnd_6370565] using wordTrace_append hprefix tailTrace_6370565
  have hstable : (prefixWord ++ tailWord_6370565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370565).length < 2 ^ (prefixWord ++ tailWord_6370565).sum := by decide
  have hdescent : baseEnd_6370565 < baseStart_6370565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370571 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 4]
def baseStart_6370571 : Nat := 118140960795 + 6370571 * 2 ^ 59
def prefixEnd_6370571 : Nat := 4983230072969 + 3 ^ 40 * 6370571 * 2
def baseEnd_6370571 : Nat := 3271164966593899845364783

theorem tailTrace_6370571 : CollatzResearch.WordTrace tailWord_6370571 prefixEnd_6370571 3271164966593899845364783 := by
  unfold tailWord_6370571
  simp only [CollatzResearch.WordTrace]
  refine ⟨232353813003516748751255567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154902542002344499167503711 232353813003516748751255567)
  ·
    refine ⟨348530719505275123126883351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232353813003516748751255567 348530719505275123126883351)
    ·
      refine ⟨522796079257912684690325027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348530719505275123126883351 522796079257912684690325027)
      ·
        refine ⟨784194118886869027035487541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522796079257912684690325027 784194118886869027035487541)
        ·
          refine ⟨73518198645643971284576957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 784194118886869027035487541 73518198645643971284576957)
          ·
            refine ⟨27569324492116489231716359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73518198645643971284576957 27569324492116489231716359)
            ·
              refine ⟨41353986738174733847574539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27569324492116489231716359 41353986738174733847574539)
              ·
                refine ⟨62030980107262100771361809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41353986738174733847574539 62030980107262100771361809)
                ·
                  refine ⟨46523235080446575578521357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62030980107262100771361809 46523235080446575578521357)
                  ·
                    refine ⟨17446213155167465841945509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46523235080446575578521357 17446213155167465841945509)
                    ·
                      refine ⟨3271164966593899845364783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17446213155167465841945509 3271164966593899845364783)
                      ·
                        rfl

theorem cell23_6370571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 4].length) (baseStart_6370571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370571 prefixEnd_6370571 := by exact prefixLift 6370571
  have htrace : WordTrace (prefixWord ++ tailWord_6370571) baseStart_6370571 baseEnd_6370571 := by
    simpa [prefixWord, tailWord_6370571, baseEnd_6370571] using wordTrace_append hprefix tailTrace_6370571
  have hstable : (prefixWord ++ tailWord_6370571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370571).length < 2 ^ (prefixWord ++ tailWord_6370571).sum := by decide
  have hdescent : baseEnd_6370571 < baseStart_6370571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370609 : List Nat := [1, 2, 2, 3, 3, 3, 2, 1, 1, 3, 2]
def baseStart_6370609 : Nat := 118140960795 + 6370609 * 2 ^ 59
def prefixEnd_6370609 : Nat := 4983230072969 + 3 ^ 40 * 6370609 * 2
def baseEnd_6370609 : Nat := 3271184478858770696689609

theorem tailTrace_6370609 : CollatzResearch.WordTrace tailWord_6370609 prefixEnd_6370609 3271184478858770696689609 := by
  unfold tailWord_6370609
  simp only [CollatzResearch.WordTrace]
  refine ⟨232355198977379081241138881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154903465984919387494092587 232355198977379081241138881)
  ·
    refine ⟨174266399233034310930854161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232355198977379081241138881 174266399233034310930854161)
    ·
      refine ⟨130699799424775733198140621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174266399233034310930854161 130699799424775733198140621)
      ·
        refine ⟨49012424784290899949302733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130699799424775733198140621 49012424784290899949302733)
        ·
          refine ⟨18379659294109087480988525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49012424784290899949302733 18379659294109087480988525)
          ·
            refine ⟨6892372235290907805370697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18379659294109087480988525 6892372235290907805370697)
            ·
              refine ⟨5169279176468180854028023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6892372235290907805370697 5169279176468180854028023)
              ·
                refine ⟨7753918764702271281042035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5169279176468180854028023 7753918764702271281042035)
                ·
                  refine ⟨11630878147053406921563053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7753918764702271281042035 11630878147053406921563053)
                  ·
                    refine ⟨4361579305145027595586145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11630878147053406921563053 4361579305145027595586145)
                    ·
                      refine ⟨3271184478858770696689609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361579305145027595586145 3271184478858770696689609)
                      ·
                        rfl

theorem cell23_6370609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_6370609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370609 prefixEnd_6370609 := by exact prefixLift 6370609
  have htrace : WordTrace (prefixWord ++ tailWord_6370609) baseStart_6370609 baseEnd_6370609 := by
    simpa [prefixWord, tailWord_6370609, baseEnd_6370609] using wordTrace_append hprefix tailTrace_6370609
  have hstable : (prefixWord ++ tailWord_6370609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370609).length < 2 ^ (prefixWord ++ tailWord_6370609).sum := by decide
  have hdescent : baseEnd_6370609 < baseStart_6370609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370622 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_6370622 : Nat := 118140960795 + 6370622 * 2 ^ 59
def prefixEnd_6370622 : Nat := 4983230072969 + 3 ^ 40 * 6370622 * 2
def baseEnd_6370622 : Nat := 3271191154107279145827049

theorem tailTrace_6370622 : CollatzResearch.WordTrace tailWord_6370622 prefixEnd_6370622 3271191154107279145827049 := by
  unfold tailWord_6370622
  simp only [CollatzResearch.WordTrace]
  refine ⟨29044459140791498057670265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154903782084221322974241413 29044459140791498057670265)
  ·
    refine ⟨21783344355593623543252699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29044459140791498057670265 21783344355593623543252699)
    ·
      refine ⟨32675016533390435314879049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21783344355593623543252699 32675016533390435314879049)
      ·
        refine ⟨24506262400042826486159287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32675016533390435314879049 24506262400042826486159287)
        ·
          refine ⟨36759393600064239729238931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24506262400042826486159287 36759393600064239729238931)
          ·
            refine ⟨55139090400096359593858397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36759393600064239729238931 55139090400096359593858397)
            ·
              refine ⟨20677158900036134847696899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55139090400096359593858397 20677158900036134847696899)
              ·
                refine ⟨31015738350054202271545349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20677158900036134847696899 31015738350054202271545349)
                ·
                  refine ⟨5815450940635162925914753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31015738350054202271545349 5815450940635162925914753)
                  ·
                    refine ⟨4361588205476372194436065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5815450940635162925914753 4361588205476372194436065)
                    ·
                      refine ⟨3271191154107279145827049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361588205476372194436065 3271191154107279145827049)
                      ·
                        rfl

theorem cell23_6370622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_6370622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370622 prefixEnd_6370622 := by exact prefixLift 6370622
  have htrace : WordTrace (prefixWord ++ tailWord_6370622) baseStart_6370622 baseEnd_6370622 := by
    simpa [prefixWord, tailWord_6370622, baseEnd_6370622] using wordTrace_append hprefix tailTrace_6370622
  have hstable : (prefixWord ++ tailWord_6370622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370622).length < 2 ^ (prefixWord ++ tailWord_6370622).sum := by decide
  have hdescent : baseEnd_6370622 < baseStart_6370622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370638 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_6370638 : Nat := 118140960795 + 6370638 * 2 ^ 59
def prefixEnd_6370638 : Nat := 4983230072969 + 3 ^ 40 * 6370638 * 2
def baseEnd_6370638 : Nat := 3271199369797751083226975

theorem tailTrace_6370638 : CollatzResearch.WordTrace tailWord_6370638 prefixEnd_6370638 3271199369797751083226975 := by
  unfold tailWord_6370638
  simp only [CollatzResearch.WordTrace]
  refine ⟨29044532086784252399243071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154904171129516012795963045 29044532086784252399243071)
  ·
    refine ⟨43566798130176378598864607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29044532086784252399243071 43566798130176378598864607)
    ·
      refine ⟨65350197195264567898296911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43566798130176378598864607 65350197195264567898296911)
      ·
        refine ⟨98025295792896851847445367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65350197195264567898296911 98025295792896851847445367)
        ·
          refine ⟨147037943689345277771168051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98025295792896851847445367 147037943689345277771168051)
          ·
            refine ⟨220556915534017916656752077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147037943689345277771168051 220556915534017916656752077)
            ·
              refine ⟨82708843325256718746282029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220556915534017916656752077 82708843325256718746282029)
              ·
                refine ⟨31015816246971269529855761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82708843325256718746282029 31015816246971269529855761)
                ·
                  refine ⟨23261862185228452147391821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31015816246971269529855761 23261862185228452147391821)
                  ·
                    refine ⟨8723198319460669555271933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23261862185228452147391821 8723198319460669555271933)
                    ·
                      refine ⟨3271199369797751083226975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8723198319460669555271933 3271199369797751083226975)
                      ·
                        rfl

theorem cell23_6370638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_6370638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370638 prefixEnd_6370638 := by exact prefixLift 6370638
  have htrace : WordTrace (prefixWord ++ tailWord_6370638) baseStart_6370638 baseEnd_6370638 := by
    simpa [prefixWord, tailWord_6370638, baseEnd_6370638] using wordTrace_append hprefix tailTrace_6370638
  have hstable : (prefixWord ++ tailWord_6370638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370638).length < 2 ^ (prefixWord ++ tailWord_6370638).sum := by decide
  have hdescent : baseEnd_6370638 < baseStart_6370638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370641 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 3, 7]
def baseStart_6370641 : Nat := 118140960795 + 6370641 * 2 ^ 59
def prefixEnd_6370641 : Nat := 4983230072969 + 3 ^ 40 * 6370641 * 2
def baseEnd_6370641 : Nat := 1090400303413238190496487

theorem tailTrace_6370641 : CollatzResearch.WordTrace tailWord_6370641 prefixEnd_6370641 1090400303413238190496487 := by
  unfold tailWord_6370641
  simp only [CollatzResearch.WordTrace]
  refine ⟨232356366113263150706303777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154904244075508767137535851 232356366113263150706303777)
  ·
    refine ⟨174267274584947363029727833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232356366113263150706303777 174267274584947363029727833)
    ·
      refine ⟨130700455938710522272295875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174267274584947363029727833 130700455938710522272295875)
      ·
        refine ⟨196050683908065783408443813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130700455938710522272295875 196050683908065783408443813)
        ·
          refine ⟨36759503232762334389083215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196050683908065783408443813 36759503232762334389083215)
          ·
            refine ⟨55139254849143501583624823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36759503232762334389083215 55139254849143501583624823)
            ·
              refine ⟨82708882273715252375437235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55139254849143501583624823 82708882273715252375437235)
              ·
                refine ⟨124063323410572878563155853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82708882273715252375437235 124063323410572878563155853)
                ·
                  refine ⟨46523746278964829461183445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124063323410572878563155853 46523746278964829461183445)
                  ·
                    refine ⟨1090400303413238190496487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46523746278964829461183445 1090400303413238190496487)
                    ·
                      rfl

theorem cell23_6370641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_6370641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370641 prefixEnd_6370641 := by exact prefixLift 6370641
  have htrace : WordTrace (prefixWord ++ tailWord_6370641) baseStart_6370641 baseEnd_6370641 := by
    simpa [prefixWord, tailWord_6370641, baseEnd_6370641] using wordTrace_append hprefix tailTrace_6370641
  have hstable : (prefixWord ++ tailWord_6370641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370641).length < 2 ^ (prefixWord ++ tailWord_6370641).sum := by decide
  have hdescent : baseEnd_6370641 < baseStart_6370641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370658 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_6370658 : Nat := 118140960795 + 6370658 * 2 ^ 59
def prefixEnd_6370658 : Nat := 4983230072969 + 3 ^ 40 * 6370658 * 2
def baseEnd_6370658 : Nat := 1090403213136947001658961

theorem tailTrace_6370658 : CollatzResearch.WordTrace tailWord_6370658 prefixEnd_6370658 1090403213136947001658961 := by
  unfold tailWord_6370658
  simp only [CollatzResearch.WordTrace]
  refine ⟨58089246538550390652418157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154904657436134375073115085 58089246538550390652418157)
  ·
    refine ⟨21783467451956396494656809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58089246538550390652418157 21783467451956396494656809)
    ·
      refine ⟨16337600588967297370992607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21783467451956396494656809 16337600588967297370992607)
      ·
        refine ⟨24506400883450946056488911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16337600588967297370992607 24506400883450946056488911)
        ·
          refine ⟨36759601325176419084733367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24506400883450946056488911 36759601325176419084733367)
          ·
            refine ⟨55139401987764628627100051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36759601325176419084733367 55139401987764628627100051)
            ·
              refine ⟨82709102981646942940650077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55139401987764628627100051 82709102981646942940650077)
              ·
                refine ⟨31015913618117603602743779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82709102981646942940650077 31015913618117603602743779)
                ·
                  refine ⟨46523870427176405404115669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31015913618117603602743779 46523870427176405404115669)
                  ·
                    refine ⟨1090403213136947001658961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46523870427176405404115669 1090403213136947001658961)
                    ·
                      rfl

theorem cell23_6370658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_6370658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370658 prefixEnd_6370658 := by exact prefixLift 6370658
  have htrace : WordTrace (prefixWord ++ tailWord_6370658) baseStart_6370658 baseEnd_6370658 := by
    simpa [prefixWord, tailWord_6370658, baseEnd_6370658] using wordTrace_append hprefix tailTrace_6370658
  have hstable : (prefixWord ++ tailWord_6370658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370658).length < 2 ^ (prefixWord ++ tailWord_6370658).sum := by decide
  have hdescent : baseEnd_6370658 < baseStart_6370658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370712 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 2, 1, 4]
def baseStart_6370712 : Nat := 118140960795 + 6370712 * 2 ^ 59
def prefixEnd_6370712 : Nat := 4983230072969 + 3 ^ 40 * 6370712 * 2
def baseEnd_6370712 : Nat := 3271237367366183793701635

theorem tailTrace_6370712 : CollatzResearch.WordTrace tailWord_6370712 prefixEnd_6370712 3271237367366183793701635 := by
  unfold tailWord_6370712
  simp only [CollatzResearch.WordTrace]
  refine ⟨116179477848002964916069195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154905970464003953221425593 116179477848002964916069195)
  ·
    refine ⟨174269216772004447374103793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116179477848002964916069195 174269216772004447374103793)
    ·
      refine ⟨130701912579003335530577845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174269216772004447374103793 130701912579003335530577845)
      ·
        refine ⟨12253304304281562705991673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130701912579003335530577845 12253304304281562705991673)
        ·
          refine ⟨9189978228211172029493755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12253304304281562705991673 9189978228211172029493755)
          ·
            refine ⟨13784967342316758044240633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9189978228211172029493755 13784967342316758044240633)
            ·
              refine ⟨10338725506737568533180475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13784967342316758044240633 10338725506737568533180475)
              ·
                refine ⟨15508088260106352799770713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10338725506737568533180475 15508088260106352799770713)
                ·
                  refine ⟨11631066195079764599828035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15508088260106352799770713 11631066195079764599828035)
                  ·
                    refine ⟨17446599292619646899742053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11631066195079764599828035 17446599292619646899742053)
                    ·
                      refine ⟨3271237367366183793701635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17446599292619646899742053 3271237367366183793701635)
                      ·
                        rfl

theorem cell23_6370712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_6370712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370712 prefixEnd_6370712 := by exact prefixLift 6370712
  have htrace : WordTrace (prefixWord ++ tailWord_6370712) baseStart_6370712 baseEnd_6370712 := by
    simpa [prefixWord, tailWord_6370712, baseEnd_6370712] using wordTrace_append hprefix tailTrace_6370712
  have hstable : (prefixWord ++ tailWord_6370712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370712).length < 2 ^ (prefixWord ++ tailWord_6370712).sum := by decide
  have hdescent : baseEnd_6370712 < baseStart_6370712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370731 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 4, 9]
def baseStart_6370731 : Nat := 118140960795 + 6370731 * 2 ^ 59
def prefixEnd_6370731 : Nat := 4983230072969 + 3 ^ 40 * 6370731 * 2
def baseEnd_6370731 : Nat := 1090415707832873073121349

theorem tailTrace_6370731 : CollatzResearch.WordTrace tailWord_6370731 prefixEnd_6370731 1090415707832873073121349 := by
  unfold tailWord_6370731
  simp only [CollatzResearch.WordTrace]
  refine ⟨232359648682937096077080047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154906432455291397384720031 232359648682937096077080047)
  ·
    refine ⟨348539473024405644115620071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232359648682937096077080047 348539473024405644115620071)
    ·
      refine ⟨522809209536608466173430107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348539473024405644115620071 522809209536608466173430107)
      ·
        refine ⟨784213814304912699260145161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522809209536608466173430107 784213814304912699260145161)
        ·
          refine ⟨588160360728684524445108871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784213814304912699260145161 588160360728684524445108871)
          ·
            refine ⟨882240541093026786667663307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588160360728684524445108871 882240541093026786667663307)
            ·
              refine ⟨1323360811639540180001494961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882240541093026786667663307 1323360811639540180001494961)
              ·
                refine ⟨992520608729655135001121221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1323360811639540180001494961 992520608729655135001121221)
                ·
                  refine ⟨186097614136810337812710229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 992520608729655135001121221 186097614136810337812710229)
                  ·
                    refine ⟨1090415707832873073121349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 186097614136810337812710229 1090415707832873073121349)
                    ·
                      rfl

theorem cell23_6370731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 9].length) (baseStart_6370731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370731 prefixEnd_6370731 := by exact prefixLift 6370731
  have htrace : WordTrace (prefixWord ++ tailWord_6370731) baseStart_6370731 baseEnd_6370731 := by
    simpa [prefixWord, tailWord_6370731, baseEnd_6370731] using wordTrace_append hprefix tailTrace_6370731
  have hstable : (prefixWord ++ tailWord_6370731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370731).length < 2 ^ (prefixWord ++ tailWord_6370731).sum := by decide
  have hdescent : baseEnd_6370731 < baseStart_6370731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370755 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 4, 3, 2]
def baseStart_6370755 : Nat := 118140960795 + 6370755 * 2 ^ 59
def prefixEnd_6370755 : Nat := 4983230072969 + 3 ^ 40 * 6370755 * 2
def baseEnd_6370755 : Nat := 3271259447034327125463937

theorem tailTrace_6370755 : CollatzResearch.WordTrace tailWord_6370755 prefixEnd_6370755 3271259447034327125463937 := by
  unfold tailWord_6370755
  simp only [CollatzResearch.WordTrace]
  refine ⟨232360524034850148175953719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154907016023233432117302479 232360524034850148175953719)
  ·
    refine ⟨348540786052275222263930579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232360524034850148175953719 348540786052275222263930579)
    ·
      refine ⟨522811179078412833395895869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348540786052275222263930579 522811179078412833395895869)
      ·
        refine ⟨196054192154404812523460951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 522811179078412833395895869 196054192154404812523460951)
        ·
          refine ⟨294081288231607218785191427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196054192154404812523460951 294081288231607218785191427)
          ·
            refine ⟨441121932347410828177787141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294081288231607218785191427 441121932347410828177787141)
            ·
              refine ⟨82710362315139530283335089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 441121932347410828177787141 82710362315139530283335089)
              ·
                refine ⟨62032771736354647712501317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82710362315139530283335089 62032771736354647712501317)
                ·
                  refine ⟨11631144700566496446093997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62032771736354647712501317 11631144700566496446093997)
                  ·
                    refine ⟨4361679262712436167285249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11631144700566496446093997 4361679262712436167285249)
                    ·
                      refine ⟨3271259447034327125463937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361679262712436167285249 3271259447034327125463937)
                      ·
                        rfl

theorem cell23_6370755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 3, 2].length) (baseStart_6370755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370755 prefixEnd_6370755 := by exact prefixLift 6370755
  have htrace : WordTrace (prefixWord ++ tailWord_6370755) baseStart_6370755 baseEnd_6370755 := by
    simpa [prefixWord, tailWord_6370755, baseEnd_6370755] using wordTrace_append hprefix tailTrace_6370755
  have hstable : (prefixWord ++ tailWord_6370755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370755).length < 2 ^ (prefixWord ++ tailWord_6370755).sum := by decide
  have hdescent : baseEnd_6370755 < baseStart_6370755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370762 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 3, 1, 3]
def baseStart_6370762 : Nat := 118140960795 + 6370762 * 2 ^ 59
def prefixEnd_6370762 : Nat := 4983230072969 + 3 ^ 40 * 6370762 * 2
def baseEnd_6370762 : Nat := 3271263041398908598076405

theorem tailTrace_6370762 : CollatzResearch.WordTrace tailWord_6370762 prefixEnd_6370762 3271263041398908598076405 := by
  unfold tailWord_6370762
  simp only [CollatzResearch.WordTrace]
  refine ⟨58090194836456197092864635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154907186230549858914305693 58090194836456197092864635)
  ·
    refine ⟨87135292254684295639296953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58090194836456197092864635 87135292254684295639296953)
    ·
      refine ⟨65351469191013221729472715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87135292254684295639296953 65351469191013221729472715)
      ·
        refine ⟨98027203786519832594209073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65351469191013221729472715 98027203786519832594209073)
        ·
          refine ⟨73520402839889874445656805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98027203786519832594209073 73520402839889874445656805)
          ·
            refine ⟨13785075532479351458560651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73520402839889874445656805 13785075532479351458560651)
            ·
              refine ⟨20677613298719027187840977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13785075532479351458560651 20677613298719027187840977)
              ·
                refine ⟨15508209974039270390880733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20677613298719027187840977 15508209974039270390880733)
                ·
                  refine ⟨5815578740264726396580275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15508209974039270390880733 5815578740264726396580275)
                  ·
                    refine ⟨8723368110397089594870413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5815578740264726396580275 8723368110397089594870413)
                    ·
                      refine ⟨3271263041398908598076405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8723368110397089594870413 3271263041398908598076405)
                      ·
                        rfl

theorem cell23_6370762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_6370762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370762 prefixEnd_6370762 := by exact prefixLift 6370762
  have htrace : WordTrace (prefixWord ++ tailWord_6370762) baseStart_6370762 baseEnd_6370762 := by
    simpa [prefixWord, tailWord_6370762, baseEnd_6370762] using wordTrace_append hprefix tailTrace_6370762
  have hstable : (prefixWord ++ tailWord_6370762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370762).length < 2 ^ (prefixWord ++ tailWord_6370762).sum := by decide
  have hdescent : baseEnd_6370762 < baseStart_6370762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370788 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_6370788 : Nat := 118140960795 + 6370788 * 2 ^ 59
def prefixEnd_6370788 : Nat := 4983230072969 + 3 ^ 40 * 6370788 * 2
def baseEnd_6370788 : Nat := 3271276391895925496351285

theorem tailTrace_6370788 : CollatzResearch.WordTrace tailWord_6370788 prefixEnd_6370788 3271276391895925496351285 := by
  unfold tailWord_6370788
  simp only [CollatzResearch.WordTrace]
  refine ⟨116180863821865297405952509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154907818429153729874603345 116180863821865297405952509)
  ·
    refine ⟨43567823933199486527232191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116180863821865297405952509 43567823933199486527232191)
    ·
      refine ⟨65351735899799229790848287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43567823933199486527232191 65351735899799229790848287)
      ·
        refine ⟨98027603849698844686272431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65351735899799229790848287 98027603849698844686272431)
        ·
          refine ⟨147041405774548267029408647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98027603849698844686272431 147041405774548267029408647)
          ·
            refine ⟨220562108661822400544112971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147041405774548267029408647 220562108661822400544112971)
            ·
              refine ⟨330843162992733600816169457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220562108661822400544112971 330843162992733600816169457)
              ·
                refine ⟨248132372244550200612127093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330843162992733600816169457 248132372244550200612127093)
                ·
                  refine ⟨23262409897926581307386915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 248132372244550200612127093 23262409897926581307386915)
                  ·
                    refine ⟨34893614846889871961080373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23262409897926581307386915 34893614846889871961080373)
                    ·
                      refine ⟨3271276391895925496351285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34893614846889871961080373 3271276391895925496351285)
                      ·
                        rfl

theorem cell23_6370788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_6370788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370788 prefixEnd_6370788 := by exact prefixLift 6370788
  have htrace : WordTrace (prefixWord ++ tailWord_6370788) baseStart_6370788 baseEnd_6370788 := by
    simpa [prefixWord, tailWord_6370788, baseEnd_6370788] using wordTrace_append hprefix tailTrace_6370788
  have hstable : (prefixWord ++ tailWord_6370788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370788).length < 2 ^ (prefixWord ++ tailWord_6370788).sum := by decide
  have hdescent : baseEnd_6370788 < baseStart_6370788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370795 : List Nat := [1, 1, 1, 1, 2, 3, 2, 6, 2, 4]
def baseStart_6370795 : Nat := 118140960795 + 6370795 * 2 ^ 59
def prefixEnd_6370795 : Nat := 4983230072969 + 3 ^ 40 * 6370795 * 2
def baseEnd_6370795 : Nat := 1090426662086835656321251

theorem tailTrace_6370795 : CollatzResearch.WordTrace tailWord_6370795 prefixEnd_6370795 1090426662086835656321251 := by
  unfold tailWord_6370795
  simp only [CollatzResearch.WordTrace]
  refine ⟨232361982954705235007409839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154907988636470156671606559 232361982954705235007409839)
  ·
    refine ⟨348542974432057852511114759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232361982954705235007409839 348542974432057852511114759)
    ·
      refine ⟨522814461648086778766672139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348542974432057852511114759 522814461648086778766672139)
      ·
        refine ⟨784221692472130168150008209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522814461648086778766672139 784221692472130168150008209)
        ·
          refine ⟨588166269354097626112506157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784221692472130168150008209 588166269354097626112506157)
          ·
            refine ⟨220562351007786609792189809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 588166269354097626112506157 220562351007786609792189809)
            ·
              refine ⟨165421763255839957344142357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220562351007786609792189809 165421763255839957344142357)
              ·
                refine ⟨7754145152617498000506673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165421763255839957344142357 7754145152617498000506673)
                ·
                  refine ⟨5815608864463123500380005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7754145152617498000506673 5815608864463123500380005)
                  ·
                    refine ⟨1090426662086835656321251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5815608864463123500380005 1090426662086835656321251)
                    ·
                      rfl

theorem cell23_6370795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 4].length) (baseStart_6370795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370795 prefixEnd_6370795 := by exact prefixLift 6370795
  have htrace : WordTrace (prefixWord ++ tailWord_6370795) baseStart_6370795 baseEnd_6370795 := by
    simpa [prefixWord, tailWord_6370795, baseEnd_6370795] using wordTrace_append hprefix tailTrace_6370795
  have hstable : (prefixWord ++ tailWord_6370795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370795).length < 2 ^ (prefixWord ++ tailWord_6370795).sum := by decide
  have hdescent : baseEnd_6370795 < baseStart_6370795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370869 : List Nat := [1, 3, 3, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_6370869 : Nat := 118140960795 + 6370869 * 2 ^ 59
def prefixEnd_6370869 : Nat := 4983230072969 + 3 ^ 40 * 6370869 * 2
def baseEnd_6370869 : Nat := 3271317983828939679438413

theorem tailTrace_6370869 : CollatzResearch.WordTrace tailWord_6370869 prefixEnd_6370869 3271317983828939679438413 := by
  unfold tailWord_6370869
  simp only [CollatzResearch.WordTrace]
  refine ⟨232364681956437145645603661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154909787970958097097069107 232364681956437145645603661)
  ·
    refine ⟨87136755733663929617101373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232364681956437145645603661 87136755733663929617101373)
    ·
      refine ⟨32676283400123973606413015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87136755733663929617101373 32676283400123973606413015)
      ·
        refine ⟨49014425100185960409619523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32676283400123973606413015 49014425100185960409619523)
        ·
          refine ⟨73521637650278940614429285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49014425100185960409619523 73521637650278940614429285)
          ·
            refine ⟨13785307059427301365205491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73521637650278940614429285 13785307059427301365205491)
            ·
              refine ⟨20677960589140952047808237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13785307059427301365205491 20677960589140952047808237)
              ·
                refine ⟨7754235220927857017928089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20677960589140952047808237 7754235220927857017928089)
                ·
                  refine ⟨5815676415695892763446067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7754235220927857017928089 5815676415695892763446067)
                  ·
                    refine ⟨8723514623543839145169101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5815676415695892763446067 8723514623543839145169101)
                    ·
                      refine ⟨3271317983828939679438413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8723514623543839145169101 3271317983828939679438413)
                      ·
                        rfl

theorem cell23_6370869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_6370869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370869 prefixEnd_6370869 := by exact prefixLift 6370869
  have htrace : WordTrace (prefixWord ++ tailWord_6370869) baseStart_6370869 baseEnd_6370869 := by
    simpa [prefixWord, tailWord_6370869, baseEnd_6370869] using wordTrace_append hprefix tailTrace_6370869
  have hstable : (prefixWord ++ tailWord_6370869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370869).length < 2 ^ (prefixWord ++ tailWord_6370869).sum := by decide
  have hdescent : baseEnd_6370869 < baseStart_6370869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370875 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 1, 10, 2]
def baseStart_6370875 : Nat := 118140960795 + 6370875 * 2 ^ 59
def prefixEnd_6370875 : Nat := 4983230072969 + 3 ^ 40 * 6370875 * 2
def baseEnd_6370875 : Nat := 3271321064712866655963385

theorem tailTrace_6370875 : CollatzResearch.WordTrace tailWord_6370875 prefixEnd_6370875 3271321064712866655963385 := by
  unfold tailWord_6370875
  simp only [CollatzResearch.WordTrace]
  refine ⟨232364900794415408670322079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154909933862943605780214719 232364900794415408670322079)
  ·
    refine ⟨348547351191623113005483119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232364900794415408670322079 348547351191623113005483119)
    ·
      refine ⟨522821026787434669508224679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348547351191623113005483119 522821026787434669508224679)
      ·
        refine ⟨784231540181152004262337019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522821026787434669508224679 784231540181152004262337019)
        ·
          refine ⟨1176347310271728006393505529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784231540181152004262337019 1176347310271728006393505529)
          ·
            refine ⟨882260482703796004795129147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1176347310271728006393505529 882260482703796004795129147)
            ·
              refine ⟨1323390724055694007192693721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882260482703796004795129147 1323390724055694007192693721)
              ·
                refine ⟨992543043041770505394520291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1323390724055694007192693721 992543043041770505394520291)
                ·
                  refine ⟨1488814564562655758091780437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992543043041770505394520291 1488814564562655758091780437)
                  ·
                    refine ⟨4361761419617155541284513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1488814564562655758091780437 4361761419617155541284513)
                    ·
                      refine ⟨3271321064712866655963385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361761419617155541284513 3271321064712866655963385)
                      ·
                        rfl

theorem cell23_6370875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 10, 2].length) (baseStart_6370875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370875 prefixEnd_6370875 := by exact prefixLift 6370875
  have htrace : WordTrace (prefixWord ++ tailWord_6370875) baseStart_6370875 baseEnd_6370875 := by
    simpa [prefixWord, tailWord_6370875, baseEnd_6370875] using wordTrace_append hprefix tailTrace_6370875
  have hstable : (prefixWord ++ tailWord_6370875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370875).length < 2 ^ (prefixWord ++ tailWord_6370875).sum := by decide
  have hdescent : baseEnd_6370875 < baseStart_6370875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370879 : List Nat := [1, 1, 2, 2, 3, 3, 3, 2, 1, 3, 2]
def baseStart_6370879 : Nat := 118140960795 + 6370879 * 2 ^ 59
def prefixEnd_6370879 : Nat := 4983230072969 + 3 ^ 40 * 6370879 * 2
def baseEnd_6370879 : Nat := 3271323118635484640313367

theorem tailTrace_6370879 : CollatzResearch.WordTrace tailWord_6370879 prefixEnd_6370879 3271323118635484640313367 := by
  unfold tailWord_6370879
  simp only [CollatzResearch.WordTrace]
  refine ⟨232365046686400917353467691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154910031124267278235645127 232365046686400917353467691)
  ·
    refine ⟨348547570029601376030201537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232365046686400917353467691 348547570029601376030201537)
    ·
      refine ⟨261410677522201032022651153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348547570029601376030201537 261410677522201032022651153)
      ·
        refine ⟨196058008141650774016988365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261410677522201032022651153 196058008141650774016988365)
        ·
          refine ⟨73521753053119040256370637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196058008141650774016988365 73521753053119040256370637)
          ·
            refine ⟨27570657394919640096138989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73521753053119040256370637 27570657394919640096138989)
            ·
              refine ⟨10338996523094865036052121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27570657394919640096138989 10338996523094865036052121)
              ·
                refine ⟨7754247392321148777039091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10338996523094865036052121 7754247392321148777039091)
                ·
                  refine ⟨11631371088481723165558637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7754247392321148777039091 11631371088481723165558637)
                  ·
                    refine ⟨4361764158180646187084489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11631371088481723165558637 4361764158180646187084489)
                    ·
                      refine ⟨3271323118635484640313367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361764158180646187084489 3271323118635484640313367)
                      ·
                        rfl

theorem cell23_6370879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 3, 2].length) (baseStart_6370879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370879 prefixEnd_6370879 := by exact prefixLift 6370879
  have htrace : WordTrace (prefixWord ++ tailWord_6370879) baseStart_6370879 baseEnd_6370879 := by
    simpa [prefixWord, tailWord_6370879, baseEnd_6370879] using wordTrace_append hprefix tailTrace_6370879
  have hstable : (prefixWord ++ tailWord_6370879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370879).length < 2 ^ (prefixWord ++ tailWord_6370879).sum := by decide
  have hdescent : baseEnd_6370879 < baseStart_6370879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370886 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_6370886 : Nat := 118140960795 + 6370886 * 2 ^ 59
def prefixEnd_6370886 : Nat := 4983230072969 + 3 ^ 40 * 6370886 * 2
def baseEnd_6370886 : Nat := 3271326713000066112925835

theorem tailTrace_6370886 : CollatzResearch.WordTrace tailWord_6370886 prefixEnd_6370886 3271326713000066112925835 := by
  unfold tailWord_6370886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7261415687417986173405391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 154910201331583705032648341 7261415687417986173405391)
  ·
    refine ⟨10892123531126979260108087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7261415687417986173405391 10892123531126979260108087)
    ·
      refine ⟨16338185296690468890162131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10892123531126979260108087 16338185296690468890162131)
      ·
        refine ⟨24507277945035703335243197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16338185296690468890162131 24507277945035703335243197)
        ·
          refine ⟨9190229229388388750716199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24507277945035703335243197 9190229229388388750716199)
          ·
            refine ⟨13785343844082583126074299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9190229229388388750716199 13785343844082583126074299)
            ·
              refine ⟨20678015766123874689111449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13785343844082583126074299 20678015766123874689111449)
              ·
                refine ⟨15508511824592906016833587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20678015766123874689111449 15508511824592906016833587)
                ·
                  refine ⟨23262767736889359025250381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15508511824592906016833587 23262767736889359025250381)
                  ·
                    refine ⟨8723537901333509634468893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23262767736889359025250381 8723537901333509634468893)
                    ·
                      refine ⟨3271326713000066112925835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8723537901333509634468893 3271326713000066112925835)
                      ·
                        rfl

theorem cell23_6370886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_6370886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370886 prefixEnd_6370886 := by exact prefixLift 6370886
  have htrace : WordTrace (prefixWord ++ tailWord_6370886) baseStart_6370886 baseEnd_6370886 := by
    simpa [prefixWord, tailWord_6370886, baseEnd_6370886] using wordTrace_append hprefix tailTrace_6370886
  have hstable : (prefixWord ++ tailWord_6370886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370886).length < 2 ^ (prefixWord ++ tailWord_6370886).sum := by decide
  have hdescent : baseEnd_6370886 < baseStart_6370886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370892 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 3, 4, 2]
def baseStart_6370892 : Nat := 118140960795 + 6370892 * 2 ^ 59
def prefixEnd_6370892 : Nat := 4983230072969 + 3 ^ 40 * 6370892 * 2
def baseEnd_6370892 : Nat := 3271329793883993089450807

theorem tailTrace_6370892 : CollatzResearch.WordTrace tailWord_6370892 prefixEnd_6370892 3271329793883993089450807 := by
  unfold tailWord_6370892
  simp only [CollatzResearch.WordTrace]
  refine ⟨116182760417676910286845465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154910347223569213715793953 116182760417676910286845465)
  ·
    refine ⟨87137070313257682715134099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116182760417676910286845465 87137070313257682715134099)
    ·
      refine ⟨130705605469886524072701149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87137070313257682715134099 130705605469886524072701149)
      ·
        refine ⟨49014602051207446527262931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130705605469886524072701149 49014602051207446527262931)
        ·
          refine ⟨73521903076811169790894397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49014602051207446527262931 73521903076811169790894397)
          ·
            refine ⟨27570713653804188671585399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73521903076811169790894397 27570713653804188671585399)
            ·
              refine ⟨41356070480706283007378099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27570713653804188671585399 41356070480706283007378099)
              ·
                refine ⟨62034105721059424511067149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41356070480706283007378099 62034105721059424511067149)
                ·
                  refine ⟨23262789645397284191650181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62034105721059424511067149 23262789645397284191650181)
                  ·
                    refine ⟨4361773058511990785934409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23262789645397284191650181 4361773058511990785934409)
                    ·
                      refine ⟨3271329793883993089450807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361773058511990785934409 3271329793883993089450807)
                      ·
                        rfl

theorem cell23_6370892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_6370892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370892 prefixEnd_6370892 := by exact prefixLift 6370892
  have htrace : WordTrace (prefixWord ++ tailWord_6370892) baseStart_6370892 baseEnd_6370892 := by
    simpa [prefixWord, tailWord_6370892, baseEnd_6370892] using wordTrace_append hprefix tailTrace_6370892
  have hstable : (prefixWord ++ tailWord_6370892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370892).length < 2 ^ (prefixWord ++ tailWord_6370892).sum := by decide
  have hdescent : baseEnd_6370892 < baseStart_6370892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370922 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_6370922 : Nat := 118140960795 + 6370922 * 2 ^ 59
def prefixEnd_6370922 : Nat := 4983230072969 + 3 ^ 40 * 6370922 * 2
def baseEnd_6370922 : Nat := 3271345198303627972075669

theorem tailTrace_6370922 : CollatzResearch.WordTrace tailWord_6370922 prefixEnd_6370922 3271345198303627972075669 := by
  unfold tailWord_6370922
  simp only [CollatzResearch.WordTrace]
  refine ⟨58091653756311283924320755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154911076683496757131522013 58091653756311283924320755)
  ·
    refine ⟨87137480634466925886481133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58091653756311283924320755 87137480634466925886481133)
    ·
      refine ⟨32676555237925097207430425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87137480634466925886481133 32676555237925097207430425)
      ·
        refine ⟨24507416428443822905572819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32676555237925097207430425 24507416428443822905572819)
        ·
          refine ⟨36761124642665734358359229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24507416428443822905572819 36761124642665734358359229)
          ·
            refine ⟨13785421740999650384384711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36761124642665734358359229 13785421740999650384384711)
            ·
              refine ⟨20678132611499475576577067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13785421740999650384384711 20678132611499475576577067)
              ·
                refine ⟨31017198917249213364865601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20678132611499475576577067 31017198917249213364865601)
                ·
                  refine ⟨23262899187936910023649201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31017198917249213364865601 23262899187936910023649201)
                  ·
                    refine ⟨17447174390952682517736901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23262899187936910023649201 17447174390952682517736901)
                    ·
                      refine ⟨3271345198303627972075669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17447174390952682517736901 3271345198303627972075669)
                      ·
                        rfl

theorem cell23_6370922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_6370922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370922 prefixEnd_6370922 := by exact prefixLift 6370922
  have htrace : WordTrace (prefixWord ++ tailWord_6370922) baseStart_6370922 baseEnd_6370922 := by
    simpa [prefixWord, tailWord_6370922, baseEnd_6370922] using wordTrace_append hprefix tailTrace_6370922
  have hstable : (prefixWord ++ tailWord_6370922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370922).length < 2 ^ (prefixWord ++ tailWord_6370922).sum := by decide
  have hdescent : baseEnd_6370922 < baseStart_6370922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370926 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_6370926 : Nat := 118140960795 + 6370926 * 2 ^ 59
def prefixEnd_6370926 : Nat := 4983230072969 + 3 ^ 40 * 6370926 * 2
def baseEnd_6370926 : Nat := 3271347252226245956425651

theorem tailTrace_6370926 : CollatzResearch.WordTrace tailWord_6370926 prefixEnd_6370926 3271347252226245956425651 := by
  unfold tailWord_6370926
  simp only [CollatzResearch.WordTrace]
  refine ⟨29045845114653830547553579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154911173944820429586952421 29045845114653830547553579)
  ·
    refine ⟨43568767671980745821330369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29045845114653830547553579 43568767671980745821330369)
    ·
      refine ⟨32676575753985559365997777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43568767671980745821330369 32676575753985559365997777)
      ·
        refine ⟨24507431815489169524498333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32676575753985559365997777 24507431815489169524498333)
        ·
          refine ⟨9190286930808438571686875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24507431815489169524498333 9190286930808438571686875)
          ·
            refine ⟨13785430396212657857530313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9190286930808438571686875 13785430396212657857530313)
            ·
              refine ⟨10339072797159493393147735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13785430396212657857530313 10339072797159493393147735)
              ·
                refine ⟨15508609195739240089721603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10339072797159493393147735 15508609195739240089721603)
                ·
                  refine ⟨23262913793608860134582405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15508609195739240089721603 23262913793608860134582405)
                  ·
                    refine ⟨4361796336301661275234201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23262913793608860134582405 4361796336301661275234201)
                    ·
                      refine ⟨3271347252226245956425651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361796336301661275234201 3271347252226245956425651)
                      ·
                        rfl

theorem cell23_6370926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_6370926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370926 prefixEnd_6370926 := by exact prefixLift 6370926
  have htrace : WordTrace (prefixWord ++ tailWord_6370926) baseStart_6370926 baseEnd_6370926 := by
    simpa [prefixWord, tailWord_6370926, baseEnd_6370926] using wordTrace_append hprefix tailTrace_6370926
  have hstable : (prefixWord ++ tailWord_6370926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370926).length < 2 ^ (prefixWord ++ tailWord_6370926).sum := by decide
  have hdescent : baseEnd_6370926 < baseStart_6370926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370992 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 3, 4]
def baseStart_6370992 : Nat := 118140960795 + 6370992 * 2 ^ 59
def prefixEnd_6370992 : Nat := 4983230072969 + 3 ^ 40 * 6370992 * 2
def baseEnd_6370992 : Nat := 1090460380649814232733449

theorem tailTrace_6370992 : CollatzResearch.WordTrace tailWord_6370992 prefixEnd_6370992 1090460380649814232733449 := by
  unfold tailWord_6370992
  simp only [CollatzResearch.WordTrace]
  refine ⟨116184584067495768826165615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154912778756661025101554153 116184584067495768826165615)
  ·
    refine ⟨174276876101243653239248423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116184584067495768826165615 174276876101243653239248423)
    ·
      refine ⟨261415314151865479858872635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174276876101243653239248423 261415314151865479858872635)
      ·
        refine ⟨392122971227798219788308953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261415314151865479858872635 392122971227798219788308953)
        ·
          refine ⟨294092228420848664841231715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392122971227798219788308953 294092228420848664841231715)
          ·
            refine ⟨441138342631272997261847573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294092228420848664841231715 441138342631272997261847573)
            ·
              refine ⟨20678359810840921746649105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 441138342631272997261847573 20678359810840921746649105)
              ·
                refine ⟨15508769858130691309986829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20678359810840921746649105 15508769858130691309986829)
                ·
                  refine ⟨5815788696799009241245061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15508769858130691309986829 5815788696799009241245061)
                  ·
                    refine ⟨1090460380649814232733449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5815788696799009241245061 1090460380649814232733449)
                    ·
                      rfl

theorem cell23_6370992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 3, 4].length) (baseStart_6370992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370992 prefixEnd_6370992 := by exact prefixLift 6370992
  have htrace : WordTrace (prefixWord ++ tailWord_6370992) baseStart_6370992 baseEnd_6370992 := by
    simpa [prefixWord, tailWord_6370992, baseEnd_6370992] using wordTrace_append hprefix tailTrace_6370992
  have hstable : (prefixWord ++ tailWord_6370992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370992).length < 2 ^ (prefixWord ++ tailWord_6370992).sum := by decide
  have hdescent : baseEnd_6370992 < baseStart_6370992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370995 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 4]
def baseStart_6370995 : Nat := 118140960795 + 6370995 * 2 ^ 59
def prefixEnd_6370995 : Nat := 4983230072969 + 3 ^ 40 * 6370995 * 2
def baseEnd_6370995 : Nat := 3271382682391406186462833

theorem tailTrace_6370995 : CollatzResearch.WordTrace tailWord_6370995 prefixEnd_6370995 3271382682391406186462833 := by
  unfold tailWord_6370995
  simp only [CollatzResearch.WordTrace]
  refine ⟨232369277553980669164690439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154912851702653779443126959 232369277553980669164690439)
  ·
    refine ⟨348553916330971003747035659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232369277553980669164690439 348553916330971003747035659)
    ·
      refine ⟨522830874496456505620553489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348553916330971003747035659 522830874496456505620553489)
      ·
        refine ⟨392123155872342379215415117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522830874496456505620553489 392123155872342379215415117)
        ·
          refine ⟨147046183452128392205780669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392123155872342379215415117 147046183452128392205780669)
          ·
            refine ⟨55142318794548147077167751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147046183452128392205780669 55142318794548147077167751)
            ·
              refine ⟨82713478191822220615751627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55142318794548147077167751 82713478191822220615751627)
              ·
                refine ⟨124070217287733330923627441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82713478191822220615751627 124070217287733330923627441)
                ·
                  refine ⟨93052662965799998192720581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124070217287733330923627441 93052662965799998192720581)
                  ·
                    refine ⟨17447374306087499661135109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93052662965799998192720581 17447374306087499661135109)
                    ·
                      refine ⟨3271382682391406186462833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17447374306087499661135109 3271382682391406186462833)
                      ·
                        rfl

theorem cell23_6370995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_6370995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6370995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6370995 prefixEnd_6370995 := by exact prefixLift 6370995
  have htrace : WordTrace (prefixWord ++ tailWord_6370995) baseStart_6370995 baseEnd_6370995 := by
    simpa [prefixWord, tailWord_6370995, baseEnd_6370995] using wordTrace_append hprefix tailTrace_6370995
  have hstable : (prefixWord ++ tailWord_6370995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370995).length < 2 ^ (prefixWord ++ tailWord_6370995).sum := by decide
  have hdescent : baseEnd_6370995 < baseStart_6370995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371002 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3]
def baseStart_6371002 : Nat := 118140960795 + 6371002 * 2 ^ 59
def prefixEnd_6371002 : Nat := 4983230072969 + 3 ^ 40 * 6371002 * 2
def baseEnd_6371002 : Nat := 3271386276755987659075301

theorem tailTrace_6371002 : CollatzResearch.WordTrace tailWord_6371002 prefixEnd_6371002 3271386276755987659075301 := by
  unfold tailWord_6371002
  simp only [CollatzResearch.WordTrace]
  refine ⟨58092383216238827340048815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154913021909970206240130173 58092383216238827340048815)
  ·
    refine ⟨87138574824358241010073223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58092383216238827340048815 87138574824358241010073223)
    ·
      refine ⟨130707862236537361515109835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87138574824358241010073223 130707862236537361515109835)
      ·
        refine ⟨196061793354806042272664753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130707862236537361515109835 196061793354806042272664753)
        ·
          refine ⟨147046345016104531704498565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196061793354806042272664753 147046345016104531704498565)
          ·
            refine ⟨27571189690519599694593481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147046345016104531704498565 27571189690519599694593481)
            ·
              refine ⟨20678392267889699770945111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27571189690519599694593481 20678392267889699770945111)
              ·
                refine ⟨31017588401834549656417667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20678392267889699770945111 31017588401834549656417667)
                ·
                  refine ⟨46526382602751824484626501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31017588401834549656417667 46526382602751824484626501)
                  ·
                    refine ⟨8723696738015967090867469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46526382602751824484626501 8723696738015967090867469)
                    ·
                      refine ⟨3271386276755987659075301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8723696738015967090867469 3271386276755987659075301)
                      ·
                        rfl

theorem cell23_6371002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_6371002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371002 prefixEnd_6371002 := by exact prefixLift 6371002
  have htrace : WordTrace (prefixWord ++ tailWord_6371002) baseStart_6371002 baseEnd_6371002 := by
    simpa [prefixWord, tailWord_6371002, baseEnd_6371002] using wordTrace_append hprefix tailTrace_6371002
  have hstable : (prefixWord ++ tailWord_6371002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371002).length < 2 ^ (prefixWord ++ tailWord_6371002).sum := by decide
  have hdescent : baseEnd_6371002 < baseStart_6371002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371005 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 10]
def baseStart_6371005 : Nat := 118140960795 + 6371005 * 2 ^ 59
def prefixEnd_6371005 : Nat := 4983230072969 + 3 ^ 40 * 6371005 * 2
def baseEnd_6371005 : Nat := 363487535244216794148643

theorem tailTrace_6371005 : CollatzResearch.WordTrace tailWord_6371005 prefixEnd_6371005 363487535244216794148643 := by
  unfold tailWord_6371005
  simp only [CollatzResearch.WordTrace]
  refine ⟨232369642283944440872554469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154913094855962960581702979 232369642283944440872554469)
  ·
    refine ⟨43569307928239582663603963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232369642283944440872554469 43569307928239582663603963)
    ·
      refine ⟨65353961892359373995405945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43569307928239582663603963 65353961892359373995405945)
      ·
        refine ⟨49015471419269530496554459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65353961892359373995405945 49015471419269530496554459)
        ·
          refine ⟨73523207128904295744831689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49015471419269530496554459 73523207128904295744831689)
          ·
            refine ⟨55142405346678221808623767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73523207128904295744831689 55142405346678221808623767)
            ·
              refine ⟨82713608020017332712935651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55142405346678221808623767 82713608020017332712935651)
              ·
                refine ⟨124070412030025999069403477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82713608020017332712935651 124070412030025999069403477)
                ·
                  refine ⟨363487535244216794148643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 124070412030025999069403477 363487535244216794148643)
                  ·
                    rfl

theorem cell23_6371005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_6371005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371005 prefixEnd_6371005 := by exact prefixLift 6371005
  have htrace : WordTrace (prefixWord ++ tailWord_6371005) baseStart_6371005 baseEnd_6371005 := by
    simpa [prefixWord, tailWord_6371005, baseEnd_6371005] using wordTrace_append hprefix tailTrace_6371005
  have hstable : (prefixWord ++ tailWord_6371005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371005).length < 2 ^ (prefixWord ++ tailWord_6371005).sum := by decide
  have hdescent : baseEnd_6371005 < baseStart_6371005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371022 : List Nat := [4, 1, 1, 1, 3, 1, 2, 4, 6]
def baseStart_6371022 : Nat := 118140960795 + 6371022 * 2 ^ 59
def prefixEnd_6371022 : Nat := 4983230072969 + 3 ^ 40 * 6371022 * 2
def baseEnd_6371022 : Nat := 363488505152119731202801

theorem tailTrace_6371022 : CollatzResearch.WordTrace tailWord_6371022 prefixEnd_6371022 363488505152119731202801 := by
  unfold tailWord_6371022
  simp only [CollatzResearch.WordTrace]
  refine ⟨29046282790610356596990415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154913508216588568517282213 29046282790610356596990415)
  ·
    refine ⟨43569424185915534895485623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29046282790610356596990415 43569424185915534895485623)
    ·
      refine ⟨65354136278873302343228435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43569424185915534895485623 65354136278873302343228435)
      ·
        refine ⟨98031204418309953514842653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65354136278873302343228435 98031204418309953514842653)
        ·
          refine ⟨36761701656866232568065995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98031204418309953514842653 36761701656866232568065995)
          ·
            refine ⟨55142552485299348852098993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36761701656866232568065995 55142552485299348852098993)
            ·
              refine ⟨41356914363974511639074245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55142552485299348852098993 41356914363974511639074245)
              ·
                refine ⟨7754421443245220932326421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41356914363974511639074245 7754421443245220932326421)
                ·
                  refine ⟨363488505152119731202801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7754421443245220932326421 363488505152119731202801)
                  ·
                    rfl

theorem cell23_6371022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_6371022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371022 prefixEnd_6371022 := by exact prefixLift 6371022
  have htrace : WordTrace (prefixWord ++ tailWord_6371022) baseStart_6371022 baseEnd_6371022 := by
    simpa [prefixWord, tailWord_6371022, baseEnd_6371022] using wordTrace_append hprefix tailTrace_6371022
  have hstable : (prefixWord ++ tailWord_6371022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371022).length < 2 ^ (prefixWord ++ tailWord_6371022).sum := by decide
  have hdescent : baseEnd_6371022 < baseStart_6371022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371026 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_6371026 : Nat := 118140960795 + 6371026 * 2 ^ 59
def prefixEnd_6371026 : Nat := 4983230072969 + 3 ^ 40 * 6371026 * 2
def baseEnd_6371026 : Nat := 1090466200097231855058397

theorem tailTrace_6371026 : CollatzResearch.WordTrace tailWord_6371026 prefixEnd_6371026 1090466200097231855058397 := by
  unfold tailWord_6371026
  simp only [CollatzResearch.WordTrace]
  refine ⟨58092602054217090364767233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154913605477912240972712621 58092602054217090364767233)
  ·
    refine ⟨43569451540662817773575425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58092602054217090364767233 43569451540662817773575425)
    ·
      refine ⟨32677088655497113330181569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43569451540662817773575425 32677088655497113330181569)
      ·
        refine ⟨24507816491622834997636177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32677088655497113330181569 24507816491622834997636177)
        ·
          refine ⟨18380862368717126248227133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24507816491622834997636177 18380862368717126248227133)
          ·
            refine ⟨6892823388268922343085175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18380862368717126248227133 6892823388268922343085175)
            ·
              refine ⟨10339235082403383514627763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6892823388268922343085175 10339235082403383514627763)
              ·
                refine ⟨15508852623605075271941645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10339235082403383514627763 15508852623605075271941645)
                ·
                  refine ⟨5815819733851903226978117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15508852623605075271941645 5815819733851903226978117)
                  ·
                    refine ⟨1090466200097231855058397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5815819733851903226978117 1090466200097231855058397)
                    ·
                      rfl

theorem cell23_6371026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_6371026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371026 prefixEnd_6371026 := by exact prefixLift 6371026
  have htrace : WordTrace (prefixWord ++ tailWord_6371026) baseStart_6371026 baseEnd_6371026 := by
    simpa [prefixWord, tailWord_6371026, baseEnd_6371026] using wordTrace_append hprefix tailTrace_6371026
  have hstable : (prefixWord ++ tailWord_6371026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371026).length < 2 ^ (prefixWord ++ tailWord_6371026).sum := by decide
  have hdescent : baseEnd_6371026 < baseStart_6371026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371059 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 2, 3, 2]
def baseStart_6371059 : Nat := 118140960795 + 6371059 * 2 ^ 59
def prefixEnd_6371059 : Nat := 4983230072969 + 3 ^ 40 * 6371059 * 2
def baseEnd_6371059 : Nat := 3271415545153293936062539

theorem tailTrace_6371059 : CollatzResearch.WordTrace tailWord_6371059 prefixEnd_6371059 3271415545153293936062539 := by
  unfold tailWord_6371059
  simp only [CollatzResearch.WordTrace]
  refine ⟨232371611825748808095020231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154914407883832538730013487 232371611825748808095020231)
  ·
    refine ⟨348557417738623212142530347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232371611825748808095020231 348557417738623212142530347)
    ·
      refine ⟨522836126607934818213795521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348557417738623212142530347 522836126607934818213795521)
      ·
        refine ⟨392127094955951113660346641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522836126607934818213795521 392127094955951113660346641)
        ·
          refine ⟨294095321216963335245259981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392127094955951113660346641 294095321216963335245259981)
          ·
            refine ⟨110285745456361250716972493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294095321216963335245259981 110285745456361250716972493)
            ·
              refine ⟨41357154546135469018864685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110285745456361250716972493 41357154546135469018864685)
              ·
                refine ⟨15508932954800800882074257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41357154546135469018864685 15508932954800800882074257)
                ·
                  refine ⟨11631699716100600661555693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15508932954800800882074257 11631699716100600661555693)
                  ·
                    refine ⟨4361887393537725248083385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11631699716100600661555693 4361887393537725248083385)
                    ·
                      refine ⟨3271415545153293936062539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361887393537725248083385 3271415545153293936062539)
                      ·
                        rfl

theorem cell23_6371059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 3, 2].length) (baseStart_6371059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371059 prefixEnd_6371059 := by exact prefixLift 6371059
  have htrace : WordTrace (prefixWord ++ tailWord_6371059) baseStart_6371059 baseEnd_6371059 := by
    simpa [prefixWord, tailWord_6371059, baseEnd_6371059] using wordTrace_append hprefix tailTrace_6371059
  have hstable : (prefixWord ++ tailWord_6371059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371059).length < 2 ^ (prefixWord ++ tailWord_6371059).sum := by decide
  have hdescent : baseEnd_6371059 < baseStart_6371059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371066 : List Nat := [3, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3]
def baseStart_6371066 : Nat := 118140960795 + 6371066 * 2 ^ 59
def prefixEnd_6371066 : Nat := 4983230072969 + 3 ^ 40 * 6371066 * 2
def baseEnd_6371066 : Nat := 3271419139517875408675007

theorem tailTrace_6371066 : CollatzResearch.WordTrace tailWord_6371066 prefixEnd_6371066 3271419139517875408675007 := by
  unfold tailWord_6371066
  simp only [CollatzResearch.WordTrace]
  refine ⟨58092966784180862072631263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154914578091148965527016701 58092966784180862072631263)
  ·
    refine ⟨87139450176271293108946895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58092966784180862072631263 87139450176271293108946895)
    ·
      refine ⟨130709175264406939663420343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87139450176271293108946895 130709175264406939663420343)
      ·
        refine ⟨196063762896610409495130515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130709175264406939663420343 196063762896610409495130515)
        ·
          refine ⟨294095644344915614242695773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196063762896610409495130515 294095644344915614242695773)
          ·
            refine ⟨110285866629343355341010915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294095644344915614242695773 110285866629343355341010915)
            ·
              refine ⟨165428799944015033011516373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110285866629343355341010915 165428799944015033011516373)
              ·
                refine ⟨3877237498687852336207415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 165428799944015033011516373 3877237498687852336207415)
                ·
                  refine ⟨5815856248031778504311123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877237498687852336207415 5815856248031778504311123)
                  ·
                    refine ⟨8723784372047667756466685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5815856248031778504311123 8723784372047667756466685)
                    ·
                      refine ⟨3271419139517875408675007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8723784372047667756466685 3271419139517875408675007)
                      ·
                        rfl

theorem cell23_6371066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3].length) (baseStart_6371066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371066 prefixEnd_6371066 := by exact prefixLift 6371066
  have htrace : WordTrace (prefixWord ++ tailWord_6371066) baseStart_6371066 baseEnd_6371066 := by
    simpa [prefixWord, tailWord_6371066, baseEnd_6371066] using wordTrace_append hprefix tailTrace_6371066
  have hstable : (prefixWord ++ tailWord_6371066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371066).length < 2 ^ (prefixWord ++ tailWord_6371066).sum := by decide
  have hdescent : baseEnd_6371066 < baseStart_6371066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371076 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_6371076 : Nat := 118140960795 + 6371076 * 2 ^ 59
def prefixEnd_6371076 : Nat := 4983230072969 + 3 ^ 40 * 6371076 * 2
def baseEnd_6371076 : Nat := 3271424274324420369549961

theorem tailTrace_6371076 : CollatzResearch.WordTrace tailWord_6371076 prefixEnd_6371076 3271424274324420369549961 := by
  unfold tailWord_6371076
  simp only [CollatzResearch.WordTrace]
  refine ⟨116186115933343609999194541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154914821244458146665592721 116186115933343609999194541)
  ·
    refine ⟨43569793475003853749697953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116186115933343609999194541 43569793475003853749697953)
    ·
      refine ⟨32677345106252890312273465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43569793475003853749697953 32677345106252890312273465)
      ·
        refine ⟨24508008829689667734205099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32677345106252890312273465 24508008829689667734205099)
        ·
          refine ⟨36762013244534501601307649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24508008829689667734205099 36762013244534501601307649)
          ·
            refine ⟨27571509933400876200980737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36762013244534501601307649 27571509933400876200980737)
            ·
              refine ⟨20678632450050657150735553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27571509933400876200980737 20678632450050657150735553)
              ·
                refine ⟨15508974337537992863051665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20678632450050657150735553 15508974337537992863051665)
                ·
                  refine ⟨11631730753153494647288749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15508974337537992863051665 11631730753153494647288749)
                  ·
                    refine ⟨4361899032432560492733281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11631730753153494647288749 4361899032432560492733281)
                    ·
                      refine ⟨3271424274324420369549961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361899032432560492733281 3271424274324420369549961)
                      ·
                        rfl

theorem cell23_6371076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_6371076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371076 prefixEnd_6371076 := by exact prefixLift 6371076
  have htrace : WordTrace (prefixWord ++ tailWord_6371076) baseStart_6371076 baseEnd_6371076 := by
    simpa [prefixWord, tailWord_6371076, baseEnd_6371076] using wordTrace_append hprefix tailTrace_6371076
  have hstable : (prefixWord ++ tailWord_6371076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371076).length < 2 ^ (prefixWord ++ tailWord_6371076).sum := by decide
  have hdescent : baseEnd_6371076 < baseStart_6371076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371083 : List Nat := [1, 1, 1, 1, 5, 1, 6, 2, 1, 1, 3]
def baseStart_6371083 : Nat := 118140960795 + 6371083 * 2 ^ 59
def prefixEnd_6371083 : Nat := 4983230072969 + 3 ^ 40 * 6371083 * 2
def baseEnd_6371083 : Nat := 3271427868689001842162429

theorem tailTrace_6371083 : CollatzResearch.WordTrace tailWord_6371083 prefixEnd_6371083 3271427868689001842162429 := by
  unfold tailWord_6371083
  simp only [CollatzResearch.WordTrace]
  refine ⟨232372487177661860193893903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154914991451774573462595935 232372487177661860193893903)
  ·
    refine ⟨348558730766492790290840855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232372487177661860193893903 348558730766492790290840855)
    ·
      refine ⟨522838096149739185436261283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348558730766492790290840855 522838096149739185436261283)
      ·
        refine ⟨784257144224608778154391925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522838096149739185436261283 784257144224608778154391925)
        ·
          refine ⟨73524107271057072951974243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 784257144224608778154391925 73524107271057072951974243)
          ·
            refine ⟨110286160906585609427961365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73524107271057072951974243 110286160906585609427961365)
            ·
              refine ⟨5169663792496200441935689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110286160906585609427961365 5169663792496200441935689)
              ·
                refine ⟨3877247844372150331451767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5169663792496200441935689 3877247844372150331451767)
                ·
                  refine ⟨5815871766558225497177651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877247844372150331451767 5815871766558225497177651)
                  ·
                    refine ⟨8723807649837338245766477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5815871766558225497177651 8723807649837338245766477)
                    ·
                      refine ⟨3271427868689001842162429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8723807649837338245766477 3271427868689001842162429)
                      ·
                        rfl

theorem cell23_6371083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 1, 1, 3].length) (baseStart_6371083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371083 prefixEnd_6371083 := by exact prefixLift 6371083
  have htrace : WordTrace (prefixWord ++ tailWord_6371083) baseStart_6371083 baseEnd_6371083 := by
    simpa [prefixWord, tailWord_6371083, baseEnd_6371083] using wordTrace_append hprefix tailTrace_6371083
  have hstable : (prefixWord ++ tailWord_6371083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371083).length < 2 ^ (prefixWord ++ tailWord_6371083).sum := by decide
  have hdescent : baseEnd_6371083 < baseStart_6371083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371109 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 3, 2, 3]
def baseStart_6371109 : Nat := 118140960795 + 6371109 * 2 ^ 59
def prefixEnd_6371109 : Nat := 4983230072969 + 3 ^ 40 * 6371109 * 2
def baseEnd_6371109 : Nat := 3271441219186018740437309

theorem tailTrace_6371109 : CollatzResearch.WordTrace tailWord_6371109 prefixEnd_6371109 3271441219186018740437309 := by
  unfold tailWord_6371109
  simp only [CollatzResearch.WordTrace]
  refine ⟨232373435475567666634340381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154915623650378444422893587 232373435475567666634340381)
  ·
    refine ⟨87140038303337874987877643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232373435475567666634340381 87140038303337874987877643)
    ·
      refine ⟨130710057455006812481816465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87140038303337874987877643 130710057455006812481816465)
      ·
        refine ⟨98032543091255109361362349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130710057455006812481816465 98032543091255109361362349)
        ·
          refine ⟨36762203659220666010510881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98032543091255109361362349 36762203659220666010510881)
          ·
            refine ⟨27571652744415499507883161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36762203659220666010510881 27571652744415499507883161)
            ·
              refine ⟨20678739558311624630912371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27571652744415499507883161 20678739558311624630912371)
              ·
                refine ⟨31018109337467436946368557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20678739558311624630912371 31018109337467436946368557)
                ·
                  refine ⟨11631791001550288854888209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31018109337467436946368557 11631791001550288854888209)
                  ·
                    refine ⟨8723843251162716641166157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11631791001550288854888209 8723843251162716641166157)
                    ·
                      refine ⟨3271441219186018740437309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8723843251162716641166157 3271441219186018740437309)
                      ·
                        rfl

theorem cell23_6371109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_6371109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371109 prefixEnd_6371109 := by exact prefixLift 6371109
  have htrace : WordTrace (prefixWord ++ tailWord_6371109) baseStart_6371109 baseEnd_6371109 := by
    simpa [prefixWord, tailWord_6371109, baseEnd_6371109] using wordTrace_append hprefix tailTrace_6371109
  have hstable : (prefixWord ++ tailWord_6371109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371109).length < 2 ^ (prefixWord ++ tailWord_6371109).sum := by decide
  have hdescent : baseEnd_6371109 < baseStart_6371109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371123 : List Nat := [1, 1, 1, 2, 7, 2, 2, 1, 1, 1, 4]
def baseStart_6371123 : Nat := 118140960795 + 6371123 * 2 ^ 59
def prefixEnd_6371123 : Nat := 4983230072969 + 3 ^ 40 * 6371123 * 2
def baseEnd_6371123 : Nat := 3271448407915181685662245

theorem tailTrace_6371123 : CollatzResearch.WordTrace tailWord_6371123 prefixEnd_6371123 3271448407915181685662245 := by
  unfold tailWord_6371123
  simp only [CollatzResearch.WordTrace]
  refine ⟨232373946097516947025350023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154915964065011298016900015 232373946097516947025350023)
  ·
    refine ⟨348560919146275420538025035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232373946097516947025350023 348560919146275420538025035)
    ·
      refine ⟨522841378719413130807037553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348560919146275420538025035 522841378719413130807037553)
      ·
        refine ⟨392131034039559848105278165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522841378719413130807037553 392131034039559848105278165)
        ·
          refine ⟨9190571110302183939967457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 392131034039559848105278165 9190571110302183939967457)
          ·
            refine ⟨6892928332726637954975593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9190571110302183939967457 6892928332726637954975593)
            ·
              refine ⟨5169696249544978466231695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6892928332726637954975593 5169696249544978466231695)
              ·
                refine ⟨7754544374317467699347543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5169696249544978466231695 7754544374317467699347543)
                ·
                  refine ⟨11631816561476201549021315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7754544374317467699347543 11631816561476201549021315)
                  ·
                    refine ⟨17447724842214302323531973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11631816561476201549021315 17447724842214302323531973)
                    ·
                      refine ⟨3271448407915181685662245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17447724842214302323531973 3271448407915181685662245)
                      ·
                        rfl

theorem cell23_6371123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 1, 1, 4].length) (baseStart_6371123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371123 prefixEnd_6371123 := by exact prefixLift 6371123
  have htrace : WordTrace (prefixWord ++ tailWord_6371123) baseStart_6371123 baseEnd_6371123 := by
    simpa [prefixWord, tailWord_6371123, baseEnd_6371123] using wordTrace_append hprefix tailTrace_6371123
  have hstable : (prefixWord ++ tailWord_6371123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371123).length < 2 ^ (prefixWord ++ tailWord_6371123).sum := by decide
  have hdescent : baseEnd_6371123 < baseStart_6371123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371129 : List Nat := [1, 2, 1, 7, 1, 1, 10]
def baseStart_6371129 : Nat := 118140960795 + 6371129 * 2 ^ 59
def prefixEnd_6371129 : Nat := 4983230072969 + 3 ^ 40 * 6371129 * 2
def baseEnd_6371129 : Nat := 40388289985174181014657

theorem tailTrace_6371129 : CollatzResearch.WordTrace tailWord_6371129 prefixEnd_6371129 40388289985174181014657 := by
  unfold tailWord_6371129
  simp only [CollatzResearch.WordTrace]
  refine ⟨232374164935495210050068441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154916109956996806700045627 232374164935495210050068441)
  ·
    refine ⟨174280623701621407537551331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232374164935495210050068441 174280623701621407537551331)
    ·
      refine ⟨261420935552432111306326997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174280623701621407537551331 261420935552432111306326997)
      ·
        refine ⟨6127053177010127608742039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 261420935552432111306326997 6127053177010127608742039)
        ·
          refine ⟨9190579765515191413113059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6127053177010127608742039 9190579765515191413113059)
          ·
            refine ⟨13785869648272787119669589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9190579765515191413113059 13785869648272787119669589)
            ·
              refine ⟨40388289985174181014657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13785869648272787119669589 40388289985174181014657)
              ·
                rfl

theorem cell23_6371129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 10].length) (baseStart_6371129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371129 prefixEnd_6371129 := by exact prefixLift 6371129
  have htrace : WordTrace (prefixWord ++ tailWord_6371129) baseStart_6371129 baseEnd_6371129 := by
    simpa [prefixWord, tailWord_6371129, baseEnd_6371129] using wordTrace_append hprefix tailTrace_6371129
  have hstable : (prefixWord ++ tailWord_6371129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371129).length < 2 ^ (prefixWord ++ tailWord_6371129).sum := by decide
  have hdescent : baseEnd_6371129 < baseStart_6371129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371133 : List Nat := [1, 4, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_6371133 : Nat := 118140960795 + 6371133 * 2 ^ 59
def prefixEnd_6371133 : Nat := 4983230072969 + 3 ^ 40 * 6371133 * 2
def baseEnd_6371133 : Nat := 1090484514240575548845733

theorem tailTrace_6371133 : CollatzResearch.WordTrace tailWord_6371133 prefixEnd_6371133 1090484514240575548845733 := by
  unfold tailWord_6371133
  simp only [CollatzResearch.WordTrace]
  refine ⟨232374310827480718733214053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154916207218320479155476035 232374310827480718733214053)
  ·
    refine ⟨43570183280152634762477635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232374310827480718733214053 43570183280152634762477635)
    ·
      refine ⟨65355274920228952143716453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43570183280152634762477635 65355274920228952143716453)
      ·
        refine ⟨12254114047542928526946835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65355274920228952143716453 12254114047542928526946835)
        ·
          refine ⟨18381171071314392790420253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12254114047542928526946835 18381171071314392790420253)
          ·
            refine ⟨6892939151742897296407595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18381171071314392790420253 6892939151742897296407595)
            ·
              refine ⟨10339408727614345944611393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6892939151742897296407595 10339408727614345944611393)
              ·
                refine ⟨7754556545710759458458545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10339408727614345944611393 7754556545710759458458545)
                ·
                  refine ⟨5815917409283069593843909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7754556545710759458458545 5815917409283069593843909)
                  ·
                    refine ⟨1090484514240575548845733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5815917409283069593843909 1090484514240575548845733)
                    ·
                      rfl

theorem cell23_6371133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_6371133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371133 prefixEnd_6371133 := by exact prefixLift 6371133
  have htrace : WordTrace (prefixWord ++ tailWord_6371133) baseStart_6371133 baseEnd_6371133 := by
    simpa [prefixWord, tailWord_6371133, baseEnd_6371133] using wordTrace_append hprefix tailTrace_6371133
  have hstable : (prefixWord ++ tailWord_6371133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371133).length < 2 ^ (prefixWord ++ tailWord_6371133).sum := by decide
  have hdescent : baseEnd_6371133 < baseStart_6371133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371156 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_6371156 : Nat := 118140960795 + 6371156 * 2 ^ 59
def prefixEnd_6371156 : Nat := 4983230072969 + 3 ^ 40 * 6371156 * 2
def baseEnd_6371156 : Nat := 3271465352776780056549593

theorem tailTrace_6371156 : CollatzResearch.WordTrace tailWord_6371156 prefixEnd_6371156 3271465352776780056549593 := by
  unfold tailWord_6371156
  simp only [CollatzResearch.WordTrace]
  refine ⟨116187574853198696830650661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154916766470931595774200881 116187574853198696830650661)
  ·
    refine ⟨21785170284974755655746999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116187574853198696830650661 21785170284974755655746999)
    ·
      refine ⟨32677755427462133483620499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21785170284974755655746999 32677755427462133483620499)
      ·
        refine ⟨49016633141193200225430749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32677755427462133483620499 49016633141193200225430749)
        ·
          refine ⟨18381237427947450084536531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49016633141193200225430749 18381237427947450084536531)
          ·
            refine ⟨27571856141921175126804797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18381237427947450084536531 27571856141921175126804797)
            ·
              refine ⟨10339446053220440672551799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27571856141921175126804797 10339446053220440672551799)
              ·
                refine ⟨15509169079830661008827699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10339446053220440672551799 15509169079830661008827699)
                ·
                  refine ⟨23263753619745991513241549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15509169079830661008827699 23263753619745991513241549)
                  ·
                    refine ⟨8723907607404746817465581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23263753619745991513241549 8723907607404746817465581)
                    ·
                      refine ⟨3271465352776780056549593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8723907607404746817465581 3271465352776780056549593)
                      ·
                        rfl

theorem cell23_6371156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_6371156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371156 prefixEnd_6371156 := by exact prefixLift 6371156
  have htrace : WordTrace (prefixWord ++ tailWord_6371156) baseStart_6371156 baseEnd_6371156 := by
    simpa [prefixWord, tailWord_6371156, baseEnd_6371156] using wordTrace_append hprefix tailTrace_6371156
  have hstable : (prefixWord ++ tailWord_6371156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371156).length < 2 ^ (prefixWord ++ tailWord_6371156).sum := by decide
  have hdescent : baseEnd_6371156 < baseStart_6371156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371179 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 3, 4, 2]
def baseStart_6371179 : Nat := 118140960795 + 6371179 * 2 ^ 59
def prefixEnd_6371179 : Nat := 4983230072969 + 3 ^ 40 * 6371179 * 2
def baseEnd_6371179 : Nat := 3271477162831833466561987

theorem tailTrace_6371179 : CollatzResearch.WordTrace tailWord_6371179 prefixEnd_6371179 3271477162831833466561987 := by
  unfold tailWord_6371179
  simp only [CollatzResearch.WordTrace]
  refine ⟨232375988585314068589388591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154917325723542712392925727 232375988585314068589388591)
  ·
    refine ⟨348563982877971102884082887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232375988585314068589388591 348563982877971102884082887)
    ·
      refine ⟨522845974316956654326124331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348563982877971102884082887 522845974316956654326124331)
      ·
        refine ⟨784268961475434981489186497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522845974316956654326124331 784268961475434981489186497)
        ·
          refine ⟨588201721106576236116889873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784268961475434981489186497 588201721106576236116889873)
          ·
            refine ⟨441151290829932177087667405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588201721106576236116889873 441151290829932177087667405)
            ·
              refine ⟨165431734061224566407875277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441151290829932177087667405 165431734061224566407875277)
              ·
                refine ⟨62036900272959212402953229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165431734061224566407875277 62036900272959212402953229)
                ·
                  refine ⟨23263837602359704651107461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62036900272959212402953229 23263837602359704651107461)
                  ·
                    refine ⟨4361969550442444622082649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23263837602359704651107461 4361969550442444622082649)
                    ·
                      refine ⟨3271477162831833466561987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4361969550442444622082649 3271477162831833466561987)
                      ·
                        rfl

theorem cell23_6371179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4, 2].length) (baseStart_6371179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371179 prefixEnd_6371179 := by exact prefixLift 6371179
  have htrace : WordTrace (prefixWord ++ tailWord_6371179) baseStart_6371179 baseEnd_6371179 := by
    simpa [prefixWord, tailWord_6371179, baseEnd_6371179] using wordTrace_append hprefix tailTrace_6371179
  have hstable : (prefixWord ++ tailWord_6371179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371179).length < 2 ^ (prefixWord ++ tailWord_6371179).sum := by decide
  have hdescent : baseEnd_6371179 < baseStart_6371179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371207 : List Nat := [1, 1, 4, 2, 5, 1, 2, 1, 2, 1, 3]
def baseStart_6371207 : Nat := 118140960795 + 6371207 * 2 ^ 59
def prefixEnd_6371207 : Nat := 4983230072969 + 3 ^ 40 * 6371207 * 2
def baseEnd_6371207 : Nat := 3271491540290159357011859

theorem tailTrace_6371207 : CollatzResearch.WordTrace tailWord_6371207 prefixEnd_6371207 3271491540290159357011859 := by
  unfold tailWord_6371207
  simp only [CollatzResearch.WordTrace]
  refine ⟨232377009829212629371407875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154918006552808419580938583 232377009829212629371407875)
  ·
    refine ⟨348565514743818944057111813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232377009829212629371407875 348565514743818944057111813)
    ·
      refine ⟨65356034014466052010708465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348565514743818944057111813 65356034014466052010708465)
      ·
        refine ⟨49017025510849539008031349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65356034014466052010708465 49017025510849539008031349)
        ·
          refine ⟨4595346141642144282002939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49017025510849539008031349 4595346141642144282002939)
          ·
            refine ⟨6893019212463216423004409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595346141642144282002939 6893019212463216423004409)
            ·
              refine ⟨5169764409347412317253307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6893019212463216423004409 5169764409347412317253307)
              ·
                refine ⟨7754646614021118475879961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5169764409347412317253307 7754646614021118475879961)
                ·
                  refine ⟨5815984960515838856909971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7754646614021118475879961 5815984960515838856909971)
                  ·
                    refine ⟨8723977440773758285364957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5815984960515838856909971 8723977440773758285364957)
                    ·
                      refine ⟨3271491540290159357011859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8723977440773758285364957 3271491540290159357011859)
                      ·
                        rfl

theorem cell23_6371207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_6371207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371207 prefixEnd_6371207 := by exact prefixLift 6371207
  have htrace : WordTrace (prefixWord ++ tailWord_6371207) baseStart_6371207 baseEnd_6371207 := by
    simpa [prefixWord, tailWord_6371207, baseEnd_6371207] using wordTrace_append hprefix tailTrace_6371207
  have hstable : (prefixWord ++ tailWord_6371207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371207).length < 2 ^ (prefixWord ++ tailWord_6371207).sum := by decide
  have hdescent : baseEnd_6371207 < baseStart_6371207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371253 : List Nat := [1, 3, 3, 2, 1, 2, 4, 2, 5]
def baseStart_6371253 : Nat := 118140960795 + 6371253 * 2 ^ 59
def prefixEnd_6371253 : Nat := 4983230072969 + 3 ^ 40 * 6371253 * 2
def baseEnd_6371253 : Nat := 363501684488918464115183

theorem tailTrace_6371253 : CollatzResearch.WordTrace tailWord_6371253 prefixEnd_6371253 363501684488918464115183 := by
  unfold tailWord_6371253
  simp only [CollatzResearch.WordTrace]
  refine ⟨232378687587045979227582413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154919125058030652818388275 232378687587045979227582413)
  ·
    refine ⟨87142007845142242210343405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232378687587045979227582413 87142007845142242210343405)
    ·
      refine ⟨32678252941928340828878777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87142007845142242210343405 32678252941928340828878777)
      ·
        refine ⟨24508689706446255621659083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32678252941928340828878777 24508689706446255621659083)
        ·
          refine ⟨36763034559669383432488625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24508689706446255621659083 36763034559669383432488625)
          ·
            refine ⟨27572275919752037574366469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36763034559669383432488625 27572275919752037574366469)
            ·
              refine ⟨5169801734953507045193713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27572275919752037574366469 5169801734953507045193713)
              ·
                refine ⟨3877351301215130283895285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5169801734953507045193713 3877351301215130283895285)
                ·
                  refine ⟨363501684488918464115183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3877351301215130283895285 363501684488918464115183)
                  ·
                    rfl

theorem cell23_6371253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 5].length) (baseStart_6371253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371253 prefixEnd_6371253 := by exact prefixLift 6371253
  have htrace : WordTrace (prefixWord ++ tailWord_6371253) baseStart_6371253 baseEnd_6371253 := by
    simpa [prefixWord, tailWord_6371253, baseEnd_6371253] using wordTrace_append hprefix tailTrace_6371253
  have hstable : (prefixWord ++ tailWord_6371253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371253).length < 2 ^ (prefixWord ++ tailWord_6371253).sum := by decide
  have hdescent : baseEnd_6371253 < baseStart_6371253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371299 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 6]
def baseStart_6371299 : Nat := 118140960795 + 6371299 * 2 ^ 59
def prefixEnd_6371299 : Nat := 4983230072969 + 3 ^ 40 * 6371299 * 2
def baseEnd_6371299 : Nat := 3271538780510372997061435

theorem tailTrace_6371299 : CollatzResearch.WordTrace tailWord_6371299 prefixEnd_6371299 3271538780510372997061435 := by
  unfold tailWord_6371299
  simp only [CollatzResearch.WordTrace]
  refine ⟨232380365344879329083756951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154920243563252886055837967 232380365344879329083756951)
  ·
    refine ⟨348570548017318993625635427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232380365344879329083756951 348570548017318993625635427)
    ·
      refine ⟨522855822025978490438453141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348570548017318993625635427 522855822025978490438453141)
      ·
        refine ⟨24508866657467741739302491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 522855822025978490438453141 24508866657467741739302491)
        ·
          refine ⟨36763299986201612608953737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24508866657467741739302491 36763299986201612608953737)
          ·
            refine ⟨27572474989651209456715303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36763299986201612608953737 27572474989651209456715303)
            ·
              refine ⟨41358712484476814185072955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27572474989651209456715303 41358712484476814185072955)
              ·
                refine ⟨62038068726715221277609433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41358712484476814185072955 62038068726715221277609433)
                ·
                  refine ⟨46528551545036415958207075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62038068726715221277609433 46528551545036415958207075)
                  ·
                    refine ⟨69792827317554623937310613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46528551545036415958207075 69792827317554623937310613)
                    ·
                      refine ⟨3271538780510372997061435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69792827317554623937310613 3271538780510372997061435)
                      ·
                        rfl

theorem cell23_6371299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_6371299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371299 prefixEnd_6371299 := by exact prefixLift 6371299
  have htrace : WordTrace (prefixWord ++ tailWord_6371299) baseStart_6371299 baseEnd_6371299 := by
    simpa [prefixWord, tailWord_6371299, baseEnd_6371299] using wordTrace_append hprefix tailTrace_6371299
  have hstable : (prefixWord ++ tailWord_6371299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371299).length < 2 ^ (prefixWord ++ tailWord_6371299).sum := by decide
  have hdescent : baseEnd_6371299 < baseStart_6371299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371306 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_6371306 : Nat := 118140960795 + 6371306 * 2 ^ 59
def prefixEnd_6371306 : Nat := 4983230072969 + 3 ^ 40 * 6371306 * 2
def baseEnd_6371306 : Nat := 3271542374874954469673903

theorem tailTrace_6371306 : CollatzResearch.WordTrace tailWord_6371306 prefixEnd_6371306 3271542374874954469673903 := by
  unfold tailWord_6371306
  simp only [CollatzResearch.WordTrace]
  refine ⟨58095155163963492319815443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154920413770569312852841181 58095155163963492319815443)
  ·
    refine ⟨87142732745945238479723165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58095155163963492319815443 87142732745945238479723165)
    ·
      refine ⟨32678524779729464429896187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87142732745945238479723165 32678524779729464429896187)
      ·
        refine ⟨49017787169594196644844281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32678524779729464429896187 49017787169594196644844281)
        ·
          refine ⟨36763340377195647483633211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49017787169594196644844281 36763340377195647483633211)
          ·
            refine ⟨55145010565793471225449817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36763340377195647483633211 55145010565793471225449817)
            ·
              refine ⟨41358757924345103419087363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55145010565793471225449817 41358757924345103419087363)
              ·
                refine ⟨62038136886517655128631045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41358757924345103419087363 62038136886517655128631045)
                ·
                  refine ⟨11632150666222060336618321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62038136886517655128631045 11632150666222060336618321)
                  ·
                    refine ⟨8724112999666545252463741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11632150666222060336618321 8724112999666545252463741)
                    ·
                      refine ⟨3271542374874954469673903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8724112999666545252463741 3271542374874954469673903)
                      ·
                        rfl

theorem cell23_6371306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_6371306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371306 prefixEnd_6371306 := by exact prefixLift 6371306
  have htrace : WordTrace (prefixWord ++ tailWord_6371306) baseStart_6371306 baseEnd_6371306 := by
    simpa [prefixWord, tailWord_6371306, baseEnd_6371306] using wordTrace_append hprefix tailTrace_6371306
  have hstable : (prefixWord ++ tailWord_6371306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371306).length < 2 ^ (prefixWord ++ tailWord_6371306).sum := by decide
  have hdescent : baseEnd_6371306 < baseStart_6371306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371313 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 3, 4]
def baseStart_6371313 : Nat := 118140960795 + 6371313 * 2 ^ 59
def prefixEnd_6371313 : Nat := 4983230072969 + 3 ^ 40 * 6371313 * 2
def baseEnd_6371313 : Nat := 1090515323079845314095457

theorem tailTrace_6371313 : CollatzResearch.WordTrace tailWord_6371313 prefixEnd_6371313 1090515323079845314095457 := by
  unfold tailWord_6371313
  simp only [CollatzResearch.WordTrace]
  refine ⟨232380875966828609474766593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154920583977885739649844395 232380875966828609474766593)
  ·
    refine ⟨174285656975121457106074945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232380875966828609474766593 174285656975121457106074945)
    ·
      refine ⟨130714242731341092829556209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174285656975121457106074945 130714242731341092829556209)
      ·
        refine ⟨98035682048505819622167157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130714242731341092829556209 98035682048505819622167157)
        ·
          refine ⟨9190845192047420589578171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98035682048505819622167157 9190845192047420589578171)
          ·
            refine ⟨13786267788071130884367257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9190845192047420589578171 13786267788071130884367257)
            ·
              refine ⟨10339700841053348163275443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13786267788071130884367257 10339700841053348163275443)
              ·
                refine ⟨15509551261580022244913165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10339700841053348163275443 15509551261580022244913165)
                ·
                  refine ⟨5816081723092508341842437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15509551261580022244913165 5816081723092508341842437)
                  ·
                    refine ⟨1090515323079845314095457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5816081723092508341842437 1090515323079845314095457)
                    ·
                      rfl

theorem cell23_6371313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_6371313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371313 prefixEnd_6371313 := by exact prefixLift 6371313
  have htrace : WordTrace (prefixWord ++ tailWord_6371313) baseStart_6371313 baseEnd_6371313 := by
    simpa [prefixWord, tailWord_6371313, baseEnd_6371313] using wordTrace_append hprefix tailTrace_6371313
  have hstable : (prefixWord ++ tailWord_6371313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371313).length < 2 ^ (prefixWord ++ tailWord_6371313).sum := by decide
  have hdescent : baseEnd_6371313 < baseStart_6371313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371329 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_6371329 : Nat := 118140960795 + 6371329 * 2 ^ 59
def prefixEnd_6371329 : Nat := 4983230072969 + 3 ^ 40 * 6371329 * 2
def baseEnd_6371329 : Nat := 3271554184930007879686297

theorem tailTrace_6371329 : CollatzResearch.WordTrace tailWord_6371329 prefixEnd_6371329 3271554184930007879686297 := by
  unfold tailWord_6371329
  simp only [CollatzResearch.WordTrace]
  refine ⟨232381459534770644207349041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154920973023180429471566027 232381459534770644207349041)
  ·
    refine ⟨174286094651077983155511781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232381459534770644207349041 174286094651077983155511781)
    ·
      refine ⟨32678642747077121841658459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174286094651077983155511781 32678642747077121841658459)
      ·
        refine ⟨49017964120615682762487689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32678642747077121841658459 49017964120615682762487689)
        ·
          refine ⟨36763473090461762071865767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49017964120615682762487689 36763473090461762071865767)
          ·
            refine ⟨55145209635692643107798651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36763473090461762071865767 55145209635692643107798651)
            ·
              refine ⟨82717814453538964661697977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55145209635692643107798651 82717814453538964661697977)
              ·
                refine ⟨62038360840154223496273483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82717814453538964661697977 62038360840154223496273483)
                ·
                  refine ⟨93057541260231335244410225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62038360840154223496273483 93057541260231335244410225)
                  ·
                    refine ⟨69793155945173501433307669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93057541260231335244410225 69793155945173501433307669)
                    ·
                      refine ⟨3271554184930007879686297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69793155945173501433307669 3271554184930007879686297)
                      ·
                        rfl

theorem cell23_6371329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_6371329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371329 prefixEnd_6371329 := by exact prefixLift 6371329
  have htrace : WordTrace (prefixWord ++ tailWord_6371329) baseStart_6371329 baseEnd_6371329 := by
    simpa [prefixWord, tailWord_6371329, baseEnd_6371329] using wordTrace_append hprefix tailTrace_6371329
  have hstable : (prefixWord ++ tailWord_6371329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371329).length < 2 ^ (prefixWord ++ tailWord_6371329).sum := by decide
  have hdescent : baseEnd_6371329 < baseStart_6371329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371363 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 2, 3, 2]
def baseStart_6371363 : Nat := 118140960795 + 6371363 * 2 ^ 59
def prefixEnd_6371363 : Nat := 4983230072969 + 3 ^ 40 * 6371363 * 2
def baseEnd_6371363 : Nat := 3271571643272260746661141

theorem tailTrace_6371363 : CollatzResearch.WordTrace tailWord_6371363 prefixEnd_6371363 3271571643272260746661141 := by
  unfold tailWord_6371363
  simp only [CollatzResearch.WordTrace]
  refine ⟨232382699616647468014086743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154921799744431645342724495 232382699616647468014086743)
  ·
    refine ⟨348574049424971202021130115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232382699616647468014086743 348574049424971202021130115)
    ·
      refine ⟨522861074137456803031695173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348574049424971202021130115 522861074137456803031695173)
      ·
        refine ⟨98036451400773150568442845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 522861074137456803031695173 98036451400773150568442845)
        ·
          refine ⟨36763669275289931463166067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98036451400773150568442845 36763669275289931463166067)
          ·
            refine ⟨55145503912934897194749101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36763669275289931463166067 55145503912934897194749101)
            ·
              refine ⟨20679563967350586448030913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55145503912934897194749101 20679563967350586448030913)
              ·
                refine ⟨15509672975512939836023185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20679563967350586448030913 15509672975512939836023185)
                ·
                  refine ⟨11632254731634704877017389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15509672975512939836023185 11632254731634704877017389)
                  ·
                    refine ⟨4362095524363014328881521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11632254731634704877017389 4362095524363014328881521)
                    ·
                      refine ⟨3271571643272260746661141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362095524363014328881521 3271571643272260746661141)
                      ·
                        rfl

theorem cell23_6371363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_6371363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371363 prefixEnd_6371363 := by exact prefixLift 6371363
  have htrace : WordTrace (prefixWord ++ tailWord_6371363) baseStart_6371363 baseEnd_6371363 := by
    simpa [prefixWord, tailWord_6371363, baseEnd_6371363] using wordTrace_append hprefix tailTrace_6371363
  have hstable : (prefixWord ++ tailWord_6371363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371363).length < 2 ^ (prefixWord ++ tailWord_6371363).sum := by decide
  have hdescent : baseEnd_6371363 < baseStart_6371363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371370 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_6371370 : Nat := 118140960795 + 6371370 * 2 ^ 59
def prefixEnd_6371370 : Nat := 4983230072969 + 3 ^ 40 * 6371370 * 2
def baseEnd_6371370 : Nat := 3271575237636842219273609

theorem tailTrace_6371370 : CollatzResearch.WordTrace tailWord_6371370 prefixEnd_6371370 3271575237636842219273609 := by
  unfold tailWord_6371370
  simp only [CollatzResearch.WordTrace]
  refine ⟨58095738731905527052397891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154921969951748072139727709 58095738731905527052397891)
  ·
    refine ⟨87143608097858290578596837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58095738731905527052397891 87143608097858290578596837)
    ·
      refine ⟨16339426518348429483486907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87143608097858290578596837 16339426518348429483486907)
      ·
        refine ⟨24509139777522644225230361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16339426518348429483486907 24509139777522644225230361)
        ·
          refine ⟨18381854833141983168922771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24509139777522644225230361 18381854833141983168922771)
          ·
            refine ⟨27572782249712974753384157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18381854833141983168922771 27572782249712974753384157)
            ·
              refine ⟨10339793343642365532519059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27572782249712974753384157 10339793343642365532519059)
              ·
                refine ⟨15509690015463548298778589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10339793343642365532519059 15509690015463548298778589)
                ·
                  refine ⟨5816133755798830612041971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15509690015463548298778589 5816133755798830612041971)
                  ·
                    refine ⟨8724200633698245918062957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5816133755798830612041971 8724200633698245918062957)
                    ·
                      refine ⟨3271575237636842219273609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8724200633698245918062957 3271575237636842219273609)
                      ·
                        rfl

theorem cell23_6371370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_6371370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371370 prefixEnd_6371370 := by exact prefixLift 6371370
  have htrace : WordTrace (prefixWord ++ tailWord_6371370) baseStart_6371370 baseEnd_6371370 := by
    simpa [prefixWord, tailWord_6371370, baseEnd_6371370] using wordTrace_append hprefix tailTrace_6371370
  have hstable : (prefixWord ++ tailWord_6371370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371370).length < 2 ^ (prefixWord ++ tailWord_6371370).sum := by decide
  have hdescent : baseEnd_6371370 < baseStart_6371370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371393 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_6371393 : Nat := 118140960795 + 6371393 * 2 ^ 59
def prefixEnd_6371393 : Nat := 4983230072969 + 3 ^ 40 * 6371393 * 2
def baseEnd_6371393 : Nat := 3271587047691895629286003

theorem tailTrace_6371393 : CollatzResearch.WordTrace tailWord_6371393 prefixEnd_6371393 3271587047691895629286003 := by
  unfold tailWord_6371393
  simp only [CollatzResearch.WordTrace]
  refine ⟨232383793806538783137678833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154922529204359188758452555 232383793806538783137678833)
  ·
    refine ⟨174287845354904087353259125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232383793806538783137678833 174287845354904087353259125)
    ·
      refine ⟨16339485502022258189368043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174287845354904087353259125 16339485502022258189368043)
      ·
        refine ⟨24509228253033387284052065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16339485502022258189368043 24509228253033387284052065)
        ·
          refine ⟨18381921189775040463039049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24509228253033387284052065 18381921189775040463039049)
          ·
            refine ⟨13786440892331280347279287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18381921189775040463039049 13786440892331280347279287)
            ·
              refine ⟨20679661338496920520918931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13786440892331280347279287 20679661338496920520918931)
              ·
                refine ⟨31019492007745380781378397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20679661338496920520918931 31019492007745380781378397)
                ·
                  refine ⟨11632309502904517793016899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31019492007745380781378397 11632309502904517793016899)
                  ·
                    refine ⟨17448464254356776689525349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11632309502904517793016899 17448464254356776689525349)
                    ·
                      refine ⟨3271587047691895629286003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17448464254356776689525349 3271587047691895629286003)
                      ·
                        rfl

theorem cell23_6371393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_6371393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371393 prefixEnd_6371393 := by exact prefixLift 6371393
  have htrace : WordTrace (prefixWord ++ tailWord_6371393) baseStart_6371393 baseEnd_6371393 := by
    simpa [prefixWord, tailWord_6371393, baseEnd_6371393] using wordTrace_append hprefix tailTrace_6371393
  have hstable : (prefixWord ++ tailWord_6371393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371393).length < 2 ^ (prefixWord ++ tailWord_6371393).sum := by decide
  have hdescent : baseEnd_6371393 < baseStart_6371393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371399 : List Nat := [1, 1, 4, 1, 3, 1, 1, 11]
def baseStart_6371399 : Nat := 118140960795 + 6371399 * 2 ^ 59
def prefixEnd_6371399 : Nat := 4983230072969 + 3 ^ 40 * 6371399 * 2
def baseEnd_6371399 : Nat := 121170004762067503918925

theorem tailTrace_6371399 : CollatzResearch.WordTrace tailWord_6371399 prefixEnd_6371399 121170004762067503918925 := by
  unfold tailWord_6371399
  simp only [CollatzResearch.WordTrace]
  refine ⟨232384012644517046162397251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154922675096344697441598167 232384012644517046162397251)
  ·
    refine ⟨348576018966775569243595877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232384012644517046162397251 348576018966775569243595877)
    ·
      refine ⟨65358003556270419233174227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348576018966775569243595877 65358003556270419233174227)
      ·
        refine ⟨98037005334405628849761341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65358003556270419233174227 98037005334405628849761341)
        ·
          refine ⟨36763877000402110818660503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98037005334405628849761341 36763877000402110818660503)
          ·
            refine ⟨55145815500603166227990755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36763877000402110818660503 55145815500603166227990755)
            ·
              refine ⟨82718723250904749341986133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55145815500603166227990755 82718723250904749341986133)
              ·
                refine ⟨121170004762067503918925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 82718723250904749341986133 121170004762067503918925)
                ·
                  rfl

theorem cell23_6371399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 11].length) (baseStart_6371399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371399 prefixEnd_6371399 := by exact prefixLift 6371399
  have htrace : WordTrace (prefixWord ++ tailWord_6371399) baseStart_6371399 baseEnd_6371399 := by
    simpa [prefixWord, tailWord_6371399, baseEnd_6371399] using wordTrace_append hprefix tailTrace_6371399
  have hstable : (prefixWord ++ tailWord_6371399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371399).length < 2 ^ (prefixWord ++ tailWord_6371399).sum := by decide
  have hdescent : baseEnd_6371399 < baseStart_6371399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371406 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_6371406 : Nat := 118140960795 + 6371406 * 2 ^ 59
def prefixEnd_6371406 : Nat := 4983230072969 + 3 ^ 40 * 6371406 * 2
def baseEnd_6371406 : Nat := 3271593722940404078423443

theorem tailTrace_6371406 : CollatzResearch.WordTrace tailWord_6371406 prefixEnd_6371406 3271593722940404078423443 := by
  unfold tailWord_6371406
  simp only [CollatzResearch.WordTrace]
  refine ⟨29048033494436460794737759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154922845303661124238601381 29048033494436460794737759)
  ·
    refine ⟨43572050241654691192106639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29048033494436460794737759 43572050241654691192106639)
    ·
      refine ⟨65358075362482036788159959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43572050241654691192106639 65358075362482036788159959)
      ·
        refine ⟨98037113043723055182239939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65358075362482036788159959 98037113043723055182239939)
        ·
          refine ⟨147055669565584582773359909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98037113043723055182239939 147055669565584582773359909)
          ·
            refine ⟨27572938043547109270004983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147055669565584582773359909 27572938043547109270004983)
            ·
              refine ⟨41359407065320663905007475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27572938043547109270004983 41359407065320663905007475)
              ·
                refine ⟨62039110597980995857511213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41359407065320663905007475 62039110597980995857511213)
                ·
                  refine ⟨23264666474242873446566705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62039110597980995857511213 23264666474242873446566705)
                  ·
                    refine ⟨17448499855682155084925029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23264666474242873446566705 17448499855682155084925029)
                    ·
                      refine ⟨3271593722940404078423443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17448499855682155084925029 3271593722940404078423443)
                      ·
                        rfl

theorem cell23_6371406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_6371406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371406 prefixEnd_6371406 := by exact prefixLift 6371406
  have htrace : WordTrace (prefixWord ++ tailWord_6371406) baseStart_6371406 baseEnd_6371406 := by
    simpa [prefixWord, tailWord_6371406, baseEnd_6371406] using wordTrace_append hprefix tailTrace_6371406
  have hstable : (prefixWord ++ tailWord_6371406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371406).length < 2 ^ (prefixWord ++ tailWord_6371406).sum := by decide
  have hdescent : baseEnd_6371406 < baseStart_6371406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371413 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 1, 1, 5]
def baseStart_6371413 : Nat := 118140960795 + 6371413 * 2 ^ 59
def prefixEnd_6371413 : Nat := 4983230072969 + 3 ^ 40 * 6371413 * 2
def baseEnd_6371413 : Nat := 3271597317304985551035911

theorem tailTrace_6371413 : CollatzResearch.WordTrace tailWord_6371413 prefixEnd_6371413 3271597317304985551035911 := by
  unfold tailWord_6371413
  simp only [CollatzResearch.WordTrace]
  refine ⟨232384523266466326553406893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154923015510977551035604595 232384523266466326553406893)
  ·
    refine ⟨87144196224924872457527585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232384523266466326553406893 87144196224924872457527585)
    ·
      refine ⟨65358147168693654343145689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87144196224924872457527585 65358147168693654343145689)
      ·
        refine ⟨49018610376520240757359267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65358147168693654343145689 49018610376520240757359267)
        ·
          refine ⟨73527915564780361136038901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49018610376520240757359267 73527915564780361136038901)
          ·
            refine ⟨6893242084198158856503647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73527915564780361136038901 6893242084198158856503647)
            ·
              refine ⟨10339863126297238284755471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6893242084198158856503647 10339863126297238284755471)
              ·
                refine ⟨15509794689445857427133207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10339863126297238284755471 15509794689445857427133207)
                ·
                  refine ⟨23264692034168786140699811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15509794689445857427133207 23264692034168786140699811)
                  ·
                    refine ⟨34897038051253179211049717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23264692034168786140699811 34897038051253179211049717)
                    ·
                      refine ⟨3271597317304985551035911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34897038051253179211049717 3271597317304985551035911)
                      ·
                        rfl

theorem cell23_6371413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_6371413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371413 prefixEnd_6371413 := by exact prefixLift 6371413
  have htrace : WordTrace (prefixWord ++ tailWord_6371413) baseStart_6371413 baseEnd_6371413 := by
    simpa [prefixWord, tailWord_6371413, baseEnd_6371413] using wordTrace_append hprefix tailTrace_6371413
  have hstable : (prefixWord ++ tailWord_6371413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371413).length < 2 ^ (prefixWord ++ tailWord_6371413).sum := by decide
  have hdescent : baseEnd_6371413 < baseStart_6371413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371420 : List Nat := [2, 2, 4, 1, 1, 3, 2, 2, 2, 4]
def baseStart_6371420 : Nat := 118140960795 + 6371420 * 2 ^ 59
def prefixEnd_6371420 : Nat := 4983230072969 + 3 ^ 40 * 6371420 * 2
def baseEnd_6371420 : Nat := 1090533637223189007882793

theorem tailTrace_6371420 : CollatzResearch.WordTrace tailWord_6371420 prefixEnd_6371420 1090533637223189007882793 := by
  unfold tailWord_6371420
  simp only [CollatzResearch.WordTrace]
  refine ⟨116192389288720483374455857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154923185718293977832607809 116192389288720483374455857)
  ·
    refine ⟨87144291966540362530841893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116192389288720483374455857 87144291966540362530841893)
    ·
      refine ⟨16339554743726317974532855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87144291966540362530841893 16339554743726317974532855)
      ·
        refine ⟨24509332115589476961799283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16339554743726317974532855 24509332115589476961799283)
        ·
          refine ⟨36763998173384215442698925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24509332115589476961799283 36763998173384215442698925)
          ·
            refine ⟨13786499315019080791012097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36763998173384215442698925 13786499315019080791012097)
            ·
              refine ⟨10339874486264310593259073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13786499315019080791012097 10339874486264310593259073)
              ·
                refine ⟨7754905864698232944944305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10339874486264310593259073 7754905864698232944944305)
                ·
                  refine ⟨5816179398523674708708229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7754905864698232944944305 5816179398523674708708229)
                  ·
                    refine ⟨1090533637223189007882793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5816179398523674708708229 1090533637223189007882793)
                    ·
                      rfl

theorem cell23_6371420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_6371420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371420 prefixEnd_6371420 := by exact prefixLift 6371420
  have htrace : WordTrace (prefixWord ++ tailWord_6371420) baseStart_6371420 baseEnd_6371420 := by
    simpa [prefixWord, tailWord_6371420, baseEnd_6371420] using wordTrace_append hprefix tailTrace_6371420
  have hstable : (prefixWord ++ tailWord_6371420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371420).length < 2 ^ (prefixWord ++ tailWord_6371420).sum := by decide
  have hdescent : baseEnd_6371420 < baseStart_6371420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371421 : List Nat := [1, 4, 4, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_6371421 : Nat := 118140960795 + 6371421 * 2 ^ 59
def prefixEnd_6371421 : Nat := 4983230072969 + 3 ^ 40 * 6371421 * 2
def baseEnd_6371421 : Nat := 3271601425150221519735875

theorem tailTrace_6371421 : CollatzResearch.WordTrace tailWord_6371421 prefixEnd_6371421 3271601425150221519735875 := by
  unfold tailWord_6371421
  simp only [CollatzResearch.WordTrace]
  refine ⟨232384815050437343919698117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154923210033624895946465411 232384815050437343919698117)
  ·
    refine ⟨43572152821957001984943397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232384815050437343919698117 43572152821957001984943397)
    ·
      refine ⟨8169778654116937872176887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43572152821957001984943397 8169778654116937872176887)
      ·
        refine ⟨12254667981175406808265331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8169778654116937872176887 12254667981175406808265331)
        ·
          refine ⟨18382001971763110212397997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12254667981175406808265331 18382001971763110212397997)
          ·
            refine ⟨6893250739411166329649249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18382001971763110212397997 6893250739411166329649249)
            ·
              refine ⟨5169938054558374747236937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6893250739411166329649249 5169938054558374747236937)
              ·
                refine ⟨3877453540918781060427703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5169938054558374747236937 3877453540918781060427703)
                ·
                  refine ⟨5816180311378171590641555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877453540918781060427703 5816180311378171590641555)
                  ·
                    refine ⟨8724270467067257385962333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5816180311378171590641555 8724270467067257385962333)
                    ·
                      refine ⟨3271601425150221519735875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8724270467067257385962333 3271601425150221519735875)
                      ·
                        rfl

theorem cell23_6371421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_6371421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371421 prefixEnd_6371421 := by exact prefixLift 6371421
  have htrace : WordTrace (prefixWord ++ tailWord_6371421) baseStart_6371421 baseEnd_6371421 := by
    simpa [prefixWord, tailWord_6371421, baseEnd_6371421] using wordTrace_append hprefix tailTrace_6371421
  have hstable : (prefixWord ++ tailWord_6371421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371421).length < 2 ^ (prefixWord ++ tailWord_6371421).sum := by decide
  have hdescent : baseEnd_6371421 < baseStart_6371421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371506 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 7]
def baseStart_6371506 : Nat := 118140960795 + 6371506 * 2 ^ 59
def prefixEnd_6371506 : Nat := 4983230072969 + 3 ^ 40 * 6371506 * 2
def baseEnd_6371506 : Nat := 363516119000650409685887

theorem tailTrace_6371506 : CollatzResearch.WordTrace tailWord_6371506 prefixEnd_6371506 363516119000650409685887 := by
  unfold tailWord_6371506
  simp only [CollatzResearch.WordTrace]
  refine ⟨58096978813782350859135593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154925276836752935624361581 58096978813782350859135593)
  ·
    refine ⟨43572734110336763144351695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58096978813782350859135593 43572734110336763144351695)
    ·
      refine ⟨65359101165505144716527543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43572734110336763144351695 65359101165505144716527543)
      ·
        refine ⟨98038651748257717074791315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65359101165505144716527543 98038651748257717074791315)
        ·
          refine ⟨147057977622386575612186973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98038651748257717074791315 147057977622386575612186973)
          ·
            refine ⟨55146741608394965854570115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147057977622386575612186973 55146741608394965854570115)
            ·
              refine ⟨82720112412592448781855173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55146741608394965854570115 82720112412592448781855173)
              ·
                refine ⟨15510021077361084146597845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82720112412592448781855173 15510021077361084146597845)
                ·
                  refine ⟨363516119000650409685887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15510021077361084146597845 363516119000650409685887)
                  ·
                    rfl

theorem cell23_6371506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_6371506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371506 prefixEnd_6371506 := by exact prefixLift 6371506
  have htrace : WordTrace (prefixWord ++ tailWord_6371506) baseStart_6371506 baseEnd_6371506 := by
    simpa [prefixWord, tailWord_6371506, baseEnd_6371506] using wordTrace_append hprefix tailTrace_6371506
  have hstable : (prefixWord ++ tailWord_6371506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371506).length < 2 ^ (prefixWord ++ tailWord_6371506).sum := by decide
  have hdescent : baseEnd_6371506 < baseStart_6371506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371543 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 2, 5, 2]
def baseStart_6371543 : Nat := 118140960795 + 6371543 * 2 ^ 59
def prefixEnd_6371543 : Nat := 4983230072969 + 3 ^ 40 * 6371543 * 2
def baseEnd_6371543 : Nat := 3271664069790070042410313

theorem tailTrace_6371543 : CollatzResearch.WordTrace tailWord_6371543 prefixEnd_6371543 3271664069790070042410313 := by
  unfold tailWord_6371543
  simp only [CollatzResearch.WordTrace]
  refine ⟨232389264755995358755639283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154926176503996905837092855 232389264755995358755639283)
  ·
    refine ⟨348583897133993038133458925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232389264755995358755639283 348583897133993038133458925)
    ·
      refine ⟨130718961425247389300047097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348583897133993038133458925 130718961425247389300047097)
      ·
        refine ⟨98039221068935541975035323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130718961425247389300047097 98039221068935541975035323)
        ·
          refine ⟨147058831603403312962552985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98039221068935541975035323 147058831603403312962552985)
          ·
            refine ⟨110294123702552484721914739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147058831603403312962552985 110294123702552484721914739)
            ·
              refine ⟨165441185553828727082872109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110294123702552484721914739 165441185553828727082872109)
              ·
                refine ⟨62040444582685772656077041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165441185553828727082872109 62040444582685772656077041)
                ·
                  refine ⟨46530333437014329492057781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62040444582685772656077041 46530333437014329492057781)
                  ·
                    refine ⟨4362218759720093389880417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46530333437014329492057781 4362218759720093389880417)
                    ·
                      refine ⟨3271664069790070042410313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362218759720093389880417 3271664069790070042410313)
                      ·
                        rfl

theorem cell23_6371543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_6371543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371543 prefixEnd_6371543 := by exact prefixLift 6371543
  have htrace : WordTrace (prefixWord ++ tailWord_6371543) baseStart_6371543 baseEnd_6371543 := by
    simpa [prefixWord, tailWord_6371543, baseEnd_6371543] using wordTrace_append hprefix tailTrace_6371543
  have hstable : (prefixWord ++ tailWord_6371543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371543).length < 2 ^ (prefixWord ++ tailWord_6371543).sum := by decide
  have hdescent : baseEnd_6371543 < baseStart_6371543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371546 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_6371546 : Nat := 118140960795 + 6371546 * 2 ^ 59
def prefixEnd_6371546 : Nat := 4983230072969 + 3 ^ 40 * 6371546 * 2
def baseEnd_6371546 : Nat := 3271665610232033530672799

theorem tailTrace_6371546 : CollatzResearch.WordTrace tailWord_6371546 prefixEnd_6371546 3271665610232033530672799 := by
  unfold tailWord_6371546
  simp only [CollatzResearch.WordTrace]
  refine ⟨58097343543746122566999623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154926249449989660178665661 58097343543746122566999623)
  ·
    refine ⟨87146015315619183850499435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58097343543746122566999623 87146015315619183850499435)
    ·
      refine ⟨130719022973428775775749153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87146015315619183850499435 130719022973428775775749153)
      ·
        refine ⟨98039267230071581831811865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130719022973428775775749153 98039267230071581831811865)
        ·
          refine ⟨73529450422553686373858899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98039267230071581831811865 73529450422553686373858899)
          ·
            refine ⟨110294175633830529560788349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73529450422553686373858899 110294175633830529560788349)
            ·
              refine ⟨41360315862686448585295631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110294175633830529560788349 41360315862686448585295631)
              ·
                refine ⟨62040473794029672877943447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41360315862686448585295631 62040473794029672877943447)
                ·
                  refine ⟨93060710691044509316915171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62040473794029672877943447 93060710691044509316915171)
                  ·
                    refine ⟨139591066036566763975372757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93060710691044509316915171 139591066036566763975372757)
                    ·
                      refine ⟨3271665610232033530672799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139591066036566763975372757 3271665610232033530672799)
                      ·
                        rfl

theorem cell23_6371546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_6371546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371546 prefixEnd_6371546 := by exact prefixLift 6371546
  have htrace : WordTrace (prefixWord ++ tailWord_6371546) baseStart_6371546 baseEnd_6371546 := by
    simpa [prefixWord, tailWord_6371546, baseEnd_6371546] using wordTrace_append hprefix tailTrace_6371546
  have hstable : (prefixWord ++ tailWord_6371546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371546).length < 2 ^ (prefixWord ++ tailWord_6371546).sum := by decide
  have hdescent : baseEnd_6371546 < baseStart_6371546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371570 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_6371570 : Nat := 118140960795 + 6371570 * 2 ^ 59
def prefixEnd_6371570 : Nat := 4983230072969 + 3 ^ 40 * 6371570 * 2
def baseEnd_6371570 : Nat := 1090559311255913812257563

theorem tailTrace_6371570 : CollatzResearch.WordTrace tailWord_6371570 prefixEnd_6371570 1090559311255913812257563 := by
  unfold tailWord_6371570
  simp only [CollatzResearch.WordTrace]
  refine ⟨58097562381724385591718041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154926833017931694911248109 58097562381724385591718041)
  ·
    refine ⟨43573171786293289193788531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58097562381724385591718041 43573171786293289193788531)
    ·
      refine ⟨65359757679439933790682797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43573171786293289193788531 65359757679439933790682797)
      ·
        refine ⟨24509909129789975171506049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65359757679439933790682797 24509909129789975171506049)
        ·
          refine ⟨18382431847342481378629537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24509909129789975171506049 18382431847342481378629537)
          ·
            refine ⟨13786823885506861033972153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18382431847342481378629537 13786823885506861033972153)
            ·
              refine ⟨10340117914130145775479115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13786823885506861033972153 10340117914130145775479115)
              ·
                refine ⟨15510176871195218663218673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10340117914130145775479115 15510176871195218663218673)
                ·
                  refine ⟨11632632653396413997414005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15510176871195218663218673 11632632653396413997414005)
                  ·
                    refine ⟨1090559311255913812257563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11632632653396413997414005 1090559311255913812257563)
                    ·
                      rfl

theorem cell23_6371570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_6371570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371570 prefixEnd_6371570 := by exact prefixLift 6371570
  have htrace : WordTrace (prefixWord ++ tailWord_6371570) baseStart_6371570 baseEnd_6371570 := by
    simpa [prefixWord, tailWord_6371570, baseEnd_6371570] using wordTrace_append hprefix tailTrace_6371570
  have hstable : (prefixWord ++ tailWord_6371570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371570).length < 2 ^ (prefixWord ++ tailWord_6371570).sum := by decide
  have hdescent : baseEnd_6371570 < baseStart_6371570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371591 : List Nat := [1, 1, 4, 5, 2, 1, 2, 2, 5]
def baseStart_6371591 : Nat := 118140960795 + 6371591 * 2 ^ 59
def prefixEnd_6371591 : Nat := 4983230072969 + 3 ^ 40 * 6371591 * 2
def baseEnd_6371591 : Nat := 363520968540165094956677

theorem tailTrace_6371591 : CollatzResearch.WordTrace tailWord_6371591 prefixEnd_6371591 363520968540165094956677 := by
  unfold tailWord_6371591
  simp only [CollatzResearch.WordTrace]
  refine ⟨232391015459821462953386627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154927343639880975302257751 232391015459821462953386627)
  ·
    refine ⟨348586523189732194430079941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232391015459821462953386627 348586523189732194430079941)
    ·
      refine ⟨65359973098074786455639989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348586523189732194430079941 65359973098074786455639989)
      ·
        refine ⟨6127497477944511230216249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65359973098074786455639989 6127497477944511230216249)
        ·
          refine ⟨4595623108458383422662187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6127497477944511230216249 4595623108458383422662187)
          ·
            refine ⟨6893434662687575133993281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595623108458383422662187 6893434662687575133993281)
            ·
              refine ⟨5170075997015681350494961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6893434662687575133993281 5170075997015681350494961)
              ·
                refine ⟨3877556997761761012871221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5170075997015681350494961 3877556997761761012871221)
                ·
                  refine ⟨363520968540165094956677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3877556997761761012871221 363520968540165094956677)
                  ·
                    rfl

theorem cell23_6371591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 5].length) (baseStart_6371591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371591 prefixEnd_6371591 := by exact prefixLift 6371591
  have htrace : WordTrace (prefixWord ++ tailWord_6371591) baseStart_6371591 baseEnd_6371591 := by
    simpa [prefixWord, tailWord_6371591, baseEnd_6371591] using wordTrace_append hprefix tailTrace_6371591
  have hstable : (prefixWord ++ tailWord_6371591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371591).length < 2 ^ (prefixWord ++ tailWord_6371591).sum := by decide
  have hdescent : baseEnd_6371591 < baseStart_6371591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371624 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_6371624 : Nat := 118140960795 + 6371624 * 2 ^ 59
def prefixEnd_6371624 : Nat := 4983230072969 + 3 ^ 40 * 6371624 * 2
def baseEnd_6371624 : Nat := 3271705661723084225497441

theorem tailTrace_6371624 : CollatzResearch.WordTrace tailWord_6371624 prefixEnd_6371624 3271705661723084225497441 := by
  unfold tailWord_6371624
  simp only [CollatzResearch.WordTrace]
  refine ⟨116196109534350954794668963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154928146045801273059558617 116196109534350954794668963)
  ·
    refine ⟨174294164301526432192003445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116196109534350954794668963 174294164301526432192003445)
    ·
      refine ⟨16340077903268103018000323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174294164301526432192003445 16340077903268103018000323)
      ·
        refine ⟨24510116854902154527000485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16340077903268103018000323 24510116854902154527000485)
        ·
          refine ⟨4595646910294153973812591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24510116854902154527000485 4595646910294153973812591)
          ·
            refine ⟨6893470365441230960718887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595646910294153973812591 6893470365441230960718887)
            ·
              refine ⟨10340205548161846441078331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6893470365441230960718887 10340205548161846441078331)
              ·
                refine ⟨15510308322242769661617497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10340205548161846441078331 15510308322242769661617497)
                ·
                  refine ⟨11632731241682077246213123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15510308322242769661617497 11632731241682077246213123)
                  ·
                    refine ⟨17449096862523115869319685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11632731241682077246213123 17449096862523115869319685)
                    ·
                      refine ⟨3271705661723084225497441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17449096862523115869319685 3271705661723084225497441)
                      ·
                        rfl

theorem cell23_6371624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_6371624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371624 prefixEnd_6371624 := by exact prefixLift 6371624
  have htrace : WordTrace (prefixWord ++ tailWord_6371624) baseStart_6371624 baseEnd_6371624 := by
    simpa [prefixWord, tailWord_6371624, baseEnd_6371624] using wordTrace_append hprefix tailTrace_6371624
  have hstable : (prefixWord ++ tailWord_6371624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371624).length < 2 ^ (prefixWord ++ tailWord_6371624).sum := by decide
  have hdescent : baseEnd_6371624 < baseStart_6371624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371634 : List Nat := [3, 2, 1, 1, 5, 1, 2, 3, 1, 4]
def baseStart_6371634 : Nat := 118140960795 + 6371634 * 2 ^ 59
def prefixEnd_6371634 : Nat := 4983230072969 + 3 ^ 40 * 6371634 * 2
def baseEnd_6371634 : Nat := 1090570265509876395457465

theorem tailTrace_6371634 : CollatzResearch.WordTrace tailWord_6371634 prefixEnd_6371634 1090570265509876395457465 := by
  unfold tailWord_6371634
  simp only [CollatzResearch.WordTrace]
  refine ⟨58098145949666420324300489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154928389199110454198134637 58098145949666420324300489)
  ·
    refine ⟨43573609462249815243225367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58098145949666420324300489 43573609462249815243225367)
    ·
      refine ⟨65360414193374722864838051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43573609462249815243225367 65360414193374722864838051)
      ·
        refine ⟨98040621290062084297257077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65360414193374722864838051 98040621290062084297257077)
        ·
          refine ⟨9191308245943320402867851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98040621290062084297257077 9191308245943320402867851)
          ·
            refine ⟨13786962368914980604301777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9191308245943320402867851 13786962368914980604301777)
            ·
              refine ⟨10340221776686235453226333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13786962368914980604301777 10340221776686235453226333)
              ·
                refine ⟨3877583166257338294959875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10340221776686235453226333 3877583166257338294959875)
                ·
                  refine ⟨5816374749386007442439813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877583166257338294959875 5816374749386007442439813)
                  ·
                    refine ⟨1090570265509876395457465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5816374749386007442439813 1090570265509876395457465)
                    ·
                      rfl

theorem cell23_6371634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_6371634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371634 prefixEnd_6371634 := by exact prefixLift 6371634
  have htrace : WordTrace (prefixWord ++ tailWord_6371634) baseStart_6371634 baseEnd_6371634 := by
    simpa [prefixWord, tailWord_6371634, baseEnd_6371634] using wordTrace_append hprefix tailTrace_6371634
  have hstable : (prefixWord ++ tailWord_6371634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371634).length < 2 ^ (prefixWord ++ tailWord_6371634).sum := by decide
  have hdescent : baseEnd_6371634 < baseStart_6371634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371663 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 4]
def baseStart_6371663 : Nat := 118140960795 + 6371663 * 2 ^ 59
def prefixEnd_6371663 : Nat := 4983230072969 + 3 ^ 40 * 6371663 * 2
def baseEnd_6371663 : Nat := 3271725687468609572909761

theorem tailTrace_6371663 : CollatzResearch.WordTrace tailWord_6371663 prefixEnd_6371663 3271725687468609572909761 := by
  unfold tailWord_6371663
  simp only [CollatzResearch.WordTrace]
  refine ⟨232393641515560619250007643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154929094343707079500005095 232393641515560619250007643)
  ·
    refine ⟨348590462273340928875011465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232393641515560619250007643 348590462273340928875011465)
    ·
      refine ⟨261442846705005696656258599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348590462273340928875011465 261442846705005696656258599)
      ·
        refine ⟨392164270057508544984387899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261442846705005696656258599 392164270057508544984387899)
        ·
          refine ⟨588246405086262817476581849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392164270057508544984387899 588246405086262817476581849)
          ·
            refine ⟨441184803814697113107436387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588246405086262817476581849 441184803814697113107436387)
            ·
              refine ⟨661777205722045669661154581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441184803814697113107436387 661777205722045669661154581)
              ·
                refine ⟨31020806518220890765366621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 661777205722045669661154581 31020806518220890765366621)
                ·
                  refine ⟨11632802444332834037012483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31020806518220890765366621 11632802444332834037012483)
                  ·
                    refine ⟨17449203666499251055518725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11632802444332834037012483 17449203666499251055518725)
                    ·
                      refine ⟨3271725687468609572909761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17449203666499251055518725 3271725687468609572909761)
                      ·
                        rfl

theorem cell23_6371663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_6371663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371663 prefixEnd_6371663 := by exact prefixLift 6371663
  have htrace : WordTrace (prefixWord ++ tailWord_6371663) baseStart_6371663 baseEnd_6371663 := by
    simpa [prefixWord, tailWord_6371663, baseEnd_6371663] using wordTrace_append hprefix tailTrace_6371663
  have hstable : (prefixWord ++ tailWord_6371663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371663).length < 2 ^ (prefixWord ++ tailWord_6371663).sum := by decide
  have hdescent : baseEnd_6371663 < baseStart_6371663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371683 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 5]
def baseStart_6371683 : Nat := 118140960795 + 6371683 * 2 ^ 59
def prefixEnd_6371683 : Nat := 4983230072969 + 3 ^ 40 * 6371683 * 2
def baseEnd_6371683 : Nat := 3271735957081699494659669

theorem tailTrace_6371683 : CollatzResearch.WordTrace tailWord_6371683 prefixEnd_6371683 3271735957081699494659669 := by
  unfold tailWord_6371683
  simp only [CollatzResearch.WordTrace]
  refine ⟨232394370975488162665735703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154929580650325441777157135 232394370975488162665735703)
  ·
    refine ⟨348591556463232243998603555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232394370975488162665735703 348591556463232243998603555)
    ·
      refine ⟨522887334694848365997905333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348591556463232243998603555 522887334694848365997905333)
      ·
        refine ⟨49020687627642034312303625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 522887334694848365997905333 49020687627642034312303625)
        ·
          refine ⟨36765515720731525734227719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49020687627642034312303625 36765515720731525734227719)
          ·
            refine ⟨55148273581097288601341579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36765515720731525734227719 55148273581097288601341579)
            ·
              refine ⟨82722410371645932902012369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55148273581097288601341579 82722410371645932902012369)
              ·
                refine ⟨62041807778734449676509277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82722410371645932902012369 62041807778734449676509277)
                ·
                  refine ⟨23265677917025418628690979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62041807778734449676509277 23265677917025418628690979)
                  ·
                    refine ⟨34898516875538127943036469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23265677917025418628690979 34898516875538127943036469)
                    ·
                      refine ⟨3271735957081699494659669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34898516875538127943036469 3271735957081699494659669)
                      ·
                        rfl

theorem cell23_6371683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_6371683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371683 prefixEnd_6371683 := by exact prefixLift 6371683
  have htrace : WordTrace (prefixWord ++ tailWord_6371683) baseStart_6371683 baseEnd_6371683 := by
    simpa [prefixWord, tailWord_6371683, baseEnd_6371683] using wordTrace_append hprefix tailTrace_6371683
  have hstable : (prefixWord ++ tailWord_6371683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371683).length < 2 ^ (prefixWord ++ tailWord_6371683).sum := by decide
  have hdescent : baseEnd_6371683 < baseStart_6371683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371724 : List Nat := [2, 2, 1, 2, 1, 6, 2, 1, 2, 4]
def baseStart_6371724 : Nat := 118140960795 + 6371724 * 2 ^ 59
def prefixEnd_6371724 : Nat := 4983230072969 + 3 ^ 40 * 6371724 * 2
def baseEnd_6371724 : Nat := 1090585669929511278082327

theorem tailTrace_6371724 : CollatzResearch.WordTrace tailWord_6371724 prefixEnd_6371724 1090585669929511278082327 := by
  unfold tailWord_6371724
  simp only [CollatzResearch.WordTrace]
  refine ⟨116197933184169813333989113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154930577578893084445318817 116197933184169813333989113)
  ·
    refine ⟨87148449888127360000491835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116197933184169813333989113 87148449888127360000491835)
    ·
      refine ⟨130722674832191040000737753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87148449888127360000491835 130722674832191040000737753)
      ·
        refine ⟨98042006124143280000553315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130722674832191040000737753 98042006124143280000553315)
        ·
          refine ⟨147063009186214920000829973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98042006124143280000553315 147063009186214920000829973)
          ·
            refine ⟨6893578555603824375038905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147063009186214920000829973 6893578555603824375038905)
            ·
              refine ⟨5170183916702868281279179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6893578555603824375038905 5170183916702868281279179)
              ·
                refine ⟨7755275875054302421918769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170183916702868281279179 7755275875054302421918769)
                ·
                  refine ⟨5816456906290726816439077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7755275875054302421918769 5816456906290726816439077)
                  ·
                    refine ⟨1090585669929511278082327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5816456906290726816439077 1090585669929511278082327)
                    ·
                      rfl

theorem cell23_6371724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_6371724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371724 prefixEnd_6371724 := by exact prefixLift 6371724
  have htrace : WordTrace (prefixWord ++ tailWord_6371724) baseStart_6371724 baseEnd_6371724 := by
    simpa [prefixWord, tailWord_6371724, baseEnd_6371724] using wordTrace_append hprefix tailTrace_6371724
  have hstable : (prefixWord ++ tailWord_6371724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371724).length < 2 ^ (prefixWord ++ tailWord_6371724).sum := by decide
  have hdescent : baseEnd_6371724 < baseStart_6371724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371753 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 4, 3, 4]
def baseStart_6371753 : Nat := 118140960795 + 6371753 * 2 ^ 59
def prefixEnd_6371753 : Nat := 4983230072969 + 3 ^ 40 * 6371753 * 2
def baseEnd_6371753 : Nat := 3271771900727514220784347

theorem tailTrace_6371753 : CollatzResearch.WordTrace tailWord_6371753 prefixEnd_6371753 3271771900727514220784347 := by
  unfold tailWord_6371753
  simp only [CollatzResearch.WordTrace]
  refine ⟨232396924085234564620783913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154931282723489709747189275 232396924085234564620783913)
  ·
    refine ⟨174297693063925923465587935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232396924085234564620783913 174297693063925923465587935)
    ·
      refine ⟨261446539595888885198381903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174297693063925923465587935 261446539595888885198381903)
      ·
        refine ⟨392169809393833327797572855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261446539595888885198381903 392169809393833327797572855)
        ·
          refine ⟨588254714090749991696359283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392169809393833327797572855 588254714090749991696359283)
          ·
            refine ⟨882382071136124987544538925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588254714090749991696359283 882382071136124987544538925)
            ·
              refine ⟨330893276676046870329202097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 882382071136124987544538925 330893276676046870329202097)
              ·
                refine ⟨248169957507035152746901573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330893276676046870329202097 248169957507035152746901573)
                ·
                  refine ⟨46531867032569091140044045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248169957507035152746901573 46531867032569091140044045)
                  ·
                    refine ⟨17449450137213409177516517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46531867032569091140044045 17449450137213409177516517)
                    ·
                      refine ⟨3271771900727514220784347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17449450137213409177516517 3271771900727514220784347)
                      ·
                        rfl

theorem cell23_6371753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_6371753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371753 prefixEnd_6371753 := by exact prefixLift 6371753
  have htrace : WordTrace (prefixWord ++ tailWord_6371753) baseStart_6371753 baseEnd_6371753 := by
    simpa [prefixWord, tailWord_6371753, baseEnd_6371753] using wordTrace_append hprefix tailTrace_6371753
  have hstable : (prefixWord ++ tailWord_6371753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371753).length < 2 ^ (prefixWord ++ tailWord_6371753).sum := by decide
  have hdescent : baseEnd_6371753 < baseStart_6371753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371754 : List Nat := [3, 1, 6, 1, 2, 10]
def baseStart_6371754 : Nat := 118140960795 + 6371754 * 2 ^ 59
def prefixEnd_6371754 : Nat := 4983230072969 + 3 ^ 40 * 6371754 * 2
def baseEnd_6371754 : Nat := 13464084009087114061201

theorem tailTrace_6371754 : CollatzResearch.WordTrace tailWord_6371754 prefixEnd_6371754 13464084009087114061201 := by
  unfold tailWord_6371754
  simp only [CollatzResearch.WordTrace]
  refine ⟨58099240139557735447892579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154931307038820627861046877 58099240139557735447892579)
  ·
    refine ⟨87148860209336603171838869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58099240139557735447892579 87148860209336603171838869)
    ·
      refine ⟨4085102822312653273679947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87148860209336603171838869 4085102822312653273679947)
      ·
        refine ⟨6127654233468979910519921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4085102822312653273679947 6127654233468979910519921)
        ·
          refine ⟨4595740675101734932889941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6127654233468979910519921 4595740675101734932889941)
          ·
            refine ⟨13464084009087114061201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4595740675101734932889941 13464084009087114061201)
            ·
              rfl

theorem cell23_6371754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 10].length) (baseStart_6371754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371754 prefixEnd_6371754 := by exact prefixLift 6371754
  have htrace : WordTrace (prefixWord ++ tailWord_6371754) baseStart_6371754 baseEnd_6371754 := by
    simpa [prefixWord, tailWord_6371754, baseEnd_6371754] using wordTrace_append hprefix tailTrace_6371754
  have hstable : (prefixWord ++ tailWord_6371754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371754).length < 2 ^ (prefixWord ++ tailWord_6371754).sum := by decide
  have hdescent : baseEnd_6371754 < baseStart_6371754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371765 : List Nat := [1, 3, 3, 2, 3, 2, 2, 2, 1, 2, 2]
def baseStart_6371765 : Nat := 118140960795 + 6371765 * 2 ^ 59
def prefixEnd_6371765 : Nat := 4983230072969 + 3 ^ 40 * 6371765 * 2
def baseEnd_6371765 : Nat := 3271778062495368173834293

theorem tailTrace_6371765 : CollatzResearch.WordTrace tailWord_6371765 prefixEnd_6371765 3271778062495368173834293 := by
  unfold tailWord_6371765
  simp only [CollatzResearch.WordTrace]
  refine ⟨232397361761191090670220749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154931574507460727113480499 232397361761191090670220749)
  ·
    refine ⟨87149010660446659001332781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232397361761191090670220749 87149010660446659001332781)
    ·
      refine ⟨32680878997667497125499793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87149010660446659001332781 32680878997667497125499793)
      ·
        refine ⟨24510659248250622844124845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32680878997667497125499793 24510659248250622844124845)
        ·
          refine ⟨9191497218093983566546817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24510659248250622844124845 9191497218093983566546817)
          ·
            refine ⟨6893622913570487674910113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9191497218093983566546817 6893622913570487674910113)
            ·
              refine ⟨5170217185177865756182585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6893622913570487674910113 5170217185177865756182585)
              ·
                refine ⟨3877662888883399317136939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5170217185177865756182585 3877662888883399317136939)
                ·
                  refine ⟨5816494333325098975705409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877662888883399317136939 5816494333325098975705409)
                  ·
                    refine ⟨4362370749993824231779057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5816494333325098975705409 4362370749993824231779057)
                    ·
                      refine ⟨3271778062495368173834293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362370749993824231779057 3271778062495368173834293)
                      ·
                        rfl

theorem cell23_6371765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_6371765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371765 prefixEnd_6371765 := by exact prefixLift 6371765
  have htrace : WordTrace (prefixWord ++ tailWord_6371765) baseStart_6371765 baseEnd_6371765 := by
    simpa [prefixWord, tailWord_6371765, baseEnd_6371765] using wordTrace_append hprefix tailTrace_6371765
  have hstable : (prefixWord ++ tailWord_6371765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371765).length < 2 ^ (prefixWord ++ tailWord_6371765).sum := by decide
  have hdescent : baseEnd_6371765 < baseStart_6371765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371787 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 6, 2, 2]
def baseStart_6371787 : Nat := 118140960795 + 6371787 * 2 ^ 59
def prefixEnd_6371787 : Nat := 4983230072969 + 3 ^ 40 * 6371787 * 2
def baseEnd_6371787 : Nat := 3271789359069767087759191

theorem tailTrace_6371787 : CollatzResearch.WordTrace tailWord_6371787 prefixEnd_6371787 3271789359069767087759191 := by
  unfold tailWord_6371787
  simp only [CollatzResearch.WordTrace]
  refine ⟨232398164167111388427521615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154932109444740925618347743 232398164167111388427521615)
  ·
    refine ⟨348597246250667082641282423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232398164167111388427521615 348597246250667082641282423)
    ·
      refine ⟨522895869376000623961923635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348597246250667082641282423 522895869376000623961923635)
      ·
        refine ⟨784343804064000935942885453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522895869376000623961923635 784343804064000935942885453)
        ·
          refine ⟨294128926524000350978582045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 784343804064000935942885453 294128926524000350978582045)
          ·
            refine ⟨110298347446500131616968267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294128926524000350978582045 110298347446500131616968267)
            ·
              refine ⟨165447521169750197425452401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110298347446500131616968267 165447521169750197425452401)
              ·
                refine ⟨124085640877312648069089301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165447521169750197425452401 124085640877312648069089301)
                ·
                  refine ⟨5816514416124030378238561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124085640877312648069089301 5816514416124030378238561)
                  ·
                    refine ⟨4362385812093022783678921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5816514416124030378238561 4362385812093022783678921)
                    ·
                      refine ⟨3271789359069767087759191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362385812093022783678921 3271789359069767087759191)
                      ·
                        rfl

theorem cell23_6371787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 2, 2].length) (baseStart_6371787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371787 prefixEnd_6371787 := by exact prefixLift 6371787
  have htrace : WordTrace (prefixWord ++ tailWord_6371787) baseStart_6371787 baseEnd_6371787 := by
    simpa [prefixWord, tailWord_6371787, baseEnd_6371787] using wordTrace_append hprefix tailTrace_6371787
  have hstable : (prefixWord ++ tailWord_6371787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371787).length < 2 ^ (prefixWord ++ tailWord_6371787).sum := by decide
  have hdescent : baseEnd_6371787 < baseStart_6371787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371790 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_6371790 : Nat := 118140960795 + 6371790 * 2 ^ 59
def prefixEnd_6371790 : Nat := 4983230072969 + 3 ^ 40 * 6371790 * 2
def baseEnd_6371790 : Nat := 3271790899511730576021677

theorem tailTrace_6371790 : CollatzResearch.WordTrace tailWord_6371790 prefixEnd_6371790 3271790899511730576021677 := by
  unfold tailWord_6371790
  simp only [CollatzResearch.WordTrace]
  refine ⟨29049784198262564992485103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154932182390733679959920549 29049784198262564992485103)
  ·
    refine ⟨43574676297393847488727655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29049784198262564992485103 43574676297393847488727655)
    ·
      refine ⟨65362014446090771233091483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43574676297393847488727655 65362014446090771233091483)
      ·
        refine ⟨98043021669136156849637225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65362014446090771233091483 98043021669136156849637225)
        ·
          refine ⟨73532266251852117637227919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98043021669136156849637225 73532266251852117637227919)
          ·
            refine ⟨110298399377778176455841879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73532266251852117637227919 110298399377778176455841879)
            ·
              refine ⟨165447599066667264683762819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110298399377778176455841879 165447599066667264683762819)
              ·
                refine ⟨248171398600000897025644229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165447599066667264683762819 248171398600000897025644229)
                ·
                  refine ⟨46532137237500168192308293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248171398600000897025644229 46532137237500168192308293)
                  ·
                    refine ⟨8724775732031281536057805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46532137237500168192308293 8724775732031281536057805)
                    ·
                      refine ⟨3271790899511730576021677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8724775732031281536057805 3271790899511730576021677)
                      ·
                        rfl

theorem cell23_6371790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_6371790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371790 prefixEnd_6371790 := by exact prefixLift 6371790
  have htrace : WordTrace (prefixWord ++ tailWord_6371790) baseStart_6371790 baseEnd_6371790 := by
    simpa [prefixWord, tailWord_6371790, baseEnd_6371790] using wordTrace_append hprefix tailTrace_6371790
  have hstable : (prefixWord ++ tailWord_6371790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371790).length < 2 ^ (prefixWord ++ tailWord_6371790).sum := by decide
  have hdescent : baseEnd_6371790 < baseStart_6371790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371820 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 3]
def baseStart_6371820 : Nat := 118140960795 + 6371820 * 2 ^ 59
def prefixEnd_6371820 : Nat := 4983230072969 + 3 ^ 40 * 6371820 * 2
def baseEnd_6371820 : Nat := 3271806303931365458646539

theorem tailTrace_6371820 : CollatzResearch.WordTrace tailWord_6371820 prefixEnd_6371820 3271806303931365458646539 := by
  unfold tailWord_6371820
  simp only [CollatzResearch.WordTrace]
  refine ⟨116199683887995917531736457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154932911850661223375648609 116199683887995917531736457)
  ·
    refine ⟨87149762915996938148802343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116199683887995917531736457 87149762915996938148802343)
    ·
      refine ⟨130724644373995407223203515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87149762915996938148802343 130724644373995407223203515)
      ·
        refine ⟨196086966560993110834805273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130724644373995407223203515 196086966560993110834805273)
        ·
          refine ⟨147065224920744833126103955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196086966560993110834805273 147065224920744833126103955)
          ·
            refine ⟨220597837381117249689155933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147065224920744833126103955 220597837381117249689155933)
            ·
              refine ⟨82724189017918968633433475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220597837381117249689155933 82724189017918968633433475)
              ·
                refine ⟨124086283526878452950150213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82724189017918968633433475 124086283526878452950150213)
                ·
                  refine ⟨23266178161289709928153165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124086283526878452950150213 23266178161289709928153165)
                  ·
                    refine ⟨8724816810483641223057437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23266178161289709928153165 8724816810483641223057437)
                    ·
                      refine ⟨3271806303931365458646539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8724816810483641223057437 3271806303931365458646539)
                      ·
                        rfl

theorem cell23_6371820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_6371820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371820 prefixEnd_6371820 := by exact prefixLift 6371820
  have htrace : WordTrace (prefixWord ++ tailWord_6371820) baseStart_6371820 baseEnd_6371820 := by
    simpa [prefixWord, tailWord_6371820, baseEnd_6371820] using wordTrace_append hprefix tailTrace_6371820
  have hstable : (prefixWord ++ tailWord_6371820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371820).length < 2 ^ (prefixWord ++ tailWord_6371820).sum := by decide
  have hdescent : baseEnd_6371820 < baseStart_6371820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371821 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_6371821 : Nat := 118140960795 + 6371821 * 2 ^ 59
def prefixEnd_6371821 : Nat := 4983230072969 + 3 ^ 40 * 6371821 * 2
def baseEnd_6371821 : Nat := 3271806817412019954734035

theorem tailTrace_6371821 : CollatzResearch.WordTrace tailWord_6371821 prefixEnd_6371821 3271806817412019954734035 := by
  unfold tailWord_6371821
  simp only [CollatzResearch.WordTrace]
  refine ⟨232399404248988212234259317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154932936165992141489506211 232399404248988212234259317)
  ·
    refine ⟨21787444148342644896961811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232399404248988212234259317 21787444148342644896961811)
    ·
      refine ⟨32681166222513967345442717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21787444148342644896961811 32681166222513967345442717)
      ·
        refine ⟨12255437333442737754541019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32681166222513967345442717 12255437333442737754541019)
        ·
          refine ⟨18383156000164106631811529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12255437333442737754541019 18383156000164106631811529)
          ·
            refine ⟨13787367000123079973858647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18383156000164106631811529 13787367000123079973858647)
            ·
              refine ⟨20681050500184619960787971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13787367000123079973858647 20681050500184619960787971)
              ·
                refine ⟨31021575750276929941181957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20681050500184619960787971 31021575750276929941181957)
                ·
                  refine ⟨5816545453176924363971617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31021575750276929941181957 5816545453176924363971617)
                  ·
                    refine ⟨4362409089882693272978713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5816545453176924363971617 4362409089882693272978713)
                    ·
                      refine ⟨3271806817412019954734035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362409089882693272978713 3271806817412019954734035)
                      ·
                        rfl

theorem cell23_6371821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_6371821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371821 prefixEnd_6371821 := by exact prefixLift 6371821
  have htrace : WordTrace (prefixWord ++ tailWord_6371821) baseStart_6371821 baseEnd_6371821 := by
    simpa [prefixWord, tailWord_6371821, baseEnd_6371821] using wordTrace_append hprefix tailTrace_6371821
  have hstable : (prefixWord ++ tailWord_6371821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371821).length < 2 ^ (prefixWord ++ tailWord_6371821).sum := by decide
  have hdescent : baseEnd_6371821 < baseStart_6371821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371877 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 4, 4, 2]
def baseStart_6371877 : Nat := 118140960795 + 6371877 * 2 ^ 59
def prefixEnd_6371877 : Nat := 4983230072969 + 3 ^ 40 * 6371877 * 2
def baseEnd_6371877 : Nat := 3271835572328671735633777

theorem tailTrace_6371877 : CollatzResearch.WordTrace tailWord_6371877 prefixEnd_6371877 3271835572328671735633777 := by
  unfold tailWord_6371877
  simp only [CollatzResearch.WordTrace]
  refine ⟨232401446736785333798297885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154934297824523555865531923 232401446736785333798297885)
  ·
    refine ⟨87150542526294500174361707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232401446736785333798297885 87150542526294500174361707)
    ·
      refine ⟨130725813789441750261542561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87150542526294500174361707 130725813789441750261542561)
      ·
        refine ⟨98044360342081312696156921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130725813789441750261542561 98044360342081312696156921)
        ·
          refine ⟨73533270256560984522117691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98044360342081312696156921 73533270256560984522117691)
          ·
            refine ⟨110299905384841476783176537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73533270256560984522117691 110299905384841476783176537)
            ·
              refine ⟨82724929038631107587382403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110299905384841476783176537 82724929038631107587382403)
              ·
                refine ⟨124087393557946661381073605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82724929038631107587382403 124087393557946661381073605)
                ·
                  refine ⟨23266386292114999008951301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124087393557946661381073605 23266386292114999008951301)
                  ·
                    refine ⟨4362447429771562314178369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23266386292114999008951301 4362447429771562314178369)
                    ·
                      refine ⟨3271835572328671735633777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362447429771562314178369 3271835572328671735633777)
                      ·
                        rfl

theorem cell23_6371877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_6371877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371877 prefixEnd_6371877 := by exact prefixLift 6371877
  have htrace : WordTrace (prefixWord ++ tailWord_6371877) baseStart_6371877 baseEnd_6371877 := by
    simpa [prefixWord, tailWord_6371877, baseEnd_6371877] using wordTrace_append hprefix tailTrace_6371877
  have hstable : (prefixWord ++ tailWord_6371877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371877).length < 2 ^ (prefixWord ++ tailWord_6371877).sum := by decide
  have hdescent : baseEnd_6371877 < baseStart_6371877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371890 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_6371890 : Nat := 118140960795 + 6371890 * 2 ^ 59
def prefixEnd_6371890 : Nat := 4983230072969 + 3 ^ 40 * 6371890 * 2
def baseEnd_6371890 : Nat := 3271842247577180184771217

theorem tailTrace_6371890 : CollatzResearch.WordTrace tailWord_6371890 prefixEnd_6371890 3271842247577180184771217 := by
  unfold tailWord_6371890
  simp only [CollatzResearch.WordTrace]
  refine ⟨58100480221434559254630281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154934613923825491345680749 58100480221434559254630281)
  ·
    refine ⟨43575360166075919440972711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58100480221434559254630281 43575360166075919440972711)
    ·
      refine ⟨65363040249113879161459067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43575360166075919440972711 65363040249113879161459067)
      ·
        refine ⟨98044560373670818742188601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65363040249113879161459067 98044560373670818742188601)
        ·
          refine ⟨73533420280253114056641451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98044560373670818742188601 73533420280253114056641451)
          ·
            refine ⟨110300130420379671084962177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73533420280253114056641451 110300130420379671084962177)
            ·
              refine ⟨82725097815284753313721633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110300130420379671084962177 82725097815284753313721633)
              ·
                refine ⟨62043823361463564985291225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82725097815284753313721633 62043823361463564985291225)
                ·
                  refine ⟨46532867521097673738968419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62043823361463564985291225 46532867521097673738968419)
                  ·
                    refine ⟨69799301281646510608452629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46532867521097673738968419 69799301281646510608452629)
                    ·
                      refine ⟨3271842247577180184771217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69799301281646510608452629 3271842247577180184771217)
                      ·
                        rfl

theorem cell23_6371890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_6371890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371890 prefixEnd_6371890 := by exact prefixLift 6371890
  have htrace : WordTrace (prefixWord ++ tailWord_6371890) baseStart_6371890 baseEnd_6371890 := by
    simpa [prefixWord, tailWord_6371890, baseEnd_6371890] using wordTrace_append hprefix tailTrace_6371890
  have hstable : (prefixWord ++ tailWord_6371890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371890).length < 2 ^ (prefixWord ++ tailWord_6371890).sum := by decide
  have hdescent : baseEnd_6371890 < baseStart_6371890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371897 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 4, 2, 3]
def baseStart_6371897 : Nat := 118140960795 + 6371897 * 2 ^ 59
def prefixEnd_6371897 : Nat := 4983230072969 + 3 ^ 40 * 6371897 * 2
def baseEnd_6371897 : Nat := 3271845841941761657383685

theorem tailTrace_6371897 : CollatzResearch.WordTrace tailWord_6371897 prefixEnd_6371897 3271845841941761657383685 := by
  unfold tailWord_6371897
  simp only [CollatzResearch.WordTrace]
  refine ⟨232402176196712877214025945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154934784131141918142683963 232402176196712877214025945)
  ·
    refine ⟨174301632147534657910519459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232402176196712877214025945 174301632147534657910519459)
    ·
      refine ⟨261452448221301986865779189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174301632147534657910519459 261452448221301986865779189)
      ·
        refine ⟨24511167020747061268666799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 261452448221301986865779189 24511167020747061268666799)
        ·
          refine ⟨36766750531120591903000199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24511167020747061268666799 36766750531120591903000199)
          ·
            refine ⟨55150125796680887854500299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36766750531120591903000199 55150125796680887854500299)
            ·
              refine ⟨82725188695021331781750449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55150125796680887854500299 82725188695021331781750449)
              ·
                refine ⟨62043891521265998836312837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82725188695021331781750449 62043891521265998836312837)
                ·
                  refine ⟨11633229660237374781808657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62043891521265998836312837 11633229660237374781808657)
                  ·
                    refine ⟨8724922245178031086356493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11633229660237374781808657 8724922245178031086356493)
                    ·
                      refine ⟨3271845841941761657383685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8724922245178031086356493 3271845841941761657383685)
                      ·
                        rfl

theorem cell23_6371897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_6371897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371897 prefixEnd_6371897 := by exact prefixLift 6371897
  have htrace : WordTrace (prefixWord ++ tailWord_6371897) baseStart_6371897 baseEnd_6371897 := by
    simpa [prefixWord, tailWord_6371897, baseEnd_6371897] using wordTrace_append hprefix tailTrace_6371897
  have hstable : (prefixWord ++ tailWord_6371897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371897).length < 2 ^ (prefixWord ++ tailWord_6371897).sum := by decide
  have hdescent : baseEnd_6371897 < baseStart_6371897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371908 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 2, 5]
def baseStart_6371908 : Nat := 118140960795 + 6371908 * 2 ^ 59
def prefixEnd_6371908 : Nat := 4983230072969 + 3 ^ 40 * 6371908 * 2
def baseEnd_6371908 : Nat := 1090617163409653704782045

theorem tailTrace_6371908 : CollatzResearch.WordTrace tailWord_6371908 prefixEnd_6371908 1090617163409653704782045 := by
  unfold tailWord_6371908
  simp only [CollatzResearch.WordTrace]
  refine ⟨116201288699836513046338189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154935051599782017395117585 116201288699836513046338189)
  ·
    refine ⟨43575483262438692392376821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116201288699836513046338189 43575483262438692392376821)
    ·
      refine ⟨4085201555853627411785327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43575483262438692392376821 4085201555853627411785327)
      ·
        refine ⟨6127802333780441117677991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4085201555853627411785327 6127802333780441117677991)
        ·
          refine ⟨9191703500670661676516987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6127802333780441117677991 9191703500670661676516987)
          ·
            refine ⟨13787555251005992514775481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9191703500670661676516987 13787555251005992514775481)
            ·
              refine ⟨10340666438254494386081611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13787555251005992514775481 10340666438254494386081611)
              ·
                refine ⟨15510999657381741579122417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10340666438254494386081611 15510999657381741579122417)
                ·
                  refine ⟨11633249743036306184341813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15510999657381741579122417 11633249743036306184341813)
                  ·
                    refine ⟨1090617163409653704782045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11633249743036306184341813 1090617163409653704782045)
                    ·
                      rfl

theorem cell23_6371908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_6371908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371908 prefixEnd_6371908 := by exact prefixLift 6371908
  have htrace : WordTrace (prefixWord ++ tailWord_6371908) baseStart_6371908 baseEnd_6371908 := by
    simpa [prefixWord, tailWord_6371908, baseEnd_6371908] using wordTrace_append hprefix tailTrace_6371908
  have hstable : (prefixWord ++ tailWord_6371908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371908).length < 2 ^ (prefixWord ++ tailWord_6371908).sum := by decide
  have hdescent : baseEnd_6371908 < baseStart_6371908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371914 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_6371914 : Nat := 118140960795 + 6371914 * 2 ^ 59
def prefixEnd_6371914 : Nat := 4983230072969 + 3 ^ 40 * 6371914 * 2
def baseEnd_6371914 : Nat := 3271854571112888090871107

theorem tailTrace_6371914 : CollatzResearch.WordTrace tailWord_6371914 prefixEnd_6371914 3271854571112888090871107 := by
  unfold tailWord_6371914
  simp only [CollatzResearch.WordTrace]
  refine ⟨58100699059412822279348699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154935197491767526078263197 58100699059412822279348699)
  ·
    refine ⟨87151048589119233419023049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58100699059412822279348699 87151048589119233419023049)
    ·
      refine ⟨65363286441839425064267287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87151048589119233419023049 65363286441839425064267287)
      ·
        refine ⟨98044929662759137596400931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65363286441839425064267287 98044929662759137596400931)
        ·
          refine ⟨147067394494138706394601397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98044929662759137596400931 147067394494138706394601397)
          ·
            refine ⟨13787568233825503724493881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147067394494138706394601397 13787568233825503724493881)
            ·
              refine ⟨10340676175369127793370411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13787568233825503724493881 10340676175369127793370411)
              ·
                refine ⟨15511014263053691690055617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10340676175369127793370411 15511014263053691690055617)
                ·
                  refine ⟨11633260697290268767541713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15511014263053691690055617 11633260697290268767541713)
                  ·
                    refine ⟨8724945522967701575656285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11633260697290268767541713 8724945522967701575656285)
                    ·
                      refine ⟨3271854571112888090871107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8724945522967701575656285 3271854571112888090871107)
                      ·
                        rfl

theorem cell23_6371914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_6371914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371914 prefixEnd_6371914 := by exact prefixLift 6371914
  have htrace : WordTrace (prefixWord ++ tailWord_6371914) baseStart_6371914 baseEnd_6371914 := by
    simpa [prefixWord, tailWord_6371914, baseEnd_6371914] using wordTrace_append hprefix tailTrace_6371914
  have hstable : (prefixWord ++ tailWord_6371914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371914).length < 2 ^ (prefixWord ++ tailWord_6371914).sum := by decide
  have hdescent : baseEnd_6371914 < baseStart_6371914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371960 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 5, 6]
def baseStart_6371960 : Nat := 118140960795 + 6371960 * 2 ^ 59
def prefixEnd_6371960 : Nat := 4983230072969 + 3 ^ 40 * 6371960 * 2
def baseEnd_6371960 : Nat := 1090626063740998303631965

theorem tailTrace_6371960 : CollatzResearch.WordTrace tailWord_6371960 prefixEnd_6371960 1090626063740998303631965 := by
  unfold tailWord_6371960
  simp only [CollatzResearch.WordTrace]
  refine ⟨116202236997742319486784667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154936315996989759315712889 116202236997742319486784667)
  ·
    refine ⟨174303355496613479230177001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116202236997742319486784667 174303355496613479230177001)
    ·
      refine ⟨130727516622460109422632751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174303355496613479230177001 130727516622460109422632751)
      ·
        refine ⟨196091274933690164133949127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130727516622460109422632751 196091274933690164133949127)
        ·
          refine ⟨294136912400535246200923691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196091274933690164133949127 294136912400535246200923691)
          ·
            refine ⟨441205368600802869301385537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294136912400535246200923691 441205368600802869301385537)
            ·
              refine ⟨330904026450602151976039153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441205368600802869301385537 330904026450602151976039153)
              ·
                refine ⟨248178019837951613982029365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330904026450602151976039153 248178019837951613982029365)
                ·
                  refine ⟨23266689359807963810815253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 248178019837951613982029365 23266689359807963810815253)
                  ·
                    refine ⟨1090626063740998303631965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23266689359807963810815253 1090626063740998303631965)
                    ·
                      rfl

theorem cell23_6371960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_6371960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371960 prefixEnd_6371960 := by exact prefixLift 6371960
  have htrace : WordTrace (prefixWord ++ tailWord_6371960) baseStart_6371960 baseEnd_6371960 := by
    simpa [prefixWord, tailWord_6371960, baseEnd_6371960] using wordTrace_append hprefix tailTrace_6371960
  have hstable : (prefixWord ++ tailWord_6371960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371960).length < 2 ^ (prefixWord ++ tailWord_6371960).sum := by decide
  have hdescent : baseEnd_6371960 < baseStart_6371960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371967 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 1, 8, 2]
def baseStart_6371967 : Nat := 118140960795 + 6371967 * 2 ^ 59
def prefixEnd_6371967 : Nat := 4983230072969 + 3 ^ 40 * 6371967 * 2
def baseEnd_6371967 : Nat := 3271881785587576383508363

theorem tailTrace_6371967 : CollatzResearch.WordTrace tailWord_6371967 prefixEnd_6371967 3271881785587576383508363 := by
  unfold tailWord_6371967
  simp only [CollatzResearch.WordTrace]
  refine ⟨232404729306459279169074155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154936486204306186112716103 232404729306459279169074155)
  ·
    refine ⟨348607093959688918753611233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232404729306459279169074155 348607093959688918753611233)
    ·
      refine ⟨261455320469766689065208425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348607093959688918753611233 261455320469766689065208425)
      ·
        refine ⟨196091490352325016798906319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261455320469766689065208425 196091490352325016798906319)
        ·
          refine ⟨294137235528487525198359479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196091490352325016798906319 294137235528487525198359479)
          ·
            refine ⟨441205853292731287797539219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294137235528487525198359479 441205853292731287797539219)
            ·
              refine ⟨661808779939096931696308829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441205853292731287797539219 661808779939096931696308829)
              ·
                refine ⟨248178292477161349386115811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 661808779939096931696308829 248178292477161349386115811)
                ·
                  refine ⟨372267438715742024079173717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248178292477161349386115811 372267438715742024079173717)
                  ·
                    refine ⟨4362509047450101844677817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 372267438715742024079173717 4362509047450101844677817)
                    ·
                      refine ⟨3271881785587576383508363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362509047450101844677817 3271881785587576383508363)
                      ·
                        rfl

theorem cell23_6371967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 8, 2].length) (baseStart_6371967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371967 prefixEnd_6371967 := by exact prefixLift 6371967
  have htrace : WordTrace (prefixWord ++ tailWord_6371967) baseStart_6371967 baseEnd_6371967 := by
    simpa [prefixWord, tailWord_6371967, baseEnd_6371967] using wordTrace_append hprefix tailTrace_6371967
  have hstable : (prefixWord ++ tailWord_6371967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371967).length < 2 ^ (prefixWord ++ tailWord_6371967).sum := by decide
  have hdescent : baseEnd_6371967 < baseStart_6371967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371977 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 4, 4]
def baseStart_6371977 : Nat := 118140960795 + 6371977 * 2 ^ 59
def prefixEnd_6371977 : Nat := 4983230072969 + 3 ^ 40 * 6371977 * 2
def baseEnd_6371977 : Nat := 1090628973464707114794439

theorem tailTrace_6371977 : CollatzResearch.WordTrace tailWord_6371977 prefixEnd_6371977 1090628973464707114794439 := by
  unfold tailWord_6371977
  simp only [CollatzResearch.WordTrace]
  refine ⟨232405094036423050876938185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154936729357615367251292123 232405094036423050876938185)
  ·
    refine ⟨174303820527317288157703639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232405094036423050876938185 174303820527317288157703639)
    ·
      refine ⟨261455730790975932236555459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174303820527317288157703639 261455730790975932236555459)
      ·
        refine ⟨392183596186463898354833189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261455730790975932236555459 392183596186463898354833189)
        ·
          refine ⟨73534424284961980941531223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 392183596186463898354833189 73534424284961980941531223)
          ·
            refine ⟨110301636427442971412296835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73534424284961980941531223 110301636427442971412296835)
            ·
              refine ⟨165452454641164457118445253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110301636427442971412296835 165452454641164457118445253)
              ·
                refine ⟨31022335245218335709708485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165452454641164457118445253 31022335245218335709708485)
                ·
                  refine ⟨5816687858478437945570341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31022335245218335709708485 5816687858478437945570341)
                  ·
                    refine ⟨1090628973464707114794439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5816687858478437945570341 1090628973464707114794439)
                    ·
                      rfl

theorem cell23_6371977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 4].length) (baseStart_6371977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371977 prefixEnd_6371977 := by exact prefixLift 6371977
  have htrace : WordTrace (prefixWord ++ tailWord_6371977) baseStart_6371977 baseEnd_6371977 := by
    simpa [prefixWord, tailWord_6371977, baseEnd_6371977] using wordTrace_append hprefix tailTrace_6371977
  have hstable : (prefixWord ++ tailWord_6371977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371977).length < 2 ^ (prefixWord ++ tailWord_6371977).sum := by decide
  have hdescent : baseEnd_6371977 < baseStart_6371977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371997 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_6371997 : Nat := 118140960795 + 6371997 * 2 ^ 59
def prefixEnd_6371997 : Nat := 4983230072969 + 3 ^ 40 * 6371997 * 2
def baseEnd_6371997 : Nat := 3271897190007211266133225

theorem tailTrace_6371997 : CollatzResearch.WordTrace tailWord_6371997 prefixEnd_6371997 3271897190007211266133225 := by
  unfold tailWord_6371997
  simp only [CollatzResearch.WordTrace]
  refine ⟨232405823496350594292666245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154937215664233729528444163 232405823496350594292666245)
  ·
    refine ⟨43576091905565736429874921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232405823496350594292666245 43576091905565736429874921)
    ·
      refine ⟨32682068929174302322406191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43576091905565736429874921 32682068929174302322406191)
      ·
        refine ⟨49023103393761453483609287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32682068929174302322406191 49023103393761453483609287)
        ·
          refine ⟨73534655090642180225413931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49023103393761453483609287 73534655090642180225413931)
          ·
            refine ⟨110301982635963270338120897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73534655090642180225413931 110301982635963270338120897)
            ·
              refine ⟨82726486976972452753590673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110301982635963270338120897 82726486976972452753590673)
              ·
                refine ⟨62044865232729339565193005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82726486976972452753590673 62044865232729339565193005)
                ·
                  refine ⟨23266824462273502336947377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62044865232729339565193005 23266824462273502336947377)
                  ·
                    refine ⟨17450118346705126752710533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23266824462273502336947377 17450118346705126752710533)
                    ·
                      refine ⟨3271897190007211266133225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17450118346705126752710533 3271897190007211266133225)
                      ·
                        rfl

theorem cell23_6371997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_6371997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371997 prefixEnd_6371997 := by exact prefixLift 6371997
  have htrace : WordTrace (prefixWord ++ tailWord_6371997) baseStart_6371997 baseEnd_6371997 := by
    simpa [prefixWord, tailWord_6371997, baseEnd_6371997] using wordTrace_append hprefix tailTrace_6371997
  have hstable : (prefixWord ++ tailWord_6371997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371997).length < 2 ^ (prefixWord ++ tailWord_6371997).sum := by decide
  have hdescent : baseEnd_6371997 < baseStart_6371997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372021 : List Nat := [1, 3, 3, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_6372021 : Nat := 118140960795 + 6372021 * 2 ^ 59
def prefixEnd_6372021 : Nat := 4983230072969 + 3 ^ 40 * 6372021 * 2
def baseEnd_6372021 : Nat := 3271909513542919172233115

theorem tailTrace_6372021 : CollatzResearch.WordTrace tailWord_6372021 prefixEnd_6372021 3271909513542919172233115 := by
  unfold tailWord_6372021
  simp only [CollatzResearch.WordTrace]
  refine ⟨232406698848263646391539917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154937799232175764261026611 232406698848263646391539917)
  ·
    refine ⟨87152512068098867396827469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232406698848263646391539917 87152512068098867396827469)
    ·
      refine ⟨32682192025537075273810301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87152512068098867396827469 32682192025537075273810301)
      ·
        refine ⟨12255822009576403227678863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32682192025537075273810301 12255822009576403227678863)
        ·
          refine ⟨18383733014364604841518295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12255822009576403227678863 18383733014364604841518295)
          ·
            refine ⟨27575599521546907262277443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18383733014364604841518295 27575599521546907262277443)
            ·
              refine ⟨41363399282320360893416165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27575599521546907262277443 41363399282320360893416165)
              ·
                refine ⟨7755637365435067667515531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41363399282320360893416165 7755637365435067667515531)
                ·
                  refine ⟨11633456048152601501273297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7755637365435067667515531 11633456048152601501273297)
                  ·
                    refine ⟨8725092036114451125954973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11633456048152601501273297 8725092036114451125954973)
                    ·
                      refine ⟨3271909513542919172233115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8725092036114451125954973 3271909513542919172233115)
                      ·
                        rfl

theorem cell23_6372021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_6372021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372021 prefixEnd_6372021 := by exact prefixLift 6372021
  have htrace : WordTrace (prefixWord ++ tailWord_6372021) baseStart_6372021 baseEnd_6372021 := by
    simpa [prefixWord, tailWord_6372021, baseEnd_6372021] using wordTrace_append hprefix tailTrace_6372021
  have hstable : (prefixWord ++ tailWord_6372021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372021).length < 2 ^ (prefixWord ++ tailWord_6372021).sum := by decide
  have hdescent : baseEnd_6372021 < baseStart_6372021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372052 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_6372052 : Nat := 118140960795 + 6372052 * 2 ^ 59
def prefixEnd_6372052 : Nat := 4983230072969 + 3 ^ 40 * 6372052 * 2
def baseEnd_6372052 : Nat := 3271925431443208550945473

theorem tailTrace_6372052 : CollatzResearch.WordTrace tailWord_6372052 prefixEnd_6372052 3271925431443208550945473 := by
  unfold tailWord_6372052
  simp only [CollatzResearch.WordTrace]
  refine ⟨116203914755575669342959205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154938553007434225790612273 116203914755575669342959205)
  ·
    refine ⟨21788234016670438001804851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116203914755575669342959205 21788234016670438001804851)
    ·
      refine ⟨32682351025005657002707277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21788234016670438001804851 32682351025005657002707277)
      ·
        refine ⟨12255881634377121376015229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32682351025005657002707277 12255881634377121376015229)
        ·
          refine ⟨4595955612891420516005711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12255881634377121376015229 4595955612891420516005711)
          ·
            refine ⟨6893933419337130774008567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595955612891420516005711 6893933419337130774008567)
            ·
              refine ⟨10340900129005696161012851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6893933419337130774008567 10340900129005696161012851)
              ·
                refine ⟨15511350193508544241519277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10340900129005696161012851 15511350193508544241519277)
                ·
                  refine ⟨5816756322565704090569729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15511350193508544241519277 5816756322565704090569729)
                  ·
                    refine ⟨4362567241924278067927297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5816756322565704090569729 4362567241924278067927297)
                    ·
                      refine ⟨3271925431443208550945473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362567241924278067927297 3271925431443208550945473)
                      ·
                        rfl

theorem cell23_6372052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_6372052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372052 prefixEnd_6372052 := by exact prefixLift 6372052
  have htrace : WordTrace (prefixWord ++ tailWord_6372052) baseStart_6372052 baseEnd_6372052 := by
    simpa [prefixWord, tailWord_6372052, baseEnd_6372052] using wordTrace_append hprefix tailTrace_6372052
  have hstable : (prefixWord ++ tailWord_6372052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372052).length < 2 ^ (prefixWord ++ tailWord_6372052).sum := by decide
  have hdescent : baseEnd_6372052 < baseStart_6372052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372057 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 2, 3, 4]
def baseStart_6372057 : Nat := 118140960795 + 6372057 * 2 ^ 59
def prefixEnd_6372057 : Nat := 4983230072969 + 3 ^ 40 * 6372057 * 2
def baseEnd_6372057 : Nat := 3271927998846481031382949

theorem tailTrace_6372057 : CollatzResearch.WordTrace tailWord_6372057 prefixEnd_6372057 3271927998846481031382949 := by
  unfold tailWord_6372057
  simp only [CollatzResearch.WordTrace]
  refine ⟨232408011876133224539850425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154938674584088816359900283 232408011876133224539850425)
  ·
    refine ⟨174306008907099918404887819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232408011876133224539850425 174306008907099918404887819)
    ·
      refine ⟨261459013360649877607331729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174306008907099918404887819 261459013360649877607331729)
      ·
        refine ⟨196094260020487408205498797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261459013360649877607331729 196094260020487408205498797)
        ·
          refine ⟨73535347507682778077062049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196094260020487408205498797 73535347507682778077062049)
          ·
            refine ⟨55151510630762083557796537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73535347507682778077062049 55151510630762083557796537)
            ·
              refine ⟨41363632973071562668347403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55151510630762083557796537 41363632973071562668347403)
              ·
                refine ⟨62045449459607344002521105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41363632973071562668347403 62045449459607344002521105)
                ·
                  refine ⟨46534087094705508001890829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62045449459607344002521105 46534087094705508001890829)
                  ·
                    refine ⟨17450282660514565500709061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46534087094705508001890829 17450282660514565500709061)
                    ·
                      refine ⟨3271927998846481031382949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17450282660514565500709061 3271927998846481031382949)
                      ·
                        rfl

theorem cell23_6372057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_6372057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372057 prefixEnd_6372057 := by exact prefixLift 6372057
  have htrace : WordTrace (prefixWord ++ tailWord_6372057) baseStart_6372057 baseEnd_6372057 := by
    simpa [prefixWord, tailWord_6372057, baseEnd_6372057] using wordTrace_append hprefix tailTrace_6372057
  have hstable : (prefixWord ++ tailWord_6372057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372057).length < 2 ^ (prefixWord ++ tailWord_6372057).sum := by decide
  have hdescent : baseEnd_6372057 < baseStart_6372057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372068 : List Nat := [2, 3, 1, 1, 1, 4, 4, 1, 2, 1, 3]
def baseStart_6372068 : Nat := 118140960795 + 6372068 * 2 ^ 59
def prefixEnd_6372068 : Nat := 4983230072969 + 3 ^ 40 * 6372068 * 2
def baseEnd_6372068 : Nat := 3271933647133680488345399

theorem tailTrace_6372068 : CollatzResearch.WordTrace tailWord_6372068 prefixEnd_6372068 3271933647133680488345399 := by
  unfold tailWord_6372068
  simp only [CollatzResearch.WordTrace]
  refine ⟨116204206539546686709250429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154938942052728915612333905 116204206539546686709250429)
  ·
    refine ⟨43576577452330007515968911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116204206539546686709250429 43576577452330007515968911)
    ·
      refine ⟨65364866178495011273953367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43576577452330007515968911 65364866178495011273953367)
      ·
        refine ⟨98047299267742516910930051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65364866178495011273953367 98047299267742516910930051)
        ·
          refine ⟨147070948901613775366395077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98047299267742516910930051 147070948901613775366395077)
          ·
            refine ⟨27575802919052582881199077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147070948901613775366395077 27575802919052582881199077)
            ·
              refine ⟨5170463047322359290224827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27575802919052582881199077 5170463047322359290224827)
              ·
                refine ⟨7755694570983538935337241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170463047322359290224827 7755694570983538935337241)
                ·
                  refine ⟨5816770928237654201502931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7755694570983538935337241 5816770928237654201502931)
                  ·
                    refine ⟨8725156392356481302254397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5816770928237654201502931 8725156392356481302254397)
                    ·
                      refine ⟨3271933647133680488345399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8725156392356481302254397 3271933647133680488345399)
                      ·
                        rfl

theorem cell23_6372068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_6372068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372068 prefixEnd_6372068 := by exact prefixLift 6372068
  have htrace : WordTrace (prefixWord ++ tailWord_6372068) baseStart_6372068 baseEnd_6372068 := by
    simpa [prefixWord, tailWord_6372068, baseEnd_6372068] using wordTrace_append hprefix tailTrace_6372068
  have hstable : (prefixWord ++ tailWord_6372068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372068).length < 2 ^ (prefixWord ++ tailWord_6372068).sum := by decide
  have hdescent : baseEnd_6372068 < baseStart_6372068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372078 : List Nat := [4, 1, 2, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_6372078 : Nat := 118140960795 + 6372078 * 2 ^ 59
def prefixEnd_6372078 : Nat := 4983230072969 + 3 ^ 40 * 6372078 * 2
def baseEnd_6372078 : Nat := 3271938781940225449220353

theorem tailTrace_6372078 : CollatzResearch.WordTrace tailWord_6372078 prefixEnd_6372078 3271938781940225449220353 := by
  unfold tailWord_6372078
  simp only [CollatzResearch.WordTrace]
  refine ⟨29051097226132143140795611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154939185206038096750909925 29051097226132143140795611)
  ·
    refine ⟨43576645839198214711193417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29051097226132143140795611 43576645839198214711193417)
    ·
      refine ⟨32682484379398661033395063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43576645839198214711193417 32682484379398661033395063)
      ·
        refine ⟨49023726569097991550092595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32682484379398661033395063 49023726569097991550092595)
        ·
          refine ⟨73535589853646987325138893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49023726569097991550092595 73535589853646987325138893)
          ·
            refine ⟨27575846195117620246927085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73535589853646987325138893 27575846195117620246927085)
            ·
              refine ⟨10340942323169107592597657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27575846195117620246927085 10340942323169107592597657)
              ·
                refine ⟨7755706742376830694448243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10340942323169107592597657 7755706742376830694448243)
                ·
                  refine ⟨11633560113565246041672365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7755706742376830694448243 11633560113565246041672365)
                  ·
                    refine ⟨4362585042586967265627137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11633560113565246041672365 4362585042586967265627137)
                    ·
                      refine ⟨3271938781940225449220353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362585042586967265627137 3271938781940225449220353)
                      ·
                        rfl

theorem cell23_6372078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_6372078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372078 prefixEnd_6372078 := by exact prefixLift 6372078
  have htrace : WordTrace (prefixWord ++ tailWord_6372078) baseStart_6372078 baseEnd_6372078 := by
    simpa [prefixWord, tailWord_6372078, baseEnd_6372078] using wordTrace_append hprefix tailTrace_6372078
  have hstable : (prefixWord ++ tailWord_6372078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372078).length < 2 ^ (prefixWord ++ tailWord_6372078).sum := by decide
  have hdescent : baseEnd_6372078 < baseStart_6372078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372085 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6372085 : Nat := 118140960795 + 6372085 * 2 ^ 59
def prefixEnd_6372085 : Nat := 4983230072969 + 3 ^ 40 * 6372085 * 2
def baseEnd_6372085 : Nat := 3271942376304806921832821

theorem tailTrace_6372085 : CollatzResearch.WordTrace tailWord_6372085 prefixEnd_6372085 3271942376304806921832821 := by
  unfold tailWord_6372085
  simp only [CollatzResearch.WordTrace]
  refine ⟨232409033120031785321869709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154939355413354523547913139 232409033120031785321869709)
  ·
    refine ⟨87153387420011919495701141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232409033120031785321869709 87153387420011919495701141)
    ·
      refine ⟨4085315035313058726360991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87153387420011919495701141 4085315035313058726360991)
      ·
        refine ⟨6127972552969588089541487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4085315035313058726360991 6127972552969588089541487)
        ·
          refine ⟨9191958829454382134312231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6127972552969588089541487 9191958829454382134312231)
          ·
            refine ⟨13787938244181573201468347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9191958829454382134312231 13787938244181573201468347)
            ·
              refine ⟨20681907366272359802202521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13787938244181573201468347 20681907366272359802202521)
              ·
                refine ⟨15511430524704269851651891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20681907366272359802202521 15511430524704269851651891)
                ·
                  refine ⟨23267145787056404777477837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15511430524704269851651891 23267145787056404777477837)
                  ·
                    refine ⟨8725179670146151791554189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23267145787056404777477837 8725179670146151791554189)
                    ·
                      refine ⟨3271942376304806921832821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8725179670146151791554189 3271942376304806921832821)
                      ·
                        rfl

theorem cell23_6372085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6372085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372085 prefixEnd_6372085 := by exact prefixLift 6372085
  have htrace : WordTrace (prefixWord ++ tailWord_6372085) baseStart_6372085 baseEnd_6372085 := by
    simpa [prefixWord, tailWord_6372085, baseEnd_6372085] using wordTrace_append hprefix tailTrace_6372085
  have hstable : (prefixWord ++ tailWord_6372085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372085).length < 2 ^ (prefixWord ++ tailWord_6372085).sum := by decide
  have hdescent : baseEnd_6372085 < baseStart_6372085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372087 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_6372087 : Nat := 118140960795 + 6372087 * 2 ^ 59
def prefixEnd_6372087 : Nat := 4983230072969 + 3 ^ 40 * 6372087 * 2
def baseEnd_6372087 : Nat := 3271943403266115914007811

theorem tailTrace_6372087 : CollatzResearch.WordTrace tailWord_6372087 prefixEnd_6372087 3271943403266115914007811 := by
  unfold tailWord_6372087
  simp only [CollatzResearch.WordTrace]
  refine ⟨232409106066024539663442515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154939404044016359775628343 232409106066024539663442515)
  ·
    refine ⟨348613659099036809495163773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232409106066024539663442515 348613659099036809495163773)
    ·
      refine ⟨130730122162138803560686415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348613659099036809495163773 130730122162138803560686415)
      ·
        refine ⟨196095183243208205341029623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130730122162138803560686415 196095183243208205341029623)
        ·
          refine ⟨294142774864812308011544435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196095183243208205341029623 294142774864812308011544435)
          ·
            refine ⟨441214162297218462017316653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294142774864812308011544435 441214162297218462017316653)
            ·
              refine ⟨165455310861456923256493745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441214162297218462017316653 165455310861456923256493745)
              ·
                refine ⟨124091483146092692442370309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165455310861456923256493745 124091483146092692442370309)
                ·
                  refine ⟨23267153089892379832944433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124091483146092692442370309 23267153089892379832944433)
                  ·
                    refine ⟨17450364817419284874708325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23267153089892379832944433 17450364817419284874708325)
                    ·
                      refine ⟨3271943403266115914007811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17450364817419284874708325 3271943403266115914007811)
                      ·
                        rfl

theorem cell23_6372087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_6372087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372087 prefixEnd_6372087 := by exact prefixLift 6372087
  have htrace : WordTrace (prefixWord ++ tailWord_6372087) baseStart_6372087 baseEnd_6372087 := by
    simpa [prefixWord, tailWord_6372087, baseEnd_6372087] using wordTrace_append hprefix tailTrace_6372087
  have hstable : (prefixWord ++ tailWord_6372087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372087).length < 2 ^ (prefixWord ++ tailWord_6372087).sum := by decide
  have hdescent : baseEnd_6372087 < baseStart_6372087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372124 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_6372124 : Nat := 118140960795 + 6372124 * 2 ^ 59
def prefixEnd_6372124 : Nat := 4983230072969 + 3 ^ 40 * 6372124 * 2
def baseEnd_6372124 : Nat := 3271962402050332269245141

theorem tailTrace_6372124 : CollatzResearch.WordTrace tailWord_6372124 prefixEnd_6372124 3271962402050332269245141 := by
  unfold tailWord_6372124
  simp only [CollatzResearch.WordTrace]
  refine ⟨116205227783445247491269713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154940303711260329988359617 116205227783445247491269713)
  ·
    refine ⟨87153920837583935618452285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116205227783445247491269713 87153920837583935618452285)
    ·
      refine ⟨32682720314093975856919607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87153920837583935618452285 32682720314093975856919607)
      ·
        refine ⟨49024080471140963785379411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32682720314093975856919607 49024080471140963785379411)
        ·
          refine ⟨73536120706711445678069117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49024080471140963785379411 73536120706711445678069117)
          ·
            refine ⟨27576045265016792129275919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73536120706711445678069117 27576045265016792129275919)
            ·
              refine ⟨41364067897525188193913879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27576045265016792129275919 41364067897525188193913879)
              ·
                refine ⟨62046101846287782290870819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41364067897525188193913879 62046101846287782290870819)
                ·
                  refine ⟨93069152769431673436306229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62046101846287782290870819 93069152769431673436306229)
                  ·
                    refine ⟨8725233072134219384653709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93069152769431673436306229 8725233072134219384653709)
                    ·
                      refine ⟨3271962402050332269245141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8725233072134219384653709 3271962402050332269245141)
                      ·
                        rfl

theorem cell23_6372124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_6372124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372124 prefixEnd_6372124 := by exact prefixLift 6372124
  have htrace : WordTrace (prefixWord ++ tailWord_6372124) baseStart_6372124 baseEnd_6372124 := by
    simpa [prefixWord, tailWord_6372124, baseEnd_6372124] using wordTrace_append hprefix tailTrace_6372124
  have hstable : (prefixWord ++ tailWord_6372124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372124).length < 2 ^ (prefixWord ++ tailWord_6372124).sum := by decide
  have hdescent : baseEnd_6372124 < baseStart_6372124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372125 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_6372125 : Nat := 118140960795 + 6372125 * 2 ^ 59
def prefixEnd_6372125 : Nat := 4983230072969 + 3 ^ 40 * 6372125 * 2
def baseEnd_6372125 : Nat := 3271962915530986765332637

theorem tailTrace_6372125 : CollatzResearch.WordTrace tailWord_6372125 prefixEnd_6372125 3271962915530986765332637 := by
  unfold tailWord_6372125
  simp only [CollatzResearch.WordTrace]
  refine ⟨232410492039886872153325829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154940328026591248102217219 232410492039886872153325829)
  ·
    refine ⟨43576967257478788528748593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232410492039886872153325829 43576967257478788528748593)
    ·
      refine ⟨32682725443109091396561445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43576967257478788528748593 32682725443109091396561445)
      ·
        refine ⟨6128011020582954636855271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32682725443109091396561445 6128011020582954636855271)
        ·
          refine ⟨9192016530874431955282907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6128011020582954636855271 9192016530874431955282907)
          ·
            refine ⟨13788024796311647932924361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9192016530874431955282907 13788024796311647932924361)
            ·
              refine ⟨10341018597233735949693271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13788024796311647932924361 10341018597233735949693271)
              ·
                refine ⟨15511527895850603924539907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10341018597233735949693271 15511527895850603924539907)
                ·
                  refine ⟨23267291843775905886809861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15511527895850603924539907 23267291843775905886809861)
                  ·
                    refine ⟨4362617220707982353776849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23267291843775905886809861 4362617220707982353776849)
                    ·
                      refine ⟨3271962915530986765332637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362617220707982353776849 3271962915530986765332637)
                      ·
                        rfl

theorem cell23_6372125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_6372125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372125 prefixEnd_6372125 := by exact prefixLift 6372125
  have htrace : WordTrace (prefixWord ++ tailWord_6372125) baseStart_6372125 baseEnd_6372125 := by
    simpa [prefixWord, tailWord_6372125, baseEnd_6372125] using wordTrace_append hprefix tailTrace_6372125
  have hstable : (prefixWord ++ tailWord_6372125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372125).length < 2 ^ (prefixWord ++ tailWord_6372125).sum := by decide
  have hdescent : baseEnd_6372125 < baseStart_6372125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372181 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 2, 4, 2]
def baseStart_6372181 : Nat := 118140960795 + 6372181 * 2 ^ 59
def prefixEnd_6372181 : Nat := 4983230072969 + 3 ^ 40 * 6372181 * 2
def baseEnd_6372181 : Nat := 3271991670447638546232379

theorem tailTrace_6372181 : CollatzResearch.WordTrace tailWord_6372181 prefixEnd_6372181 3271991670447638546232379 := by
  unfold tailWord_6372181
  simp only [CollatzResearch.WordTrace]
  refine ⟨232412534527683993717364397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154941689685122662478242931 232412534527683993717364397)
  ·
    refine ⟨87154700447881497644011649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232412534527683993717364397 87154700447881497644011649)
    ·
      refine ⟨65366025335911123233008737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87154700447881497644011649 65366025335911123233008737)
      ·
        refine ⟨49024519001933342424756553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65366025335911123233008737 49024519001933342424756553)
        ·
          refine ⟨36768389251450006818567415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49024519001933342424756553 36768389251450006818567415)
          ·
            refine ⟨55152583877175010227851123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36768389251450006818567415 55152583877175010227851123)
            ·
              refine ⟨82728875815762515341776685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55152583877175010227851123 82728875815762515341776685)
              ·
                refine ⟨31023328430910943253166257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82728875815762515341776685 31023328430910943253166257)
                ·
                  refine ⟨23267496323183207439874693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31023328430910943253166257 23267496323183207439874693)
                  ·
                    refine ⟨4362655560596851394976505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23267496323183207439874693 4362655560596851394976505)
                    ·
                      refine ⟨3271991670447638546232379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362655560596851394976505 3271991670447638546232379)
                      ·
                        rfl

theorem cell23_6372181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_6372181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372181 prefixEnd_6372181 := by exact prefixLift 6372181
  have htrace : WordTrace (prefixWord ++ tailWord_6372181) baseStart_6372181 baseEnd_6372181 := by
    simpa [prefixWord, tailWord_6372181, baseEnd_6372181] using wordTrace_append hprefix tailTrace_6372181
  have hstable : (prefixWord ++ tailWord_6372181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372181).length < 2 ^ (prefixWord ++ tailWord_6372181).sum := by decide
  have hdescent : baseEnd_6372181 < baseStart_6372181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372208 : List Nat := [2, 1, 1, 1, 4, 1, 5, 3, 1, 4]
def baseStart_6372208 : Nat := 118140960795 + 6372208 * 2 ^ 59
def prefixEnd_6372208 : Nat := 4983230072969 + 3 ^ 40 * 6372208 * 2
def baseEnd_6372208 : Nat := 1090668511475103313531585

theorem tailTrace_6372208 : CollatzResearch.WordTrace tailWord_6372208 prefixEnd_6372208 1090668511475103313531585 := by
  unfold tailWord_6372208
  simp only [CollatzResearch.WordTrace]
  refine ⟨116206759649293088664298639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154942346199057451552398185 116206759649293088664298639)
  ·
    refine ⟨174310139473939632996447959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116206759649293088664298639 174310139473939632996447959)
    ·
      refine ⟨261465209210909449494671939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174310139473939632996447959 261465209210909449494671939)
      ·
        refine ⟨392197813816364174242007909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261465209210909449494671939 392197813816364174242007909)
        ·
          refine ⟨73537090090568282670376483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 392197813816364174242007909 73537090090568282670376483)
          ·
            refine ⟨110305635135852424005564725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73537090090568282670376483 110305635135852424005564725)
            ·
              refine ⟨10341153293986164750521693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110305635135852424005564725 10341153293986164750521693)
              ·
                refine ⟨3877932485244811781445635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10341153293986164750521693 3877932485244811781445635)
                ·
                  refine ⟨5816898727867217672168453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877932485244811781445635 5816898727867217672168453)
                  ·
                    refine ⟨1090668511475103313531585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5816898727867217672168453 1090668511475103313531585)
                    ·
                      rfl

theorem cell23_6372208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 1, 4].length) (baseStart_6372208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372208 prefixEnd_6372208 := by exact prefixLift 6372208
  have htrace : WordTrace (prefixWord ++ tailWord_6372208) baseStart_6372208 baseEnd_6372208 := by
    simpa [prefixWord, tailWord_6372208, baseEnd_6372208] using wordTrace_append hprefix tailTrace_6372208
  have hstable : (prefixWord ++ tailWord_6372208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372208).length < 2 ^ (prefixWord ++ tailWord_6372208).sum := by decide
  have hdescent : baseEnd_6372208 < baseStart_6372208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372241 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 6, 3, 2]
def baseStart_6372241 : Nat := 118140960795 + 6372241 * 2 ^ 59
def prefixEnd_6372241 : Nat := 4983230072969 + 3 ^ 40 * 6372241 * 2
def baseEnd_6372241 : Nat := 3272022479286908311482103

theorem tailTrace_6372241 : CollatzResearch.WordTrace tailWord_6372241 prefixEnd_6372241 3272022479286908311482103 := by
  unfold tailWord_6372241
  simp only [CollatzResearch.WordTrace]
  refine ⟨232414722907466623964548577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154943148604977749309699051 232414722907466623964548577)
  ·
    refine ⟨174311042180599967973411433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232414722907466623964548577 174311042180599967973411433)
    ·
      refine ⟨130733281635449975980058575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174311042180599967973411433 130733281635449975980058575)
      ·
        refine ⟨196099922453174963970087863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130733281635449975980058575 196099922453174963970087863)
        ·
          refine ⟨294149883679762445955131795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196099922453174963970087863 294149883679762445955131795)
          ·
            refine ⟨441224825519643668932697693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294149883679762445955131795 441224825519643668932697693)
            ·
              refine ⟨165459309569866375849761635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441224825519643668932697693 165459309569866375849761635)
              ·
                refine ⟨248188964354799563774642453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165459309569866375849761635 248188964354799563774642453)
                ·
                  refine ⟨11633857704131229551936365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 248188964354799563774642453 11633857704131229551936365)
                  ·
                    refine ⟨4362696639049211081976137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11633857704131229551936365 4362696639049211081976137)
                    ·
                      refine ⟨3272022479286908311482103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362696639049211081976137 3272022479286908311482103)
                      ·
                        rfl

theorem cell23_6372241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 3, 2].length) (baseStart_6372241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372241 prefixEnd_6372241 := by exact prefixLift 6372241
  have htrace : WordTrace (prefixWord ++ tailWord_6372241) baseStart_6372241 baseEnd_6372241 := by
    simpa [prefixWord, tailWord_6372241, baseEnd_6372241] using wordTrace_append hprefix tailTrace_6372241
  have hstable : (prefixWord ++ tailWord_6372241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372241).length < 2 ^ (prefixWord ++ tailWord_6372241).sum := by decide
  have hdescent : baseEnd_6372241 < baseStart_6372241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372308 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_6372308 : Nat := 118140960795 + 6372308 * 2 ^ 59
def prefixEnd_6372308 : Nat := 4983230072969 + 3 ^ 40 * 6372308 * 2
def baseEnd_6372308 : Nat := 3272056882490759549344295

theorem tailTrace_6372308 : CollatzResearch.WordTrace tailWord_6372308 prefixEnd_6372308 3272056882490759549344295 := by
  unfold tailWord_6372308
  simp only [CollatzResearch.WordTrace]
  refine ⟨116208583299111947203618789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154944777732149262938158385 116208583299111947203618789)
  ·
    refine ⟨21789109368583490100678523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116208583299111947203618789 21789109368583490100678523)
    ·
      refine ⟨32683664052875235151017785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21789109368583490100678523 32683664052875235151017785)
      ·
        refine ⟨24512748039656426363263339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32683664052875235151017785 24512748039656426363263339)
        ·
          refine ⟨36769122059484639544895009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24512748039656426363263339 36769122059484639544895009)
          ·
            refine ⟨27576841544613479658671257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36769122059484639544895009 27576841544613479658671257)
            ·
              refine ⟨20682631158460109744003443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27576841544613479658671257 20682631158460109744003443)
              ·
                refine ⟨31023946737690164616005165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20682631158460109744003443 31023946737690164616005165)
                ·
                  refine ⟨11633980026633811731001937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31023946737690164616005165 11633980026633811731001937)
                  ·
                    refine ⟨8725485019975358798251453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11633980026633811731001937 8725485019975358798251453)
                    ·
                      refine ⟨3272056882490759549344295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8725485019975358798251453 3272056882490759549344295)
                      ·
                        rfl

theorem cell23_6372308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_6372308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372308 prefixEnd_6372308 := by exact prefixLift 6372308
  have htrace : WordTrace (prefixWord ++ tailWord_6372308) baseStart_6372308 baseEnd_6372308 := by
    simpa [prefixWord, tailWord_6372308, baseEnd_6372308] using wordTrace_append hprefix tailTrace_6372308
  have hstable : (prefixWord ++ tailWord_6372308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372308).length < 2 ^ (prefixWord ++ tailWord_6372308).sum := by decide
  have hdescent : baseEnd_6372308 < baseStart_6372308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372322 : List Nat := [3, 3, 3, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_6372322 : Nat := 118140960795 + 6372322 * 2 ^ 59
def prefixEnd_6372322 : Nat := 4983230072969 + 3 ^ 40 * 6372322 * 2
def baseEnd_6372322 : Nat := 3272064071219922494569231

theorem tailTrace_6372322 : CollatzResearch.WordTrace tailWord_6372322 prefixEnd_6372322 3272064071219922494569231 := by
  unfold tailWord_6372322
  simp only [CollatzResearch.WordTrace]
  refine ⟨58104419305043293699561805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154945118146782116532164813 58104419305043293699561805)
  ·
    refine ⟨21789157239391235137335677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58104419305043293699561805 21789157239391235137335677)
    ·
      refine ⟨8170933964771713176500879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21789157239391235137335677 8170933964771713176500879)
      ·
        refine ⟨12256400947157569764751319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8170933964771713176500879 12256400947157569764751319)
        ·
          refine ⟨18384601420736354647126979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12256400947157569764751319 18384601420736354647126979)
          ·
            refine ⟨27576902131104531970690469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18384601420736354647126979 27576902131104531970690469)
            ·
              refine ⟨5170669149582099744504463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27576902131104531970690469 5170669149582099744504463)
              ·
                refine ⟨7756003724373149616756695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170669149582099744504463 7756003724373149616756695)
                ·
                  refine ⟨11634005586559724425135043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7756003724373149616756695 11634005586559724425135043)
                  ·
                    refine ⟨17451008379839586637702565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11634005586559724425135043 17451008379839586637702565)
                    ·
                      refine ⟨3272064071219922494569231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17451008379839586637702565 3272064071219922494569231)
                      ·
                        rfl

theorem cell23_6372322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_6372322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372322 prefixEnd_6372322 := by exact prefixLift 6372322
  have htrace : WordTrace (prefixWord ++ tailWord_6372322) baseStart_6372322 baseEnd_6372322 := by
    simpa [prefixWord, tailWord_6372322, baseEnd_6372322] using wordTrace_append hprefix tailTrace_6372322
  have hstable : (prefixWord ++ tailWord_6372322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372322).length < 2 ^ (prefixWord ++ tailWord_6372322).sum := by decide
  have hdescent : baseEnd_6372322 < baseStart_6372322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372324 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_6372324 : Nat := 118140960795 + 6372324 * 2 ^ 59
def prefixEnd_6372324 : Nat := 4983230072969 + 3 ^ 40 * 6372324 * 2
def baseEnd_6372324 : Nat := 1090688366060410495581407

theorem tailTrace_6372324 : CollatzResearch.WordTrace tailWord_6372324 prefixEnd_6372324 1090688366060410495581407 := by
  unfold tailWord_6372324
  simp only [CollatzResearch.WordTrace]
  refine ⟨116208875083082964569910013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154945166777443952759880017 116208875083082964569910013)
  ·
    refine ⟨43578328156156111713716255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116208875083082964569910013 43578328156156111713716255)
    ·
      refine ⟨65367492234234167570574383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43578328156156111713716255 65367492234234167570574383)
      ·
        refine ⟨98051238351351251355861575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65367492234234167570574383 98051238351351251355861575)
        ·
          refine ⟨147076857527026877033792363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98051238351351251355861575 147076857527026877033792363)
          ·
            refine ⟨220615286290540315550688545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147076857527026877033792363 220615286290540315550688545)
            ·
              refine ⟨165461464717905236663016409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220615286290540315550688545 165461464717905236663016409)
              ·
                refine ⟨124096098538428927497262307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165461464717905236663016409 124096098538428927497262307)
                ·
                  refine ⟨186144147807643391245893461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124096098538428927497262307 186144147807643391245893461)
                  ·
                    refine ⟨1090688366060410495581407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 186144147807643391245893461 1090688366060410495581407)
                    ·
                      rfl

theorem cell23_6372324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_6372324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372324 prefixEnd_6372324 := by exact prefixLift 6372324
  have htrace : WordTrace (prefixWord ++ tailWord_6372324) baseStart_6372324 baseEnd_6372324 := by
    simpa [prefixWord, tailWord_6372324, baseEnd_6372324] using wordTrace_append hprefix tailTrace_6372324
  have hstable : (prefixWord ++ tailWord_6372324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372324).length < 2 ^ (prefixWord ++ tailWord_6372324).sum := by decide
  have hdescent : baseEnd_6372324 < baseStart_6372324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372378 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2]
def baseStart_6372378 : Nat := 118140960795 + 6372378 * 2 ^ 59
def prefixEnd_6372378 : Nat := 4983230072969 + 3 ^ 40 * 6372378 * 2
def baseEnd_6372378 : Nat := 3272092826136574275468973

theorem tailTrace_6372378 : CollatzResearch.WordTrace tailWord_6372378 prefixEnd_6372378 3272092826136574275468973 := by
  unfold tailWord_6372378
  simp only [CollatzResearch.WordTrace]
  refine ⟨58104929926992574090571447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154946479805313530908190525 58104929926992574090571447)
  ·
    refine ⟨87157394890488861135857171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58104929926992574090571447 87157394890488861135857171)
    ·
      refine ⟨130736092335733291703785757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87157394890488861135857171 130736092335733291703785757)
      ·
        refine ⟨49026034625899984388919659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130736092335733291703785757 49026034625899984388919659)
        ·
          refine ⟨73539051938849976583379489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49026034625899984388919659 73539051938849976583379489)
          ·
            refine ⟨55154288954137482437534617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73539051938849976583379489 55154288954137482437534617)
            ·
              refine ⟨41365716715603111828150963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55154288954137482437534617 41365716715603111828150963)
              ·
                refine ⟨62048575073404667742226445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41365716715603111828150963 62048575073404667742226445)
                ·
                  refine ⟨23268215652526750403334917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62048575073404667742226445 23268215652526750403334917)
                  ·
                    refine ⟨4362790434848765700625297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23268215652526750403334917 4362790434848765700625297)
                    ·
                      refine ⟨3272092826136574275468973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362790434848765700625297 3272092826136574275468973)
                      ·
                        rfl

theorem cell23_6372378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_6372378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372378 prefixEnd_6372378 := by exact prefixLift 6372378
  have htrace : WordTrace (prefixWord ++ tailWord_6372378) baseStart_6372378 baseEnd_6372378 := by
    simpa [prefixWord, tailWord_6372378, baseEnd_6372378] using wordTrace_append hprefix tailTrace_6372378
  have hstable : (prefixWord ++ tailWord_6372378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372378).length < 2 ^ (prefixWord ++ tailWord_6372378).sum := by decide
  have hdescent : baseEnd_6372378 < baseStart_6372378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372395 : List Nat := [1, 1, 1, 1, 2, 1, 6, 4, 2, 2, 2]
def baseStart_6372395 : Nat := 118140960795 + 6372395 * 2 ^ 59
def prefixEnd_6372395 : Nat := 4983230072969 + 3 ^ 40 * 6372395 * 2
def baseEnd_6372395 : Nat := 3272101555307700708956395

theorem tailTrace_6372395 : CollatzResearch.WordTrace tailWord_6372395 prefixEnd_6372395 3272101555307700708956395 := by
  unfold tailWord_6372395
  simp only [CollatzResearch.WordTrace]
  refine ⟨232420339748908708265654639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154946893165939138843769759 232420339748908708265654639)
  ·
    refine ⟨348630509623363062398481959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232420339748908708265654639 348630509623363062398481959)
    ·
      refine ⟨522945764435044593597722939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348630509623363062398481959 522945764435044593597722939)
      ·
        refine ⟨784418646652566890396584409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522945764435044593597722939 784418646652566890396584409)
        ·
          refine ⟨588313984989425167797438307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784418646652566890396584409 588313984989425167797438307)
          ·
            refine ⟨882470977484137751696157461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588313984989425167797438307 882470977484137751696157461)
            ·
              refine ⟨41365827069568957110757381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 882470977484137751696157461 41365827069568957110757381)
              ·
                refine ⟨7756092575544179458267009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41365827069568957110757381 7756092575544179458267009)
                ·
                  refine ⟨5817069431658134593700257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7756092575544179458267009 5817069431658134593700257)
                  ·
                    refine ⟨4362802073743600945275193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5817069431658134593700257 4362802073743600945275193)
                    ·
                      refine ⟨3272101555307700708956395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362802073743600945275193 3272101555307700708956395)
                      ·
                        rfl

theorem cell23_6372395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 2, 2].length) (baseStart_6372395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372395 prefixEnd_6372395 := by exact prefixLift 6372395
  have htrace : WordTrace (prefixWord ++ tailWord_6372395) baseStart_6372395 baseEnd_6372395 := by
    simpa [prefixWord, tailWord_6372395, baseEnd_6372395] using wordTrace_append hprefix tailTrace_6372395
  have hstable : (prefixWord ++ tailWord_6372395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372395).length < 2 ^ (prefixWord ++ tailWord_6372395).sum := by decide
  have hdescent : baseEnd_6372395 < baseStart_6372395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372398 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_6372398 : Nat := 118140960795 + 6372398 * 2 ^ 59
def prefixEnd_6372398 : Nat := 4983230072969 + 3 ^ 40 * 6372398 * 2
def baseEnd_6372398 : Nat := 3272103095749664197218881

theorem tailTrace_6372398 : CollatzResearch.WordTrace tailWord_6372398 prefixEnd_6372398 3272103095749664197218881 := by
  unfold tailWord_6372398
  simp only [CollatzResearch.WordTrace]
  refine ⟨29052556145987229972251731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154946966111931893185342565 29052556145987229972251731)
  ·
    refine ⟨43578834218980844958377597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29052556145987229972251731 43578834218980844958377597)
    ·
      refine ⟨16342062832117816859391599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43578834218980844958377597 16342062832117816859391599)
      ·
        refine ⟨24513094248176725289087399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16342062832117816859391599 24513094248176725289087399)
        ·
          refine ⟨36769641372265087933631099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24513094248176725289087399 36769641372265087933631099)
          ·
            refine ⟨55154462058397631900446649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36769641372265087933631099 55154462058397631900446649)
            ·
              refine ⟨41365846543798223925334987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55154462058397631900446649 41365846543798223925334987)
              ·
                refine ⟨62048769815697335888002481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41365846543798223925334987 62048769815697335888002481)
                ·
                  refine ⟨46536577361773001916001861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62048769815697335888002481 46536577361773001916001861)
                  ·
                    refine ⟨8725608255332437859250349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46536577361773001916001861 8725608255332437859250349)
                    ·
                      refine ⟨3272103095749664197218881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8725608255332437859250349 3272103095749664197218881)
                      ·
                        rfl

theorem cell23_6372398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_6372398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372398 prefixEnd_6372398 := by exact prefixLift 6372398
  have htrace : WordTrace (prefixWord ++ tailWord_6372398) baseStart_6372398 baseEnd_6372398 := by
    simpa [prefixWord, tailWord_6372398, baseEnd_6372398] using wordTrace_append hprefix tailTrace_6372398
  have hstable : (prefixWord ++ tailWord_6372398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372398).length < 2 ^ (prefixWord ++ tailWord_6372398).sum := by decide
  have hdescent : baseEnd_6372398 < baseStart_6372398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372412 : List Nat := [2, 2, 2, 2, 2, 3, 1, 3, 2, 2, 2]
def baseStart_6372412 : Nat := 118140960795 + 6372412 * 2 ^ 59
def prefixEnd_6372412 : Nat := 4983230072969 + 3 ^ 40 * 6372412 * 2
def baseEnd_6372412 : Nat := 3272110284478827142443817

theorem tailTrace_6372412 : CollatzResearch.WordTrace tailWord_6372412 prefixEnd_6372412 3272110284478827142443817 := by
  unfold tailWord_6372412
  simp only [CollatzResearch.WordTrace]
  refine ⟨116210479894923560084511745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154947306526564746779348993 116210479894923560084511745)
  ·
    refine ⟨87157859921192670063383809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116210479894923560084511745 87157859921192670063383809)
    ·
      refine ⟨65368394940894502547537857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87157859921192670063383809 65368394940894502547537857)
      ·
        refine ⟨49026296205670876910653393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65368394940894502547537857 49026296205670876910653393)
        ·
          refine ⟨36769722154253157682990045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49026296205670876910653393 36769722154253157682990045)
          ·
            refine ⟨13788645807844934131121267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36769722154253157682990045 13788645807844934131121267)
            ·
              refine ⟨20682968711767401196681901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13788645807844934131121267 20682968711767401196681901)
              ·
                refine ⟨7756113266912775448755713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20682968711767401196681901 7756113266912775448755713)
                ·
                  refine ⟨5817084950184581586566785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7756113266912775448755713 5817084950184581586566785)
                  ·
                    refine ⟨4362813712638436189925089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5817084950184581586566785 4362813712638436189925089)
                    ·
                      refine ⟨3272110284478827142443817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362813712638436189925089 3272110284478827142443817)
                      ·
                        rfl

theorem cell23_6372412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_6372412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372412 prefixEnd_6372412 := by exact prefixLift 6372412
  have htrace : WordTrace (prefixWord ++ tailWord_6372412) baseStart_6372412 baseEnd_6372412 := by
    simpa [prefixWord, tailWord_6372412, baseEnd_6372412] using wordTrace_append hprefix tailTrace_6372412
  have hstable : (prefixWord ++ tailWord_6372412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372412).length < 2 ^ (prefixWord ++ tailWord_6372412).sum := by decide
  have hdescent : baseEnd_6372412 < baseStart_6372412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372446 : List Nat := [4, 4, 1, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_6372446 : Nat := 118140960795 + 6372446 * 2 ^ 59
def prefixEnd_6372446 : Nat := 4983230072969 + 3 ^ 40 * 6372446 * 2
def baseEnd_6372446 : Nat := 3272127742821080009418661

theorem tailTrace_6372446 : CollatzResearch.WordTrace tailWord_6372446 prefixEnd_6372446 3272127742821080009418661 := by
  unfold tailWord_6372446
  simp only [CollatzResearch.WordTrace]
  refine ⟨29052774983965492996970149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154948133247815962650507461 29052774983965492996970149)
  ·
    refine ⟨5447395309493529936931903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29052774983965492996970149 5447395309493529936931903)
    ·
      refine ⟨8171092964240294905397855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5447395309493529936931903 8171092964240294905397855)
      ·
        refine ⟨12256639446360442358096783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8171092964240294905397855 12256639446360442358096783)
        ·
          refine ⟨18384959169540663537145175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12256639446360442358096783 18384959169540663537145175)
          ·
            refine ⟨27577438754310995305717763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18384959169540663537145175 27577438754310995305717763)
            ·
              refine ⟨41366158131466492958576645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27577438754310995305717763 41366158131466492958576645)
              ·
                refine ⟨7756154649649967429733121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41366158131466492958576645 7756154649649967429733121)
                ·
                  refine ⟨5817115987237475572299841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7756154649649967429733121 5817115987237475572299841)
                  ·
                    refine ⟨4362836990428106679224881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5817115987237475572299841 4362836990428106679224881)
                    ·
                      refine ⟨3272127742821080009418661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362836990428106679224881 3272127742821080009418661)
                      ·
                        rfl

theorem cell23_6372446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_6372446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372446 prefixEnd_6372446 := by exact prefixLift 6372446
  have htrace : WordTrace (prefixWord ++ tailWord_6372446) baseStart_6372446 baseEnd_6372446 := by
    simpa [prefixWord, tailWord_6372446, baseEnd_6372446] using wordTrace_append hprefix tailTrace_6372446
  have hstable : (prefixWord ++ tailWord_6372446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372446).length < 2 ^ (prefixWord ++ tailWord_6372446).sum := by decide
  have hdescent : baseEnd_6372446 < baseStart_6372446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372451 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 4]
def baseStart_6372451 : Nat := 118140960795 + 6372451 * 2 ^ 59
def prefixEnd_6372451 : Nat := 4983230072969 + 3 ^ 40 * 6372451 * 2
def baseEnd_6372451 : Nat := 3272130310224352489856137

theorem tailTrace_6372451 : CollatzResearch.WordTrace tailWord_6372451 prefixEnd_6372451 3272130310224352489856137 := by
  unfold tailWord_6372451
  simp only [CollatzResearch.WordTrace]
  refine ⟨232422382236705829829693207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154948254824470553219795471 232422382236705829829693207)
  ·
    refine ⟨348633573355058744744539811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232422382236705829829693207 348633573355058744744539811)
    ·
      refine ⟨522950360032588117116809717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348633573355058744744539811 522950360032588117116809717)
      ·
        refine ⟨49026596253055135979700911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 522950360032588117116809717 49026596253055135979700911)
        ·
          refine ⟨73539894379582703969551367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49026596253055135979700911 73539894379582703969551367)
          ·
            refine ⟨110309841569374055954327051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73539894379582703969551367 110309841569374055954327051)
            ·
              refine ⟨165464762354061083931490577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110309841569374055954327051 165464762354061083931490577)
              ·
                refine ⟨124098571765545812948617933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165464762354061083931490577 124098571765545812948617933)
                ·
                  refine ⟨46536964412079679855731725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124098571765545812948617933 46536964412079679855731725)
                  ·
                    refine ⟨17451361654529879945899397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46536964412079679855731725 17451361654529879945899397)
                    ·
                      refine ⟨3272130310224352489856137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17451361654529879945899397 3272130310224352489856137)
                      ·
                        rfl

theorem cell23_6372451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_6372451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372451 prefixEnd_6372451 := by exact prefixLift 6372451
  have htrace : WordTrace (prefixWord ++ tailWord_6372451) baseStart_6372451 baseEnd_6372451 := by
    simpa [prefixWord, tailWord_6372451, baseEnd_6372451] using wordTrace_append hprefix tailTrace_6372451
  have hstable : (prefixWord ++ tailWord_6372451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372451).length < 2 ^ (prefixWord ++ tailWord_6372451).sum := by decide
  have hdescent : baseEnd_6372451 < baseStart_6372451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372458 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_6372458 : Nat := 118140960795 + 6372458 * 2 ^ 59
def prefixEnd_6372458 : Nat := 4983230072969 + 3 ^ 40 * 6372458 * 2
def baseEnd_6372458 : Nat := 3272133904588933962468605

theorem tailTrace_6372458 : CollatzResearch.WordTrace tailWord_6372458 prefixEnd_6372458 3272133904588933962468605 := by
  unfold tailWord_6372458
  simp only [CollatzResearch.WordTrace]
  refine ⟨58105659386920117506299507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154948425031786980016798685 58105659386920117506299507)
  ·
    refine ⟨87158489080380176259449261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58105659386920117506299507 87158489080380176259449261)
    ·
      refine ⟨32684433405142566097293473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87158489080380176259449261 32684433405142566097293473)
      ·
        refine ⟨24513325053856924572970105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32684433405142566097293473 24513325053856924572970105)
        ·
          refine ⟨18384993790392693429727579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24513325053856924572970105 18384993790392693429727579)
          ·
            refine ⟨27577490685589040144591369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18384993790392693429727579 27577490685589040144591369)
            ·
              refine ⟨20683118014191780108443527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27577490685589040144591369 20683118014191780108443527)
              ·
                refine ⟨31024677021287670162665291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20683118014191780108443527 31024677021287670162665291)
                ·
                  refine ⟨46537015531931505243997937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31024677021287670162665291 46537015531931505243997937)
                  ·
                    refine ⟨34902761648948628932998453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46537015531931505243997937 34902761648948628932998453)
                    ·
                      refine ⟨3272133904588933962468605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34902761648948628932998453 3272133904588933962468605)
                      ·
                        rfl

theorem cell23_6372458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_6372458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372458 prefixEnd_6372458 := by exact prefixLift 6372458
  have htrace : WordTrace (prefixWord ++ tailWord_6372458) baseStart_6372458 baseEnd_6372458 := by
    simpa [prefixWord, tailWord_6372458, baseEnd_6372458] using wordTrace_append hprefix tailTrace_6372458
  have hstable : (prefixWord ++ tailWord_6372458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372458).length < 2 ^ (prefixWord ++ tailWord_6372458).sum := by decide
  have hdescent : baseEnd_6372458 < baseStart_6372458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372498 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_6372498 : Nat := 118140960795 + 6372498 * 2 ^ 59
def prefixEnd_6372498 : Nat := 4983230072969 + 3 ^ 40 * 6372498 * 2
def baseEnd_6372498 : Nat := 3272154443815113805968421

theorem tailTrace_6372498 : CollatzResearch.WordTrace tailWord_6372498 prefixEnd_6372498 3272154443815113805968421 := by
  unfold tailWord_6372498
  simp only [CollatzResearch.WordTrace]
  refine ⟨58106024116883889214163537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154949397645023704571102765 58106024116883889214163537)
  ·
    refine ⟨43579518087662916910622653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58106024116883889214163537 43579518087662916910622653)
    ·
      refine ⟨16342319282873593841483495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43579518087662916910622653 16342319282873593841483495)
      ·
        refine ⟨24513478924310390762225243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16342319282873593841483495 24513478924310390762225243)
        ·
          refine ⟨36770218386465586143337865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24513478924310390762225243 36770218386465586143337865)
          ·
            refine ⟨27577663789849189607503399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36770218386465586143337865 27577663789849189607503399)
            ·
              refine ⟨41366495684773784411255099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27577663789849189607503399 41366495684773784411255099)
              ·
                refine ⟨62049743527160676616882649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41366495684773784411255099 62049743527160676616882649)
                ·
                  refine ⟨46537307645370507462661987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62049743527160676616882649 46537307645370507462661987)
                  ·
                    refine ⟨69805961468055761193992981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46537307645370507462661987 69805961468055761193992981)
                    ·
                      refine ⟨3272154443815113805968421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69805961468055761193992981 3272154443815113805968421)
                      ·
                        rfl

theorem cell23_6372498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_6372498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372498 prefixEnd_6372498 := by exact prefixLift 6372498
  have htrace : WordTrace (prefixWord ++ tailWord_6372498) baseStart_6372498 baseEnd_6372498 := by
    simpa [prefixWord, tailWord_6372498, baseEnd_6372498] using wordTrace_append hprefix tailTrace_6372498
  have hstable : (prefixWord ++ tailWord_6372498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372498).length < 2 ^ (prefixWord ++ tailWord_6372498).sum := by decide
  have hdescent : baseEnd_6372498 < baseStart_6372498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372508 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 8]
def baseStart_6372508 : Nat := 118140960795 + 6372508 * 2 ^ 59
def prefixEnd_6372508 : Nat := 4983230072969 + 3 ^ 40 * 6372508 * 2
def baseEnd_6372508 : Nat := 363573286513517640760375

theorem tailTrace_6372508 : CollatzResearch.WordTrace tailWord_6372508 prefixEnd_6372508 363573286513517640760375 := by
  unfold tailWord_6372508
  simp only [CollatzResearch.WordTrace]
  refine ⟨116212230598749664282259089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154949640798332885709678785 116212230598749664282259089)
  ·
    refine ⟨87159172949062248211694317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116212230598749664282259089 87159172949062248211694317)
    ·
      refine ⟨32684689855898343079385369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87159172949062248211694317 32684689855898343079385369)
      ·
        refine ⟨24513517391923757309539027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32684689855898343079385369 24513517391923757309539027)
        ·
          refine ⟨36770276087885635964308541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24513517391923757309539027 36770276087885635964308541)
          ·
            refine ⟨13788853532957113486615703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36770276087885635964308541 13788853532957113486615703)
            ·
              refine ⟨20683280299435670229923555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13788853532957113486615703 20683280299435670229923555)
              ·
                refine ⟨31024920449153505344885333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20683280299435670229923555 31024920449153505344885333)
                ·
                  refine ⟨363573286513517640760375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31024920449153505344885333 363573286513517640760375)
                  ·
                    rfl

theorem cell23_6372508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_6372508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372508 prefixEnd_6372508 := by exact prefixLift 6372508
  have htrace : WordTrace (prefixWord ++ tailWord_6372508) baseStart_6372508 baseEnd_6372508 := by
    simpa [prefixWord, tailWord_6372508, baseEnd_6372508] using wordTrace_append hprefix tailTrace_6372508
  have hstable : (prefixWord ++ tailWord_6372508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372508).length < 2 ^ (prefixWord ++ tailWord_6372508).sum := by decide
  have hdescent : baseEnd_6372508 < baseStart_6372508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372531 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 7]
def baseStart_6372531 : Nat := 118140960795 + 6372531 * 2 ^ 59
def prefixEnd_6372531 : Nat := 4983230072969 + 3 ^ 40 * 6372531 * 2
def baseEnd_6372531 : Nat := 3272171388676712176855769

theorem tailTrace_6372531 : CollatzResearch.WordTrace tailWord_6372531 prefixEnd_6372531 3272171388676712176855769 := by
  unfold tailWord_6372531
  simp only [CollatzResearch.WordTrace]
  refine ⟨232425300076416003492605447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154950200050944002328403631 232425300076416003492605447)
  ·
    refine ⟨348637950114624005238908171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232425300076416003492605447 348637950114624005238908171)
    ·
      refine ⟨522956925171936007858362257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348637950114624005238908171 522956925171936007858362257)
      ·
        refine ⟨392217693878952005893771693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522956925171936007858362257 392217693878952005893771693)
        ·
          refine ⟨147081635204607002210164385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392217693878952005893771693 147081635204607002210164385)
          ·
            refine ⟨110311226403455251657623289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147081635204607002210164385 110311226403455251657623289)
            ·
              refine ⟨82733419802591438743217467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110311226403455251657623289 82733419802591438743217467)
              ·
                refine ⟨124100129703887158114826201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82733419802591438743217467 124100129703887158114826201)
                ·
                  refine ⟨93075097277915368586119651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124100129703887158114826201 93075097277915368586119651)
                  ·
                    refine ⟨139612645916873052879179477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93075097277915368586119651 139612645916873052879179477)
                    ·
                      refine ⟨3272171388676712176855769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139612645916873052879179477 3272171388676712176855769)
                      ·
                        rfl

theorem cell23_6372531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_6372531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372531 prefixEnd_6372531 := by exact prefixLift 6372531
  have htrace : WordTrace (prefixWord ++ tailWord_6372531) baseStart_6372531 baseEnd_6372531 := by
    simpa [prefixWord, tailWord_6372531, baseEnd_6372531] using wordTrace_append hprefix tailTrace_6372531
  have hstable : (prefixWord ++ tailWord_6372531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372531).length < 2 ^ (prefixWord ++ tailWord_6372531).sum := by decide
  have hdescent : baseEnd_6372531 < baseStart_6372531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372535 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 3, 1, 3]
def baseStart_6372535 : Nat := 118140960795 + 6372535 * 2 ^ 59
def prefixEnd_6372535 : Nat := 4983230072969 + 3 ^ 40 * 6372535 * 2
def baseEnd_6372535 : Nat := 3272173442599330161205751

theorem tailTrace_6372535 : CollatzResearch.WordTrace tailWord_6372535 prefixEnd_6372535 3272173442599330161205751 := by
  unfold tailWord_6372535
  simp only [CollatzResearch.WordTrace]
  refine ⟨232425445968401512175751059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154950297312267674783834039 232425445968401512175751059)
  ·
    refine ⟨348638168952602268263626589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232425445968401512175751059 348638168952602268263626589)
    ·
      refine ⟨130739313357225850598859971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348638168952602268263626589 130739313357225850598859971)
      ·
        refine ⟨196108970035838775898289957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130739313357225850598859971 196108970035838775898289957)
        ·
          refine ⟨36770431881719770480929367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196108970035838775898289957 36770431881719770480929367)
          ·
            refine ⟨55155647822579655721394051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36770431881719770480929367 55155647822579655721394051)
            ·
              refine ⟨82733471733869483582091077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55155647822579655721394051 82733471733869483582091077)
              ·
                refine ⟨15512525950100528171642077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82733471733869483582091077 15512525950100528171642077)
                ·
                  refine ⟨5817197231287698064365779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15512525950100528171642077 5817197231287698064365779)
                  ·
                    refine ⟨8725795846931547096548669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5817197231287698064365779 8725795846931547096548669)
                    ·
                      refine ⟨3272173442599330161205751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8725795846931547096548669 3272173442599330161205751)
                      ·
                        rfl

theorem cell23_6372535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_6372535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372535 prefixEnd_6372535 := by exact prefixLift 6372535
  have htrace : WordTrace (prefixWord ++ tailWord_6372535) baseStart_6372535 baseEnd_6372535 := by
    simpa [prefixWord, tailWord_6372535, baseEnd_6372535] using wordTrace_append hprefix tailTrace_6372535
  have hstable : (prefixWord ++ tailWord_6372535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372535).length < 2 ^ (prefixWord ++ tailWord_6372535).sum := by decide
  have hdescent : baseEnd_6372535 < baseStart_6372535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372562 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_6372562 : Nat := 118140960795 + 6372562 * 2 ^ 59
def prefixEnd_6372562 : Nat := 4983230072969 + 3 ^ 40 * 6372562 * 2
def baseEnd_6372562 : Nat := 3272187306577001555568127

theorem tailTrace_6372562 : CollatzResearch.WordTrace tailWord_6372562 prefixEnd_6372562 3272187306577001555568127 := by
  unfold tailWord_6372562
  simp only [CollatzResearch.WordTrace]
  refine ⟨58106607684825923946745985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154950953826202463857989293 58106607684825923946745985)
  ·
    refine ⟨43579955763619442960059489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58106607684825923946745985 43579955763619442960059489)
    ·
      refine ⟨32684966822714582220044617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43579955763619442960059489 32684966822714582220044617)
      ·
        refine ⟨24513725117035936665033463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32684966822714582220044617 24513725117035936665033463)
        ·
          refine ⟨36770587675553904997550195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24513725117035936665033463 36770587675553904997550195)
          ·
            refine ⟨55155881513330857496325293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36770587675553904997550195 55155881513330857496325293)
            ·
              refine ⟨20683455567499071561121985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55155881513330857496325293 20683455567499071561121985)
              ·
                refine ⟨15512591675624303670841489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20683455567499071561121985 15512591675624303670841489)
                ·
                  refine ⟨11634443756718227753131117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15512591675624303670841489 11634443756718227753131117)
                  ·
                    refine ⟨4362916408769335407424169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11634443756718227753131117 4362916408769335407424169)
                    ·
                      refine ⟨3272187306577001555568127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362916408769335407424169 3272187306577001555568127)
                      ·
                        rfl

theorem cell23_6372562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_6372562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372562 prefixEnd_6372562 := by exact prefixLift 6372562
  have htrace : WordTrace (prefixWord ++ tailWord_6372562) baseStart_6372562 baseEnd_6372562 := by
    simpa [prefixWord, tailWord_6372562, baseEnd_6372562] using wordTrace_append hprefix tailTrace_6372562
  have hstable : (prefixWord ++ tailWord_6372562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372562).length < 2 ^ (prefixWord ++ tailWord_6372562).sum := by decide
  have hdescent : baseEnd_6372562 < baseStart_6372562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372588 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_6372588 : Nat := 118140960795 + 6372588 * 2 ^ 59
def prefixEnd_6372588 : Nat := 4983230072969 + 3 ^ 40 * 6372588 * 2
def baseEnd_6372588 : Nat := 3272200657074018453843007

theorem tailTrace_6372588 : CollatzResearch.WordTrace tailWord_6372588 prefixEnd_6372588 3272200657074018453843007 := by
  unfold tailWord_6372588
  simp only [CollatzResearch.WordTrace]
  refine ⟨116213689518604751113715209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154951586024806334818286945 116213689518604751113715209)
  ·
    refine ⟨87160267138953563335286407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116213689518604751113715209 87160267138953563335286407)
    ·
      refine ⟨130740400708430345002929611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87160267138953563335286407 130740400708430345002929611)
      ·
        refine ⟨196110601062645517504394417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130740400708430345002929611 196110601062645517504394417)
        ·
          refine ⟨147082950796984138128295813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196110601062645517504394417 147082950796984138128295813)
          ·
            refine ⟨27578053274434525899055465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147082950796984138128295813 27578053274434525899055465)
            ·
              refine ⟨20683539955825894424291599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27578053274434525899055465 20683539955825894424291599)
              ·
                refine ⟨31025309933738841636437399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20683539955825894424291599 31025309933738841636437399)
                ·
                  refine ⟨46537964900608262454656099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31025309933738841636437399 46537964900608262454656099)
                  ·
                    refine ⟨69806947350912393681984149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46537964900608262454656099 69806947350912393681984149)
                    ·
                      refine ⟨3272200657074018453843007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69806947350912393681984149 3272200657074018453843007)
                      ·
                        rfl

theorem cell23_6372588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_6372588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372588 prefixEnd_6372588 := by exact prefixLift 6372588
  have htrace : WordTrace (prefixWord ++ tailWord_6372588) baseStart_6372588 baseEnd_6372588 := by
    simpa [prefixWord, tailWord_6372588, baseEnd_6372588] using wordTrace_append hprefix tailTrace_6372588
  have hstable : (prefixWord ++ tailWord_6372588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372588).length < 2 ^ (prefixWord ++ tailWord_6372588).sum := by decide
  have hdescent : baseEnd_6372588 < baseStart_6372588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372595 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 3]
def baseStart_6372595 : Nat := 118140960795 + 6372595 * 2 ^ 59
def prefixEnd_6372595 : Nat := 4983230072969 + 3 ^ 40 * 6372595 * 2
def baseEnd_6372595 : Nat := 3272204251438599926455475

theorem tailTrace_6372595 : CollatzResearch.WordTrace tailWord_6372595 prefixEnd_6372595 3272204251438599926455475 := by
  unfold tailWord_6372595
  simp only [CollatzResearch.WordTrace]
  refine ⟨232427634348184142422935239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154951756232122761615290159 232427634348184142422935239)
  ·
    refine ⟨348641451522276213634402859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232427634348184142422935239 348641451522276213634402859)
    ·
      refine ⟨522962177283414320451604289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348641451522276213634402859 522962177283414320451604289)
      ·
        refine ⟨392221632962560740338703217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522962177283414320451604289 392221632962560740338703217)
        ·
          refine ⟨294166224721920555254027413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392221632962560740338703217 294166224721920555254027413)
          ·
            refine ⟨13789041783840026027532535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 294166224721920555254027413 13789041783840026027532535)
            ·
              refine ⟨20683562675760039041298803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13789041783840026027532535 20683562675760039041298803)
              ·
                refine ⟨31025344013640058561948205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20683562675760039041298803 31025344013640058561948205)
                ·
                  refine ⟨11634504005115021960730577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31025344013640058561948205 11634504005115021960730577)
                  ·
                    refine ⟨8725878003836266470547933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11634504005115021960730577 8725878003836266470547933)
                    ·
                      refine ⟨3272204251438599926455475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8725878003836266470547933 3272204251438599926455475)
                      ·
                        rfl

theorem cell23_6372595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 3].length) (baseStart_6372595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372595 prefixEnd_6372595 := by exact prefixLift 6372595
  have htrace : WordTrace (prefixWord ++ tailWord_6372595) baseStart_6372595 baseEnd_6372595 := by
    simpa [prefixWord, tailWord_6372595, baseEnd_6372595] using wordTrace_append hprefix tailTrace_6372595
  have hstable : (prefixWord ++ tailWord_6372595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372595).length < 2 ^ (prefixWord ++ tailWord_6372595).sum := by decide
  have hdescent : baseEnd_6372595 < baseStart_6372595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372612 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_6372612 : Nat := 118140960795 + 6372612 * 2 ^ 59
def prefixEnd_6372612 : Nat := 4983230072969 + 3 ^ 40 * 6372612 * 2
def baseEnd_6372612 : Nat := 3272212980609726359942897

theorem tailTrace_6372612 : CollatzResearch.WordTrace tailWord_6372612 prefixEnd_6372612 3272212980609726359942897 := by
  unfold tailWord_6372612
  simp only [CollatzResearch.WordTrace]
  refine ⟨116214127194561277163152045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154952169592748369550869393 116214127194561277163152045)
  ·
    refine ⟨43580297697960478936182017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116214127194561277163152045 43580297697960478936182017)
    ·
      refine ⟨32685223273470359202136513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43580297697960478936182017 32685223273470359202136513)
      ·
        refine ⟨24513917455102769401602385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32685223273470359202136513 24513917455102769401602385)
        ·
          refine ⟨18385438091327077051201789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24513917455102769401602385 18385438091327077051201789)
          ·
            refine ⟨6894539284247653894200671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18385438091327077051201789 6894539284247653894200671)
            ·
              refine ⟨10341808926371480841301007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6894539284247653894200671 10341808926371480841301007)
              ·
                refine ⟨15512713389557221261951511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10341808926371480841301007 15512713389557221261951511)
                ·
                  refine ⟨23269070084335831892927267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15512713389557221261951511 23269070084335831892927267)
                  ·
                    refine ⟨34903605126503747839390901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23269070084335831892927267 34903605126503747839390901)
                    ·
                      refine ⟨3272212980609726359942897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34903605126503747839390901 3272212980609726359942897)
                      ·
                        rfl

theorem cell23_6372612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_6372612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372612 prefixEnd_6372612 := by exact prefixLift 6372612
  have htrace : WordTrace (prefixWord ++ tailWord_6372612) baseStart_6372612 baseEnd_6372612 := by
    simpa [prefixWord, tailWord_6372612, baseEnd_6372612] using wordTrace_append hprefix tailTrace_6372612
  have hstable : (prefixWord ++ tailWord_6372612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372612).length < 2 ^ (prefixWord ++ tailWord_6372612).sum := by decide
  have hdescent : baseEnd_6372612 < baseStart_6372612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372652 : List Nat := [2, 2, 1, 1, 1, 3, 1, 6, 1, 3, 2]
def baseStart_6372652 : Nat := 118140960795 + 6372652 * 2 ^ 59
def prefixEnd_6372652 : Nat := 4983230072969 + 3 ^ 40 * 6372652 * 2
def baseEnd_6372652 : Nat := 3272233519835906203442713

theorem tailTrace_6372652 : CollatzResearch.WordTrace tailWord_6372652 prefixEnd_6372652 3272233519835906203442713 := by
  unfold tailWord_6372652
  simp only [CollatzResearch.WordTrace]
  refine ⟨116214856654488820578880105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154953142205985094105173473 116214856654488820578880105)
  ·
    refine ⟨87161142490866615434160079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116214856654488820578880105 87161142490866615434160079)
    ·
      refine ⟨130741713736299923151240119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87161142490866615434160079 130741713736299923151240119)
      ·
        refine ⟨196112570604449884726860179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130741713736299923151240119 196112570604449884726860179)
        ·
          refine ⟨294168855906674827090290269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196112570604449884726860179 294168855906674827090290269)
          ·
            refine ⟨110313320965003060158858851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294168855906674827090290269 110313320965003060158858851)
            ·
              refine ⟨165469981447504590238288277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110313320965003060158858851 165469981447504590238288277)
              ·
                refine ⟨7756405380351777667419763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165469981447504590238288277 7756405380351777667419763)
                ·
                  refine ⟨11634608070527666501129645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7756405380351777667419763 11634608070527666501129645)
                  ·
                    refine ⟨4362978026447874937923617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11634608070527666501129645 4362978026447874937923617)
                    ·
                      refine ⟨3272233519835906203442713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4362978026447874937923617 3272233519835906203442713)
                      ·
                        rfl

theorem cell23_6372652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 3, 2].length) (baseStart_6372652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372652 prefixEnd_6372652 := by exact prefixLift 6372652
  have htrace : WordTrace (prefixWord ++ tailWord_6372652) baseStart_6372652 baseEnd_6372652 := by
    simpa [prefixWord, tailWord_6372652, baseEnd_6372652] using wordTrace_append hprefix tailTrace_6372652
  have hstable : (prefixWord ++ tailWord_6372652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372652).length < 2 ^ (prefixWord ++ tailWord_6372652).sum := by decide
  have hdescent : baseEnd_6372652 < baseStart_6372652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372676 : List Nat := [2, 3, 4, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_6372676 : Nat := 118140960795 + 6372676 * 2 ^ 59
def prefixEnd_6372676 : Nat := 4983230072969 + 3 ^ 40 * 6372676 * 2
def baseEnd_6372676 : Nat := 3272245843371614109542603

theorem tailTrace_6372676 : CollatzResearch.WordTrace tailWord_6372676 prefixEnd_6372676 3272245843371614109542603 := by
  unfold tailWord_6372676
  simp only [CollatzResearch.WordTrace]
  refine ⟨116215294330445346628316941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154953725773927128837755921 116215294330445346628316941)
  ·
    refine ⟨43580735373917004985618853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116215294330445346628316941 43580735373917004985618853)
    ·
      refine ⟨8171387882609438434803535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43580735373917004985618853 8171387882609438434803535)
      ·
        refine ⟨12257081823914157652205303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8171387882609438434803535 12257081823914157652205303)
        ·
          refine ⟨18385622735871236478307955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12257081823914157652205303 18385622735871236478307955)
          ·
            refine ⟨27578434103806854717461933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18385622735871236478307955 27578434103806854717461933)
            ·
              refine ⟨10341912788927570519048225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27578434103806854717461933 10341912788927570519048225)
              ·
                refine ⟨7756434591695677889286169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10341912788927570519048225 7756434591695677889286169)
                ·
                  refine ⟨5817325943771758416964627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7756434591695677889286169 5817325943771758416964627)
                  ·
                    refine ⟨8725988915657637625446941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5817325943771758416964627 8725988915657637625446941)
                    ·
                      refine ⟨3272245843371614109542603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8725988915657637625446941 3272245843371614109542603)
                      ·
                        rfl

theorem cell23_6372676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_6372676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372676 prefixEnd_6372676 := by exact prefixLift 6372676
  have htrace : WordTrace (prefixWord ++ tailWord_6372676) baseStart_6372676 baseEnd_6372676 := by
    simpa [prefixWord, tailWord_6372676, baseEnd_6372676] using wordTrace_append hprefix tailTrace_6372676
  have hstable : (prefixWord ++ tailWord_6372676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372676).length < 2 ^ (prefixWord ++ tailWord_6372676).sum := by decide
  have hdescent : baseEnd_6372676 < baseStart_6372676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372695 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_6372695 : Nat := 118140960795 + 6372695 * 2 ^ 59
def prefixEnd_6372695 : Nat := 4983230072969 + 3 ^ 40 * 6372695 * 2
def baseEnd_6372695 : Nat := 3272255599504049535205015

theorem tailTrace_6372695 : CollatzResearch.WordTrace tailWord_6372695 prefixEnd_6372695 3272255599504049535205015 := by
  unfold tailWord_6372695
  simp only [CollatzResearch.WordTrace]
  refine ⟨232431281647821859501575539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154954187765214573001050359 232431281647821859501575539)
  ·
    refine ⟨348646922471732789252363309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232431281647821859501575539 348646922471732789252363309)
    ·
      refine ⟨130742595926899795969636241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348646922471732789252363309 130742595926899795969636241)
      ·
        refine ⟨98056946945174846977227181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130742595926899795969636241 98056946945174846977227181)
        ·
          refine ⟨36771355104440567616460193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98056946945174846977227181 36771355104440567616460193)
          ·
            refine ⟨27578516328330425712345145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36771355104440567616460193 27578516328330425712345145)
            ·
              refine ⟨20683887246247819284258859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27578516328330425712345145 20683887246247819284258859)
              ·
                refine ⟨31025830869371728926388289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20683887246247819284258859 31025830869371728926388289)
                ·
                  refine ⟨23269373152028796694791217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31025830869371728926388289 23269373152028796694791217)
                  ·
                    refine ⟨17452029864021597521093413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23269373152028796694791217 17452029864021597521093413)
                    ·
                      refine ⟨3272255599504049535205015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17452029864021597521093413 3272255599504049535205015)
                      ·
                        rfl

theorem cell23_6372695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_6372695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372695 prefixEnd_6372695 := by exact prefixLift 6372695
  have htrace : WordTrace (prefixWord ++ tailWord_6372695) baseStart_6372695 baseEnd_6372695 := by
    simpa [prefixWord, tailWord_6372695, baseEnd_6372695] using wordTrace_append hprefix tailTrace_6372695
  have hstable : (prefixWord ++ tailWord_6372695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372695).length < 2 ^ (prefixWord ++ tailWord_6372695).sum := by decide
  have hdescent : baseEnd_6372695 < baseStart_6372695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372728 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_6372728 : Nat := 118140960795 + 6372728 * 2 ^ 59
def prefixEnd_6372728 : Nat := 4983230072969 + 3 ^ 40 * 6372728 * 2
def baseEnd_6372728 : Nat := 3272272544365647906092363

theorem tailTrace_6372728 : CollatzResearch.WordTrace tailWord_6372728 prefixEnd_6372728 3272272544365647906092363 := by
  unfold tailWord_6372728
  simp only [CollatzResearch.WordTrace]
  refine ⟨116216242628351153068763419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154954990171134870758351225 116216242628351153068763419)
  ·
    refine ⟨174324363942526729603145129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116216242628351153068763419 174324363942526729603145129)
    ·
      refine ⟨130743272956895047202358847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174324363942526729603145129 130743272956895047202358847)
      ·
        refine ⟨196114909435342570803538271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130743272956895047202358847 196114909435342570803538271)
        ·
          refine ⟨294172364153013856205307407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196114909435342570803538271 294172364153013856205307407)
          ·
            refine ⟨441258546229520784307961111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294172364153013856205307407 441258546229520784307961111)
            ·
              refine ⟨661887819344281176461941667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441258546229520784307961111 661887819344281176461941667)
              ·
                refine ⟨992831729016421764692912501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661887819344281176461941667 992831729016421764692912501)
                ·
                  refine ⟨93077974595289540439960547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 992831729016421764692912501 93077974595289540439960547)
                  ·
                    refine ⟨139616961892934310659940821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93077974595289540439960547 139616961892934310659940821)
                    ·
                      refine ⟨3272272544365647906092363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139616961892934310659940821 3272272544365647906092363)
                      ·
                        rfl

theorem cell23_6372728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_6372728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372728 prefixEnd_6372728 := by exact prefixLift 6372728
  have htrace : WordTrace (prefixWord ++ tailWord_6372728) baseStart_6372728 baseEnd_6372728 := by
    simpa [prefixWord, tailWord_6372728, baseEnd_6372728] using wordTrace_append hprefix tailTrace_6372728
  have hstable : (prefixWord ++ tailWord_6372728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372728).length < 2 ^ (prefixWord ++ tailWord_6372728).sum := by decide
  have hdescent : baseEnd_6372728 < baseStart_6372728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372739 : List Nat := [1, 1, 1, 3, 5, 2, 3, 2, 5]
def baseStart_6372739 : Nat := 118140960795 + 6372739 * 2 ^ 59
def prefixEnd_6372739 : Nat := 4983230072969 + 3 ^ 40 * 6372739 * 2
def baseEnd_6372739 : Nat := 363586465850316373672757

theorem tailTrace_6372739 : CollatzResearch.WordTrace tailWord_6372739 prefixEnd_6372739 363586465850316373672757 := by
  unfold tailWord_6372739
  simp only [CollatzResearch.WordTrace]
  refine ⟨232432886459662455016177271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154955257639774970010784847 232432886459662455016177271)
  ·
    refine ⟨348649329689493682524265907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232432886459662455016177271 348649329689493682524265907)
    ·
      refine ⟨522973994534240523786398861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348649329689493682524265907 522973994534240523786398861)
      ·
        refine ⟨196115247950340196419899573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 522973994534240523786398861 196115247950340196419899573)
        ·
          refine ⟨18385804495344393414365585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196115247950340196419899573 18385804495344393414365585)
          ·
            refine ⟨13789353371508295060774189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18385804495344393414365585 13789353371508295060774189)
            ·
              refine ⟨5171007514315610647790321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13789353371508295060774189 5171007514315610647790321)
              ·
                refine ⟨3878255635736707985842741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5171007514315610647790321 3878255635736707985842741)
                ·
                  refine ⟨363586465850316373672757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3878255635736707985842741 363586465850316373672757)
                  ·
                    rfl

theorem cell23_6372739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 5].length) (baseStart_6372739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372739 prefixEnd_6372739 := by exact prefixLift 6372739
  have htrace : WordTrace (prefixWord ++ tailWord_6372739) baseStart_6372739 baseEnd_6372739 := by
    simpa [prefixWord, tailWord_6372739, baseEnd_6372739] using wordTrace_append hprefix tailTrace_6372739
  have hstable : (prefixWord ++ tailWord_6372739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372739).length < 2 ^ (prefixWord ++ tailWord_6372739).sum := by decide
  have hdescent : baseEnd_6372739 < baseStart_6372739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372750 : List Nat := [4, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2]
def baseStart_6372750 : Nat := 118140960795 + 6372750 * 2 ^ 59
def prefixEnd_6372750 : Nat := 4983230072969 + 3 ^ 40 * 6372750 * 2
def baseEnd_6372750 : Nat := 3272283840940046820017263

theorem tailTrace_6372750 : CollatzResearch.WordTrace tailWord_6372750 prefixEnd_6372750 3272283840940046820017263 := by
  unfold tailWord_6372750
  simp only [CollatzResearch.WordTrace]
  refine ⟨29054160957827825486853463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154955525108415069263218469 29054160957827825486853463)
  ·
    refine ⟨43581241436741738230280195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29054160957827825486853463 43581241436741738230280195)
    ·
      refine ⟨65371862155112607345420293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43581241436741738230280195 65371862155112607345420293)
      ·
        refine ⟨12257224154083613877266305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65371862155112607345420293 12257224154083613877266305)
        ·
          refine ⟨9192918115562710407949729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12257224154083613877266305 9192918115562710407949729)
          ·
            refine ⟨6894688586672032805962297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9192918115562710407949729 6894688586672032805962297)
            ·
              refine ⟨5171016440004024604471723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6894688586672032805962297 5171016440004024604471723)
              ·
                refine ⟨7756524660006036906707585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171016440004024604471723 7756524660006036906707585)
                ·
                  refine ⟨5817393495004527680030689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7756524660006036906707585 5817393495004527680030689)
                  ·
                    refine ⟨4363045121253395760023017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5817393495004527680030689 4363045121253395760023017)
                    ·
                      refine ⟨3272283840940046820017263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4363045121253395760023017 3272283840940046820017263)
                      ·
                        rfl

theorem cell23_6372750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_6372750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372750 prefixEnd_6372750 := by exact prefixLift 6372750
  have htrace : WordTrace (prefixWord ++ tailWord_6372750) baseStart_6372750 baseEnd_6372750 := by
    simpa [prefixWord, tailWord_6372750, baseEnd_6372750] using wordTrace_append hprefix tailTrace_6372750
  have hstable : (prefixWord ++ tailWord_6372750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372750).length < 2 ^ (prefixWord ++ tailWord_6372750).sum := by decide
  have hdescent : baseEnd_6372750 < baseStart_6372750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372772 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 4, 4, 2]
def baseStart_6372772 : Nat := 118140960795 + 6372772 * 2 ^ 59
def prefixEnd_6372772 : Nat := 4983230072969 + 3 ^ 40 * 6372772 * 2
def baseEnd_6372772 : Nat := 3272295137514445733942161

theorem tailTrace_6372772 : CollatzResearch.WordTrace tailWord_6372772 prefixEnd_6372772 3272295137514445733942161 := by
  unfold tailWord_6372772
  simp only [CollatzResearch.WordTrace]
  refine ⟨116217045034271450826064285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154956060045695267768085713 116217045034271450826064285)
  ·
    refine ⟨43581391887851794059774107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116217045034271450826064285 43581391887851794059774107)
    ·
      refine ⟨65372087831777691089661161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43581391887851794059774107 65372087831777691089661161)
      ·
        refine ⟨49029065873833268317245871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65372087831777691089661161 49029065873833268317245871)
        ·
          refine ⟨73543598810749902475868807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49029065873833268317245871 73543598810749902475868807)
          ·
            refine ⟨110315398216124853713803211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73543598810749902475868807 110315398216124853713803211)
            ·
              refine ⟨165473097324187280570704817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110315398216124853713803211 165473097324187280570704817)
              ·
                refine ⟨124104822993140460428028613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165473097324187280570704817 124104822993140460428028613)
                ·
                  refine ⟨23269654311213836330255365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124104822993140460428028613 23269654311213836330255365)
                  ·
                    refine ⟨4363060183352594311922881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23269654311213836330255365 4363060183352594311922881)
                    ·
                      refine ⟨3272295137514445733942161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4363060183352594311922881 3272295137514445733942161)
                      ·
                        rfl

theorem cell23_6372772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_6372772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372772 prefixEnd_6372772 := by exact prefixLift 6372772
  have htrace : WordTrace (prefixWord ++ tailWord_6372772) baseStart_6372772 baseEnd_6372772 := by
    simpa [prefixWord, tailWord_6372772, baseEnd_6372772] using wordTrace_append hprefix tailTrace_6372772
  have hstable : (prefixWord ++ tailWord_6372772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372772).length < 2 ^ (prefixWord ++ tailWord_6372772).sum := by decide
  have hdescent : baseEnd_6372772 < baseStart_6372772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372785 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_6372785 : Nat := 118140960795 + 6372785 * 2 ^ 59
def prefixEnd_6372785 : Nat := 4983230072969 + 3 ^ 40 * 6372785 * 2
def baseEnd_6372785 : Nat := 3272301812762954183079601

theorem tailTrace_6372785 : CollatzResearch.WordTrace tailWord_6372785 prefixEnd_6372785 3272301812762954183079601 := by
  unfold tailWord_6372785
  simp only [CollatzResearch.WordTrace]
  refine ⟨232434564217495804872351809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154956376144997203248234539 232434564217495804872351809)
  ·
    refine ⟨174325923163121853654263857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232434564217495804872351809 174325923163121853654263857)
    ·
      refine ⟨130744442372341390240697893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174325923163121853654263857 130744442372341390240697893)
      ·
        refine ⟨24514582944814010670130855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130744442372341390240697893 24514582944814010670130855)
        ·
          refine ⟨36771874417221016005196283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24514582944814010670130855 36771874417221016005196283)
          ·
            refine ⟨55157811625831524007794425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36771874417221016005196283 55157811625831524007794425)
            ·
              refine ⟨41368358719373643005845819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55157811625831524007794425 41368358719373643005845819)
              ·
                refine ⟨62052538079060464508768729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41368358719373643005845819 62052538079060464508768729)
                ·
                  refine ⟨46539403559295348381576547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62052538079060464508768729 46539403559295348381576547)
                  ·
                    refine ⟨69809105338943022572364821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46539403559295348381576547 69809105338943022572364821)
                    ·
                      refine ⟨3272301812762954183079601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69809105338943022572364821 3272301812762954183079601)
                      ·
                        rfl

theorem cell23_6372785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_6372785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372785 prefixEnd_6372785 := by exact prefixLift 6372785
  have htrace : WordTrace (prefixWord ++ tailWord_6372785) baseStart_6372785 baseEnd_6372785 := by
    simpa [prefixWord, tailWord_6372785, baseEnd_6372785] using wordTrace_append hprefix tailTrace_6372785
  have hstable : (prefixWord ++ tailWord_6372785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372785).length < 2 ^ (prefixWord ++ tailWord_6372785).sum := by decide
  have hdescent : baseEnd_6372785 < baseStart_6372785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372792 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 2, 2, 3]
def baseStart_6372792 : Nat := 118140960795 + 6372792 * 2 ^ 59
def prefixEnd_6372792 : Nat := 4983230072969 + 3 ^ 40 * 6372792 * 2
def baseEnd_6372792 : Nat := 3272305407127535655692069

theorem tailTrace_6372792 : CollatzResearch.WordTrace tailWord_6372792 prefixEnd_6372792 3272305407127535655692069 := by
  unfold tailWord_6372792
  simp only [CollatzResearch.WordTrace]
  refine ⟨116217409764235222533928315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154956546352313630045237753 116217409764235222533928315)
  ·
    refine ⟨174326114646352833800892473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116217409764235222533928315 174326114646352833800892473)
    ·
      refine ⟨130744585984764625350669355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174326114646352833800892473 130744585984764625350669355)
      ·
        refine ⟨196116878977146938026004033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130744585984764625350669355 196116878977146938026004033)
        ·
          refine ⟨147087659232860203519503025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196116878977146938026004033 147087659232860203519503025)
          ·
            refine ⟨110315744424645152639627269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147087659232860203519503025 110315744424645152639627269)
            ·
              refine ⟨20684202079620966119930113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110315744424645152639627269 20684202079620966119930113)
              ·
                refine ⟨15513151559715724589947585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20684202079620966119930113 15513151559715724589947585)
                ·
                  refine ⟨11634863669786793442460689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15513151559715724589947585 11634863669786793442460689)
                  ·
                    refine ⟨8726147752340095081845517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11634863669786793442460689 8726147752340095081845517)
                    ·
                      refine ⟨3272305407127535655692069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8726147752340095081845517 3272305407127535655692069)
                      ·
                        rfl

theorem cell23_6372792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_6372792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372792 prefixEnd_6372792 := by exact prefixLift 6372792
  have htrace : WordTrace (prefixWord ++ tailWord_6372792) baseStart_6372792 baseEnd_6372792 := by
    simpa [prefixWord, tailWord_6372792, baseEnd_6372792] using wordTrace_append hprefix tailTrace_6372792
  have hstable : (prefixWord ++ tailWord_6372792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372792).length < 2 ^ (prefixWord ++ tailWord_6372792).sum := by decide
  have hdescent : baseEnd_6372792 < baseStart_6372792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372812 : List Nat := [2, 2, 1, 4, 2, 1, 2, 3, 6]
def baseStart_6372812 : Nat := 118140960795 + 6372812 * 2 ^ 59
def prefixEnd_6372812 : Nat := 4983230072969 + 3 ^ 40 * 6372812 * 2
def baseEnd_6372812 : Nat := 363590630748958397493553

theorem tailTrace_6372812 : CollatzResearch.WordTrace tailWord_6372812 prefixEnd_6372812 363590630748958397493553 := by
  unfold tailWord_6372812
  simp only [CollatzResearch.WordTrace]
  refine ⟨116217774494198994241792345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154957032658931992322389793 116217774494198994241792345)
  ·
    refine ⟨87163330870649245681344259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116217774494198994241792345 87163330870649245681344259)
    ·
      refine ⟨130744996305973868522016389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87163330870649245681344259 130744996305973868522016389)
      ·
        refine ⟨24514686807370100347878073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130744996305973868522016389 24514686807370100347878073)
        ·
          refine ⟨18386015105527575260908555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24514686807370100347878073 18386015105527575260908555)
          ·
            refine ⟨27579022658291362891362833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18386015105527575260908555 27579022658291362891362833)
            ·
              refine ⟨20684266993718522168522125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27579022658291362891362833 20684266993718522168522125)
              ·
                refine ⟨7756600122644445813195797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20684266993718522168522125 7756600122644445813195797)
                ·
                  refine ⟨363590630748958397493553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7756600122644445813195797 363590630748958397493553)
                  ·
                    rfl

theorem cell23_6372812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 6].length) (baseStart_6372812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372812 prefixEnd_6372812 := by exact prefixLift 6372812
  have htrace : WordTrace (prefixWord ++ tailWord_6372812) baseStart_6372812 baseEnd_6372812 := by
    simpa [prefixWord, tailWord_6372812, baseEnd_6372812] using wordTrace_append hprefix tailTrace_6372812
  have hstable : (prefixWord ++ tailWord_6372812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372812).length < 2 ^ (prefixWord ++ tailWord_6372812).sum := by decide
  have hdescent : baseEnd_6372812 < baseStart_6372812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372856 : List Nat := [2, 1, 2, 1, 1, 5, 2, 4, 1, 1, 3]
def baseStart_6372856 : Nat := 118140960795 + 6372856 * 2 ^ 59
def prefixEnd_6372856 : Nat := 4983230072969 + 3 ^ 40 * 6372856 * 2
def baseEnd_6372856 : Nat := 3272338269889423405291775

theorem tailTrace_6372856 : CollatzResearch.WordTrace tailWord_6372856 prefixEnd_6372856 3272338269889423405291775 := by
  unfold tailWord_6372856
  simp only [CollatzResearch.WordTrace]
  refine ⟨116218576900119291999093211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154958102533492389332124281 116218576900119291999093211)
  ·
    refine ⟨174327865350178937998639817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116218576900119291999093211 174327865350178937998639817)
    ·
      refine ⟨130745899012634203498979863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174327865350178937998639817 130745899012634203498979863)
      ·
        refine ⟨196118848518951305248469795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130745899012634203498979863 196118848518951305248469795)
        ·
          refine ⟨294178272778426957872704693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196118848518951305248469795 294178272778426957872704693)
          ·
            refine ⟨27579213072977527300566065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 294178272778426957872704693 27579213072977527300566065)
            ·
              refine ⟨20684409804733145475424549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27579213072977527300566065 20684409804733145475424549)
              ·
                refine ⟨3878326838387464776642103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20684409804733145475424549 3878326838387464776642103)
                ·
                  refine ⟨5817490257581197164963155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3878326838387464776642103 5817490257581197164963155)
                  ·
                    refine ⟨8726235386371795747444733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5817490257581197164963155 8726235386371795747444733)
                    ·
                      refine ⟨3272338269889423405291775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8726235386371795747444733 3272338269889423405291775)
                      ·
                        rfl

theorem cell23_6372856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 1, 1, 3].length) (baseStart_6372856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372856 prefixEnd_6372856 := by exact prefixLift 6372856
  have htrace : WordTrace (prefixWord ++ tailWord_6372856) baseStart_6372856 baseEnd_6372856 := by
    simpa [prefixWord, tailWord_6372856, baseEnd_6372856] using wordTrace_append hprefix tailTrace_6372856
  have hstable : (prefixWord ++ tailWord_6372856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372856).length < 2 ^ (prefixWord ++ tailWord_6372856).sum := by decide
  have hdescent : baseEnd_6372856 < baseStart_6372856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372866 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_6372866 : Nat := 118140960795 + 6372866 * 2 ^ 59
def prefixEnd_6372866 : Nat := 4983230072969 + 3 ^ 40 * 6372866 * 2
def baseEnd_6372866 : Nat := 3272343404695968366166729

theorem tailTrace_6372866 : CollatzResearch.WordTrace tailWord_6372866 prefixEnd_6372866 3272343404695968366166729 := by
  unfold tailWord_6372866
  simp only [CollatzResearch.WordTrace]
  refine ⟨58109379632550588926512613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154958345686801570470700301 58109379632550588926512613)
  ·
    refine ⟨10895508681103235423721115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58109379632550588926512613 10895508681103235423721115)
    ·
      refine ⟨16343263021654853135581673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10895508681103235423721115 16343263021654853135581673)
      ·
        refine ⟨12257447266241139851686255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16343263021654853135581673 12257447266241139851686255)
        ·
          refine ⟨18386170899361709777529383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12257447266241139851686255 18386170899361709777529383)
          ·
            refine ⟨27579256349042564666294075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18386170899361709777529383 27579256349042564666294075)
            ·
              refine ⟨41368884523563846999441113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27579256349042564666294075 41368884523563846999441113)
              ·
                refine ⟨31026663392672885249580835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41368884523563846999441113 31026663392672885249580835)
                ·
                  refine ⟨46539995089009327874371253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31026663392672885249580835 46539995089009327874371253)
                  ·
                    refine ⟨4363124539594624488222305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46539995089009327874371253 4363124539594624488222305)
                    ·
                      refine ⟨3272343404695968366166729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4363124539594624488222305 3272343404695968366166729)
                      ·
                        rfl

theorem cell23_6372866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_6372866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372866 prefixEnd_6372866 := by exact prefixLift 6372866
  have htrace : WordTrace (prefixWord ++ tailWord_6372866) baseStart_6372866 baseEnd_6372866 := by
    simpa [prefixWord, tailWord_6372866, baseEnd_6372866] using wordTrace_append hprefix tailTrace_6372866
  have hstable : (prefixWord ++ tailWord_6372866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372866).length < 2 ^ (prefixWord ++ tailWord_6372866).sum := by decide
  have hdescent : baseEnd_6372866 < baseStart_6372866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372872 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 1, 6]
def baseStart_6372872 : Nat := 118140960795 + 6372872 * 2 ^ 59
def prefixEnd_6372872 : Nat := 4983230072969 + 3 ^ 40 * 6372872 * 2
def baseEnd_6372872 : Nat := 1090782161859965114230567

theorem tailTrace_6372872 : CollatzResearch.WordTrace tailWord_6372872 prefixEnd_6372872 1090782161859965114230567 := by
  unfold tailWord_6372872
  simp only [CollatzResearch.WordTrace]
  refine ⟨116218868684090309365384435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154958491578787079153845913 116218868684090309365384435)
  ·
    refine ⟨174328303026135464048076653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116218868684090309365384435 174328303026135464048076653)
    ·
      refine ⟨65373113634800799018028745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174328303026135464048076653 65373113634800799018028745)
      ·
        refine ⟨49029835226100599263521559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65373113634800799018028745 49029835226100599263521559)
        ·
          refine ⟨73544752839150898895282339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49029835226100599263521559 73544752839150898895282339)
          ·
            refine ⟨110317129258726348342923509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73544752839150898895282339 110317129258726348342923509)
            ·
              refine ⟨10342230868005595157149079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110317129258726348342923509 10342230868005595157149079)
              ·
                refine ⟨15513346302008392735723619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10342230868005595157149079 15513346302008392735723619)
                ·
                  refine ⟨23270019453012589103585429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15513346302008392735723619 23270019453012589103585429)
                  ·
                    refine ⟨1090782161859965114230567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23270019453012589103585429 1090782161859965114230567)
                    ·
                      rfl

theorem cell23_6372872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_6372872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372872 prefixEnd_6372872 := by exact prefixLift 6372872
  have htrace : WordTrace (prefixWord ++ tailWord_6372872) baseStart_6372872 baseEnd_6372872 := by
    simpa [prefixWord, tailWord_6372872, baseEnd_6372872] using wordTrace_append hprefix tailTrace_6372872
  have hstable : (prefixWord ++ tailWord_6372872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372872).length < 2 ^ (prefixWord ++ tailWord_6372872).sum := by decide
  have hdescent : baseEnd_6372872 < baseStart_6372872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372892 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_6372892 : Nat := 118140960795 + 6372892 * 2 ^ 59
def prefixEnd_6372892 : Nat := 4983230072969 + 3 ^ 40 * 6372892 * 2
def baseEnd_6372892 : Nat := 3272356755192985264441609

theorem tailTrace_6372892 : CollatzResearch.WordTrace tailWord_6372892 prefixEnd_6372892 3272356755192985264441609 := by
  unfold tailWord_6372892
  simp only [CollatzResearch.WordTrace]
  refine ⟨116219233414054081073248465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154958977885405441430997953 116219233414054081073248465)
  ·
    refine ⟨87164425060540560804936349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116219233414054081073248465 87164425060540560804936349)
    ·
      refine ⟨32686659397702710301851131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87164425060540560804936349 32686659397702710301851131)
      ·
        refine ⟨49029989096554065452776697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32686659397702710301851131 49029989096554065452776697)
        ·
          refine ⟨36772491822415549089582523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49029989096554065452776697 36772491822415549089582523)
          ·
            refine ⟨55158737733623323634373785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36772491822415549089582523 55158737733623323634373785)
            ·
              refine ⟨41369053300217492725780339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55158737733623323634373785 41369053300217492725780339)
              ·
                refine ⟨62053579950326239088670509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41369053300217492725780339 62053579950326239088670509)
                ·
                  refine ⟨23270092481372339658251441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62053579950326239088670509 23270092481372339658251441)
                  ·
                    refine ⟨17452569361029254743688581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23270092481372339658251441 17452569361029254743688581)
                    ·
                      refine ⟨3272356755192985264441609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17452569361029254743688581 3272356755192985264441609)
                      ·
                        rfl

theorem cell23_6372892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_6372892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372892 prefixEnd_6372892 := by exact prefixLift 6372892
  have htrace : WordTrace (prefixWord ++ tailWord_6372892) baseStart_6372892 baseEnd_6372892 := by
    simpa [prefixWord, tailWord_6372892, baseEnd_6372892] using wordTrace_append hprefix tailTrace_6372892
  have hstable : (prefixWord ++ tailWord_6372892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372892).length < 2 ^ (prefixWord ++ tailWord_6372892).sum := by decide
  have hdescent : baseEnd_6372892 < baseStart_6372892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372899 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 5]
def baseStart_6372899 : Nat := 118140960795 + 6372899 * 2 ^ 59
def prefixEnd_6372899 : Nat := 4983230072969 + 3 ^ 40 * 6372899 * 2
def baseEnd_6372899 : Nat := 3272360349557566737054077

theorem tailTrace_6372899 : CollatzResearch.WordTrace tailWord_6372899 prefixEnd_6372899 3272360349557566737054077 := by
  unfold tailWord_6372899
  simp only [CollatzResearch.WordTrace]
  refine ⟨232438722139082802342001751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154959148092721868228001167 232438722139082802342001751)
  ·
    refine ⟨348658083208624203513002627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232438722139082802342001751 348658083208624203513002627)
    ·
      refine ⟨522987124812936305269503941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348658083208624203513002627 522987124812936305269503941)
      ·
        refine ⟨98060085902425557238031989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 522987124812936305269503941 98060085902425557238031989)
        ·
          refine ⟨9193133053352395991065499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98060085902425557238031989 9193133053352395991065499)
          ·
            refine ⟨13789699580028593986598249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9193133053352395991065499 13789699580028593986598249)
            ·
              refine ⟨10342274685021445489948687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13789699580028593986598249 10342274685021445489948687)
              ·
                refine ⟨15513412027532168234923031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10342274685021445489948687 15513412027532168234923031)
                ·
                  refine ⟨23270118041298252352384547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15513412027532168234923031 23270118041298252352384547)
                  ·
                    refine ⟨34905177061947378528576821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23270118041298252352384547 34905177061947378528576821)
                    ·
                      refine ⟨3272360349557566737054077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34905177061947378528576821 3272360349557566737054077)
                      ·
                        rfl

theorem cell23_6372899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_6372899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372899 prefixEnd_6372899 := by exact prefixLift 6372899
  have htrace : WordTrace (prefixWord ++ tailWord_6372899) baseStart_6372899 baseEnd_6372899 := by
    simpa [prefixWord, tailWord_6372899, baseEnd_6372899] using wordTrace_append hprefix tailTrace_6372899
  have hstable : (prefixWord ++ tailWord_6372899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372899).length < 2 ^ (prefixWord ++ tailWord_6372899).sum := by decide
  have hdescent : baseEnd_6372899 < baseStart_6372899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372929 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_6372929 : Nat := 118140960795 + 6372929 * 2 ^ 59
def prefixEnd_6372929 : Nat := 4983230072969 + 3 ^ 40 * 6372929 * 2
def baseEnd_6372929 : Nat := 3272375753977201619678939

theorem tailTrace_6372929 : CollatzResearch.WordTrace tailWord_6372929 prefixEnd_6372929 3272375753977201619678939 := by
  unfold tailWord_6372929
  simp only [CollatzResearch.WordTrace]
  refine ⟨232439816328974117465593841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154959877552649411643729227 232439816328974117465593841)
  ·
    refine ⟨174329862246730588099195381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232439816328974117465593841 174329862246730588099195381)
    ·
      refine ⟨16343424585630992634299567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174329862246730588099195381 16343424585630992634299567)
      ·
        refine ⟨24515136878446488951449351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16343424585630992634299567 24515136878446488951449351)
        ·
          refine ⟨36772705317669733427174027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24515136878446488951449351 36772705317669733427174027)
          ·
            refine ⟨55159057976504600140761041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36772705317669733427174027 55159057976504600140761041)
            ·
              refine ⟨41369293482378450105570781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55159057976504600140761041 41369293482378450105570781)
              ·
                refine ⟨15513485055891918789589043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41369293482378450105570781 15513485055891918789589043)
                ·
                  refine ⟨23270227583837878184383565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15513485055891918789589043 23270227583837878184383565)
                  ·
                    refine ⟨8726335343939204319143837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23270227583837878184383565 8726335343939204319143837)
                    ·
                      refine ⟨3272375753977201619678939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8726335343939204319143837 3272375753977201619678939)
                      ·
                        rfl

theorem cell23_6372929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_6372929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372929 prefixEnd_6372929 := by exact prefixLift 6372929
  have htrace : WordTrace (prefixWord ++ tailWord_6372929) baseStart_6372929 baseEnd_6372929 := by
    simpa [prefixWord, tailWord_6372929, baseEnd_6372929] using wordTrace_append hprefix tailTrace_6372929
  have hstable : (prefixWord ++ tailWord_6372929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372929).length < 2 ^ (prefixWord ++ tailWord_6372929).sum := by decide
  have hdescent : baseEnd_6372929 < baseStart_6372929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372950 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_6372950 : Nat := 118140960795 + 6372950 * 2 ^ 59
def prefixEnd_6372950 : Nat := 4983230072969 + 3 ^ 40 * 6372950 * 2
def baseEnd_6372950 : Nat := 3272386537070946037516343

theorem tailTrace_6372950 : CollatzResearch.WordTrace tailWord_6372950 prefixEnd_6372950 3272386537070946037516343 := by
  unfold tailWord_6372950
  simp only [CollatzResearch.WordTrace]
  refine ⟨14527536391368627378256769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154960388174598692034738869 14527536391368627378256769)
  ·
    refine ⟨10895652293526470533692577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14527536391368627378256769 10895652293526470533692577)
    ·
      refine ⟨8171739220144852900269433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10895652293526470533692577 8171739220144852900269433)
      ·
        refine ⟨6128804415108639675202075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8171739220144852900269433 6128804415108639675202075)
        ·
          refine ⟨9193206622662959512803113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6128804415108639675202075 9193206622662959512803113)
          ·
            refine ⟨6894904966997219634602335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9193206622662959512803113 6894904966997219634602335)
            ·
              refine ⟨10342357450495829451903503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6894904966997219634602335 10342357450495829451903503)
              ·
                refine ⟨15513536175743744177855255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10342357450495829451903503 15513536175743744177855255)
                ·
                  refine ⟨23270304263615616266782883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15513536175743744177855255 23270304263615616266782883)
                  ·
                    refine ⟨34905456395423424400174325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23270304263615616266782883 34905456395423424400174325)
                    ·
                      refine ⟨3272386537070946037516343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34905456395423424400174325 3272386537070946037516343)
                      ·
                        rfl

theorem cell23_6372950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_6372950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372950 prefixEnd_6372950 := by exact prefixLift 6372950
  have htrace : WordTrace (prefixWord ++ tailWord_6372950) baseStart_6372950 baseEnd_6372950 := by
    simpa [prefixWord, tailWord_6372950, baseEnd_6372950] using wordTrace_append hprefix tailTrace_6372950
  have hstable : (prefixWord ++ tailWord_6372950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372950).length < 2 ^ (prefixWord ++ tailWord_6372950).sum := by decide
  have hdescent : baseEnd_6372950 < baseStart_6372950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6372992 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 7]
def baseStart_6372992 : Nat := 118140960795 + 6372992 * 2 ^ 59
def prefixEnd_6372992 : Nat := 4983230072969 + 3 ^ 40 * 6372992 * 2
def baseEnd_6372992 : Nat := 363600900362048319243461

theorem tailTrace_6372992 : CollatzResearch.WordTrace tailWord_6372992 prefixEnd_6372992 363600900362048319243461 := by
  unfold tailWord_6372992
  simp only [CollatzResearch.WordTrace]
  refine ⟨116221057063872939612568615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154961409418497252816758153 116221057063872939612568615)
  ·
    refine ⟨174331585595809409418852923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116221057063872939612568615 174331585595809409418852923)
    ·
      refine ⟨261497378393714114128279385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174331585595809409418852923 261497378393714114128279385)
      ·
        refine ⟨196123033795285585596209539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261497378393714114128279385 196123033795285585596209539)
        ·
          refine ⟨294184550692928378394314309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196123033795285585596209539 294184550692928378394314309)
          ·
            refine ⟨55159603254924070948933933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294184550692928378394314309 55159603254924070948933933)
            ·
              refine ⟨20684851220596526605850225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55159603254924070948933933 20684851220596526605850225)
              ·
                refine ⟨15513638415447394954387669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20684851220596526605850225 15513638415447394954387669)
                ·
                  refine ⟨363600900362048319243461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15513638415447394954387669 363600900362048319243461)
                  ·
                    rfl

theorem cell23_6372992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 7].length) (baseStart_6372992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6372992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6372992 prefixEnd_6372992 := by exact prefixLift 6372992
  have htrace : WordTrace (prefixWord ++ tailWord_6372992) baseStart_6372992 baseEnd_6372992 := by
    simpa [prefixWord, tailWord_6372992, baseEnd_6372992] using wordTrace_append hprefix tailTrace_6372992
  have hstable : (prefixWord ++ tailWord_6372992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6372992).length < 2 ^ (prefixWord ++ tailWord_6372992).sum := by decide
  have hdescent : baseEnd_6372992 < baseStart_6372992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6372992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373029 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 1, 7, 2]
def baseStart_6373029 : Nat := 118140960795 + 6373029 * 2 ^ 59
def prefixEnd_6373029 : Nat := 4983230072969 + 3 ^ 40 * 6373029 * 2
def baseEnd_6373029 : Nat := 3272427102042651228428479

theorem tailTrace_6373029 : CollatzResearch.WordTrace tailWord_6373029 prefixEnd_6373029 3272427102042651228428479 := by
  unfold tailWord_6373029
  simp only [CollatzResearch.WordTrace]
  refine ⟨232443463628611834544234141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154962309085741223029489427 232443463628611834544234141)
  ·
    refine ⟨87166298860729437954087803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232443463628611834544234141 87166298860729437954087803)
    ·
      refine ⟨130749448291094156931131705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87166298860729437954087803 130749448291094156931131705)
      ·
        refine ⟨98062086218320617698348779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130749448291094156931131705 98062086218320617698348779)
        ·
          refine ⟨147093129327480926547523169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98062086218320617698348779 147093129327480926547523169)
          ·
            refine ⟨110319846995610694910642377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147093129327480926547523169 110319846995610694910642377)
            ·
              refine ⟨82739885246708021182981783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110319846995610694910642377 82739885246708021182981783)
              ·
                refine ⟨124109827870062031774472675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82739885246708021182981783 124109827870062031774472675)
                ·
                  refine ⟨186164741805093047661709013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124109827870062031774472675 186164741805093047661709013)
                  ·
                    refine ⟨4363236136056868304571305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 186164741805093047661709013 4363236136056868304571305)
                    ·
                      refine ⟨3272427102042651228428479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4363236136056868304571305 3272427102042651228428479)
                      ·
                        rfl

theorem cell23_6373029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_6373029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373029 prefixEnd_6373029 := by exact prefixLift 6373029
  have htrace : WordTrace (prefixWord ++ tailWord_6373029) baseStart_6373029 baseEnd_6373029 := by
    simpa [prefixWord, tailWord_6373029, baseEnd_6373029] using wordTrace_append hprefix tailTrace_6373029
  have hstable : (prefixWord ++ tailWord_6373029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373029).length < 2 ^ (prefixWord ++ tailWord_6373029).sum := by decide
  have hdescent : baseEnd_6373029 < baseStart_6373029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373072 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 6]
def baseStart_6373072 : Nat := 118140960795 + 6373072 * 2 ^ 59
def prefixEnd_6373072 : Nat := 4983230072969 + 3 ^ 40 * 6373072 * 2
def baseEnd_6373072 : Nat := 3272449181710794560190781

theorem tailTrace_6373072 : CollatzResearch.WordTrace tailWord_6373072 prefixEnd_6373072 3272449181710794560190781 := by
  unfold tailWord_6373072
  simp only [CollatzResearch.WordTrace]
  refine ⟨116222515983728026444024735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154963354644970701925366313 116222515983728026444024735)
  ·
    refine ⟨174333773975592039666037103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116222515983728026444024735 174333773975592039666037103)
    ·
      refine ⟨261500660963388059499055655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174333773975592039666037103 261500660963388059499055655)
      ·
        refine ⟨392250991445082089248583483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261500660963388059499055655 392250991445082089248583483)
        ·
          refine ⟨588376487167623133872875225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392250991445082089248583483 588376487167623133872875225)
          ·
            refine ⟨441282365375717350404656419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588376487167623133872875225 441282365375717350404656419)
            ·
              refine ⟨661923548063576025606984629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441282365375717350404656419 661923548063576025606984629)
              ·
                refine ⟨62055332630960252400654809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 661923548063576025606984629 62055332630960252400654809)
                ·
                  refine ⟨46541499473220189300491107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62055332630960252400654809 46541499473220189300491107)
                  ·
                    refine ⟨69812249209830283950736661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46541499473220189300491107 69812249209830283950736661)
                    ·
                      refine ⟨3272449181710794560190781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69812249209830283950736661 3272449181710794560190781)
                      ·
                        rfl

theorem cell23_6373072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_6373072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373072 prefixEnd_6373072 := by exact prefixLift 6373072
  have htrace : WordTrace (prefixWord ++ tailWord_6373072) baseStart_6373072 baseEnd_6373072 := by
    simpa [prefixWord, tailWord_6373072, baseEnd_6373072] using wordTrace_append hprefix tailTrace_6373072
  have hstable : (prefixWord ++ tailWord_6373072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373072).length < 2 ^ (prefixWord ++ tailWord_6373072).sum := by decide
  have hdescent : baseEnd_6373072 < baseStart_6373072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373076 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6373076 : Nat := 118140960795 + 6373076 * 2 ^ 59
def prefixEnd_6373076 : Nat := 4983230072969 + 3 ^ 40 * 6373076 * 2
def baseEnd_6373076 : Nat := 3272451235633412544540763

theorem tailTrace_6373076 : CollatzResearch.WordTrace tailWord_6373076 prefixEnd_6373076 3272451235633412544540763 := by
  unfold tailWord_6373076
  simp only [CollatzResearch.WordTrace]
  refine ⟨116222588929720780785597541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154963451906294374380796721 116222588929720780785597541)
  ·
    refine ⟨21791735424322646397299539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116222588929720780785597541 21791735424322646397299539)
    ·
      refine ⟨32687603136483969595949309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21791735424322646397299539 32687603136483969595949309)
      ·
        refine ⟨12257851176181488598480991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32687603136483969595949309 12257851176181488598480991)
        ·
          refine ⟨18386776764272232897721487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12257851176181488598480991 18386776764272232897721487)
          ·
            refine ⟨27580165146408349346582231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18386776764272232897721487 27580165146408349346582231)
            ·
              refine ⟨41370247719612524019873347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27580165146408349346582231 41370247719612524019873347)
              ·
                refine ⟨62055371579418786029810021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41370247719612524019873347 62055371579418786029810021)
                ·
                  refine ⟨11635382171141022380589379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62055371579418786029810021 11635382171141022380589379)
                  ·
                    refine ⟨17453073256711533570884069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11635382171141022380589379 17453073256711533570884069)
                    ·
                      refine ⟨3272451235633412544540763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17453073256711533570884069 3272451235633412544540763)
                      ·
                        rfl

theorem cell23_6373076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6373076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373076 prefixEnd_6373076 := by exact prefixLift 6373076
  have htrace : WordTrace (prefixWord ++ tailWord_6373076) baseStart_6373076 baseEnd_6373076 := by
    simpa [prefixWord, tailWord_6373076, baseEnd_6373076] using wordTrace_append hprefix tailTrace_6373076
  have hstable : (prefixWord ++ tailWord_6373076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373076).length < 2 ^ (prefixWord ++ tailWord_6373076).sum := by decide
  have hdescent : baseEnd_6373076 < baseStart_6373076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373170 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2]
def baseStart_6373170 : Nat := 118140960795 + 6373170 * 2 ^ 59
def prefixEnd_6373170 : Nat := 4983230072969 + 3 ^ 40 * 6373170 * 2
def baseEnd_6373170 : Nat := 3272499502814935176765331

theorem tailTrace_6373170 : CollatzResearch.WordTrace tailWord_6373170 prefixEnd_6373170 3272499502814935176765331 := by
  unfold tailWord_6373170
  simp only [CollatzResearch.WordTrace]
  refine ⟨58112151580275253906279241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154965737547400677083411309 58112151580275253906279241)
  ·
    refine ⟨43584113685206440429709431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58112151580275253906279241 43584113685206440429709431)
    ·
      refine ⟨65376170527809660644564147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43584113685206440429709431 65376170527809660644564147)
      ·
        refine ⟨98064255791714490966846221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65376170527809660644564147 98064255791714490966846221)
        ·
          refine ⟨36774095921892934112567333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98064255791714490966846221 36774095921892934112567333)
          ·
            refine ⟨6895142985354925146106375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36774095921892934112567333 6895142985354925146106375)
            ·
              refine ⟨10342714478032387719159563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6895142985354925146106375 10342714478032387719159563)
              ·
                refine ⟨15514071717048581578739345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10342714478032387719159563 15514071717048581578739345)
                ·
                  refine ⟨11635553787786436184054509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15514071717048581578739345 11635553787786436184054509)
                  ·
                    refine ⟨4363332670419913569020441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11635553787786436184054509 4363332670419913569020441)
                    ·
                      refine ⟨3272499502814935176765331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4363332670419913569020441 3272499502814935176765331)
                      ·
                        rfl

theorem cell23_6373170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_6373170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373170 prefixEnd_6373170 := by exact prefixLift 6373170
  have htrace : WordTrace (prefixWord ++ tailWord_6373170) baseStart_6373170 baseEnd_6373170 := by
    simpa [prefixWord, tailWord_6373170, baseEnd_6373170] using wordTrace_append hprefix tailTrace_6373170
  have hstable : (prefixWord ++ tailWord_6373170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373170).length < 2 ^ (prefixWord ++ tailWord_6373170).sum := by decide
  have hdescent : baseEnd_6373170 < baseStart_6373170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373183 : List Nat := [1, 1, 2, 2, 6, 1, 1, 3, 1, 1, 4]
def baseStart_6373183 : Nat := 118140960795 + 6373183 * 2 ^ 59
def prefixEnd_6373183 : Nat := 4983230072969 + 3 ^ 40 * 6373183 * 2
def baseEnd_6373183 : Nat := 3272506178063443625902771

theorem tailTrace_6373183 : CollatzResearch.WordTrace tailWord_6373183 prefixEnd_6373183 3272506178063443625902771 := by
  unfold tailWord_6373183
  simp only [CollatzResearch.WordTrace]
  refine ⟨232449080470053918845340203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154966053646702612563560135 232449080470053918845340203)
  ·
    refine ⟨348673620705080878268010305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232449080470053918845340203 348673620705080878268010305)
    ·
      refine ⟨261505215528810658701007729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348673620705080878268010305 261505215528810658701007729)
      ·
        refine ⟨196128911646607994025755797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261505215528810658701007729 196128911646607994025755797)
        ·
          refine ⟨9193542733434749719957303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 196128911646607994025755797 9193542733434749719957303)
          ·
            refine ⟨13790314100152124579935955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9193542733434749719957303 13790314100152124579935955)
            ·
              refine ⟨20685471150228186869903933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13790314100152124579935955 20685471150228186869903933)
              ·
                refine ⟨7757051681335570076213975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20685471150228186869903933 7757051681335570076213975)
                ·
                  refine ⟨11635577522003355114320963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7757051681335570076213975 11635577522003355114320963)
                  ·
                    refine ⟨17453366283005032671481445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11635577522003355114320963 17453366283005032671481445)
                    ·
                      refine ⟨3272506178063443625902771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17453366283005032671481445 3272506178063443625902771)
                      ·
                        rfl

theorem cell23_6373183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_6373183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373183 prefixEnd_6373183 := by exact prefixLift 6373183
  have htrace : WordTrace (prefixWord ++ tailWord_6373183) baseStart_6373183 baseEnd_6373183 := by
    simpa [prefixWord, tailWord_6373183, baseEnd_6373183] using wordTrace_append hprefix tailTrace_6373183
  have hstable : (prefixWord ++ tailWord_6373183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373183).length < 2 ^ (prefixWord ++ tailWord_6373183).sum := by decide
  have hdescent : baseEnd_6373183 < baseStart_6373183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373199 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 3]
def baseStart_6373199 : Nat := 118140960795 + 6373199 * 2 ^ 59
def prefixEnd_6373199 : Nat := 4983230072969 + 3 ^ 40 * 6373199 * 2
def baseEnd_6373199 : Nat := 3272514393753915563302697

theorem tailTrace_6373199 : CollatzResearch.WordTrace tailWord_6373199 prefixEnd_6373199 3272514393753915563302697 := by
  unfold tailWord_6373199
  simp only [CollatzResearch.WordTrace]
  refine ⟨232449664037995953577922651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154966442691997302385281767 232449664037995953577922651)
  ·
    refine ⟨348674496056993930366883977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232449664037995953577922651 348674496056993930366883977)
    ·
      refine ⟨261505872042745447775162983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348674496056993930366883977 261505872042745447775162983)
      ·
        refine ⟨392258808064118171662744475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261505872042745447775162983 392258808064118171662744475)
        ·
          refine ⟨588388212096177257494116713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392258808064118171662744475 588388212096177257494116713)
          ·
            refine ⟨441291159072132943120587535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588388212096177257494116713 441291159072132943120587535)
            ·
              refine ⟨661936738608199414680881303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441291159072132943120587535 661936738608199414680881303)
              ·
                refine ⟨992905107912299122021321955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661936738608199414680881303 992905107912299122021321955)
                ·
                  refine ⟨1489357661868448683031982933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992905107912299122021321955 1489357661868448683031982933)
                  ·
                    refine ⟨8726705050010441502140525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1489357661868448683031982933 8726705050010441502140525)
                    ·
                      refine ⟨3272514393753915563302697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8726705050010441502140525 3272514393753915563302697)
                      ·
                        rfl

theorem cell23_6373199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 3].length) (baseStart_6373199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373199 prefixEnd_6373199 := by exact prefixLift 6373199
  have htrace : WordTrace (prefixWord ++ tailWord_6373199) baseStart_6373199 baseEnd_6373199 := by
    simpa [prefixWord, tailWord_6373199, baseEnd_6373199] using wordTrace_append hprefix tailTrace_6373199
  have hstable : (prefixWord ++ tailWord_6373199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373199).length < 2 ^ (prefixWord ++ tailWord_6373199).sum := by decide
  have hdescent : baseEnd_6373199 < baseStart_6373199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373220 : List Nat := [2, 3, 1, 1, 5, 1, 2, 2, 1, 2, 3]
def baseStart_6373220 : Nat := 118140960795 + 6373220 * 2 ^ 59
def prefixEnd_6373220 : Nat := 4983230072969 + 3 ^ 40 * 6373220 * 2
def baseEnd_6373220 : Nat := 3272525176847659981140101

theorem tailTrace_6373220 : CollatzResearch.WordTrace tailWord_6373220 prefixEnd_6373220 3272525176847659981140101 := by
  unfold tailWord_6373220
  simp only [CollatzResearch.WordTrace]
  refine ⟨116225214985459937082218557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154966953313946582776291409 116225214985459937082218557)
  ·
    refine ⟨43584455619547476405831959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116225214985459937082218557 43584455619547476405831959)
    ·
      refine ⟨65376683429321214608747939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43584455619547476405831959 65376683429321214608747939)
      ·
        refine ⟨98065025143981821913121909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65376683429321214608747939 98065025143981821913121909)
        ·
          refine ⟨9193596107248295804355179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98065025143981821913121909 9193596107248295804355179)
          ·
            refine ⟨13790394160872443706532769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9193596107248295804355179 13790394160872443706532769)
            ·
              refine ⟨10342795620654332779899577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13790394160872443706532769 10342795620654332779899577)
              ·
                refine ⟨7757096715490749584924683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10342795620654332779899577 7757096715490749584924683)
                ·
                  refine ⟨11635645073236124377387025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7757096715490749584924683 11635645073236124377387025)
                  ·
                    refine ⟨8726733804927093283040269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11635645073236124377387025 8726733804927093283040269)
                    ·
                      refine ⟨3272525176847659981140101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8726733804927093283040269 3272525176847659981140101)
                      ·
                        rfl

theorem cell23_6373220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_6373220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373220 prefixEnd_6373220 := by exact prefixLift 6373220
  have htrace : WordTrace (prefixWord ++ tailWord_6373220) baseStart_6373220 baseEnd_6373220 := by
    simpa [prefixWord, tailWord_6373220, baseEnd_6373220] using wordTrace_append hprefix tailTrace_6373220
  have hstable : (prefixWord ++ tailWord_6373220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373220).length < 2 ^ (prefixWord ++ tailWord_6373220).sum := by decide
  have hdescent : baseEnd_6373220 < baseStart_6373220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373239 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_6373239 : Nat := 118140960795 + 6373239 * 2 ^ 59
def prefixEnd_6373239 : Nat := 4983230072969 + 3 ^ 40 * 6373239 * 2
def baseEnd_6373239 : Nat := 3272534932980095406802513

theorem tailTrace_6373239 : CollatzResearch.WordTrace tailWord_6373239 prefixEnd_6373239 3272534932980095406802513 := by
  unfold tailWord_6373239
  simp only [CollatzResearch.WordTrace]
  refine ⟨232451122957851040409378771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154967415305234026939585847 232451122957851040409378771)
  ·
    refine ⟨348676684436776560614068157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232451122957851040409378771 348676684436776560614068157)
    ·
      refine ⟨130753756663791210230275559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348676684436776560614068157 130753756663791210230275559)
      ·
        refine ⟨196130634995686815345413339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130753756663791210230275559 196130634995686815345413339)
        ·
          refine ⟨294195952493530223018120009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196130634995686815345413339 294195952493530223018120009)
          ·
            refine ⟨220646964370147667263590007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294195952493530223018120009 220646964370147667263590007)
            ·
              refine ⟨330970446555221500895385011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220646964370147667263590007 330970446555221500895385011)
              ·
                refine ⟨496455669832832251343077517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330970446555221500895385011 496455669832832251343077517)
                ·
                  refine ⟨186170876187312094253654069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496455669832832251343077517 186170876187312094253654069)
                  ·
                    refine ⟨17453519642560508836280069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 186170876187312094253654069 17453519642560508836280069)
                    ·
                      refine ⟨3272534932980095406802513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17453519642560508836280069 3272534932980095406802513)
                      ·
                        rfl

theorem cell23_6373239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_6373239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373239 prefixEnd_6373239 := by exact prefixLift 6373239
  have htrace : WordTrace (prefixWord ++ tailWord_6373239) baseStart_6373239 baseEnd_6373239 := by
    simpa [prefixWord, tailWord_6373239, baseEnd_6373239] using wordTrace_append hprefix tailTrace_6373239
  have hstable : (prefixWord ++ tailWord_6373239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373239).length < 2 ^ (prefixWord ++ tailWord_6373239).sum := by decide
  have hdescent : baseEnd_6373239 < baseStart_6373239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373259 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 5]
def baseStart_6373259 : Nat := 118140960795 + 6373259 * 2 ^ 59
def prefixEnd_6373259 : Nat := 4983230072969 + 3 ^ 40 * 6373259 * 2
def baseEnd_6373259 : Nat := 3272545202593185328552421

theorem tailTrace_6373259 : CollatzResearch.WordTrace tailWord_6373259 prefixEnd_6373259 3272545202593185328552421 := by
  unfold tailWord_6373259
  simp only [CollatzResearch.WordTrace]
  refine ⟨232451852417778583825106831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154967901611852389216737887 232451852417778583825106831)
  ·
    refine ⟨348677778626667875737660247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232451852417778583825106831 348677778626667875737660247)
    ·
      refine ⟨523016667940001813606490371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348677778626667875737660247 523016667940001813606490371)
      ·
        refine ⟨784525001910002720409735557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523016667940001813606490371 784525001910002720409735557)
        ·
          refine ⟨147098437858125510076825417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 784525001910002720409735557 147098437858125510076825417)
          ·
            refine ⟨110323828393594132557619063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147098437858125510076825417 110323828393594132557619063)
            ·
              refine ⟨165485742590391198836428595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110323828393594132557619063 165485742590391198836428595)
              ·
                refine ⟨248228613885586798254642893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165485742590391198836428595 248228613885586798254642893)
                ·
                  refine ⟨93085730207095049345491085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248228613885586798254642893 93085730207095049345491085)
                  ·
                    refine ⟨34907148827660643504559157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93085730207095049345491085 34907148827660643504559157)
                    ·
                      refine ⟨3272545202593185328552421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34907148827660643504559157 3272545202593185328552421)
                      ·
                        rfl

theorem cell23_6373259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 5].length) (baseStart_6373259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373259 prefixEnd_6373259 := by exact prefixLift 6373259
  have htrace : WordTrace (prefixWord ++ tailWord_6373259) baseStart_6373259 baseEnd_6373259 := by
    simpa [prefixWord, tailWord_6373259, baseEnd_6373259] using wordTrace_append hprefix tailTrace_6373259
  have hstable : (prefixWord ++ tailWord_6373259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373259).length < 2 ^ (prefixWord ++ tailWord_6373259).sum := by decide
  have hdescent : baseEnd_6373259 < baseStart_6373259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373277 : List Nat := [1, 4, 2, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_6373277 : Nat := 118140960795 + 6373277 * 2 ^ 59
def prefixEnd_6373277 : Nat := 4983230072969 + 3 ^ 40 * 6373277 * 2
def baseEnd_6373277 : Nat := 3272554445244966258127339

theorem tailTrace_6373277 : CollatzResearch.WordTrace tailWord_6373277 prefixEnd_6373277 3272554445244966258127339 := by
  unfold tailWord_6373277
  simp only [CollatzResearch.WordTrace]
  refine ⟨232452508931713372899262085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154968339287808915266174723 232452508931713372899262085)
  ·
    refine ⟨43584845424696257418611641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232452508931713372899262085 43584845424696257418611641)
    ·
      refine ⟨32688634068522193063958731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43584845424696257418611641 32688634068522193063958731)
      ·
        refine ⟨49032951102783289595938097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32688634068522193063958731 49032951102783289595938097)
        ·
          refine ⟨36774713327087467196953573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49032951102783289595938097 36774713327087467196953573)
          ·
            refine ⟨6895258748828900099428795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36774713327087467196953573 6895258748828900099428795)
            ·
              refine ⟨10342888123243350149143193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6895258748828900099428795 10342888123243350149143193)
              ·
                refine ⟨7757166092432512611857395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10342888123243350149143193 7757166092432512611857395)
                ·
                  refine ⟨11635749138648768917786093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7757166092432512611857395 11635749138648768917786093)
                  ·
                    refine ⟨4363405926993288344169785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11635749138648768917786093 4363405926993288344169785)
                    ·
                      refine ⟨3272554445244966258127339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4363405926993288344169785 3272554445244966258127339)
                      ·
                        rfl

theorem cell23_6373277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_6373277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373277 prefixEnd_6373277 := by exact prefixLift 6373277
  have htrace : WordTrace (prefixWord ++ tailWord_6373277) baseStart_6373277 baseEnd_6373277 := by
    simpa [prefixWord, tailWord_6373277, baseEnd_6373277] using wordTrace_append hprefix tailTrace_6373277
  have hstable : (prefixWord ++ tailWord_6373277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373277).length < 2 ^ (prefixWord ++ tailWord_6373277).sum := by decide
  have hdescent : baseEnd_6373277 < baseStart_6373277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373289 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 7]
def baseStart_6373289 : Nat := 118140960795 + 6373289 * 2 ^ 59
def prefixEnd_6373289 : Nat := 4983230072969 + 3 ^ 40 * 6373289 * 2
def baseEnd_6373289 : Nat := 3272560607012820211177283

theorem tailTrace_6373289 : CollatzResearch.WordTrace tailWord_6373289 prefixEnd_6373289 3272560607012820211177283 := by
  unfold tailWord_6373289
  simp only [CollatzResearch.WordTrace]
  refine ⟨232452946607669898948698921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154968631071779932632465947 232452946607669898948698921)
  ·
    refine ⟨174339709955752424211524191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232452946607669898948698921 174339709955752424211524191)
    ·
      refine ⟨261509564933628636317286287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174339709955752424211524191 261509564933628636317286287)
      ·
        refine ⟨392264347400442954475929431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261509564933628636317286287 392264347400442954475929431)
        ·
          refine ⟨588396521100664431713894147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392264347400442954475929431 588396521100664431713894147)
          ·
            refine ⟨882594781650996647570841221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588396521100664431713894147 882594781650996647570841221)
            ·
              refine ⟨165486521559561871419532729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 882594781650996647570841221 165486521559561871419532729)
              ·
                refine ⟨124114891169671403564649547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165486521559561871419532729 124114891169671403564649547)
                ·
                  refine ⟨186172336754507105346974321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124114891169671403564649547 186172336754507105346974321)
                  ·
                    refine ⟨139629252565880329010230741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 186172336754507105346974321 139629252565880329010230741)
                    ·
                      refine ⟨3272560607012820211177283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139629252565880329010230741 3272560607012820211177283)
                      ·
                        rfl

theorem cell23_6373289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_6373289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373289 prefixEnd_6373289 := by exact prefixLift 6373289
  have htrace : WordTrace (prefixWord ++ tailWord_6373289) baseStart_6373289 baseEnd_6373289 := by
    simpa [prefixWord, tailWord_6373289, baseEnd_6373289] using wordTrace_append hprefix tailTrace_6373289
  have hstable : (prefixWord ++ tailWord_6373289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373289).length < 2 ^ (prefixWord ++ tailWord_6373289).sum := by decide
  have hdescent : baseEnd_6373289 < baseStart_6373289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373326 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_6373326 : Nat := 118140960795 + 6373326 * 2 ^ 59
def prefixEnd_6373326 : Nat := 4983230072969 + 3 ^ 40 * 6373326 * 2
def baseEnd_6373326 : Nat := 1090859868599012188804871

theorem tailTrace_6373326 : CollatzResearch.WordTrace tailWord_6373326 prefixEnd_6373326 1090859868599012188804871 := by
  unfold tailWord_6373326
  simp only [CollatzResearch.WordTrace]
  refine ⟨29056787013566981783474479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154969530739023902845197221 29056787013566981783474479)
  ·
    refine ⟨43585180520350472675211719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29056787013566981783474479 43585180520350472675211719)
    ·
      refine ⟨65377770780525709012817579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43585180520350472675211719 65377770780525709012817579)
      ·
        refine ⟨98066656170788563519226369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65377770780525709012817579 98066656170788563519226369)
        ·
          refine ⟨73549992128091422639419777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98066656170788563519226369 73549992128091422639419777)
          ·
            refine ⟨55162494096068566979564833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73549992128091422639419777 55162494096068566979564833)
            ·
              refine ⟨41371870572051425234673625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55162494096068566979564833 41371870572051425234673625)
              ·
                refine ⟨31028902929038568926005219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41371870572051425234673625 31028902929038568926005219)
                ·
                  refine ⟨46543354393557853389007829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31028902929038568926005219 46543354393557853389007829)
                  ·
                    refine ⟨1090859868599012188804871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46543354393557853389007829 1090859868599012188804871)
                    ·
                      rfl

theorem cell23_6373326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_6373326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373326 prefixEnd_6373326 := by exact prefixLift 6373326
  have htrace : WordTrace (prefixWord ++ tailWord_6373326) baseStart_6373326 baseEnd_6373326 := by
    simpa [prefixWord, tailWord_6373326, baseEnd_6373326] using wordTrace_append hprefix tailTrace_6373326
  have hstable : (prefixWord ++ tailWord_6373326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373326).length < 2 ^ (prefixWord ++ tailWord_6373326).sum := by decide
  have hdescent : baseEnd_6373326 < baseStart_6373326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373343 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 2, 5]
def baseStart_6373343 : Nat := 118140960795 + 6373343 * 2 ^ 59
def prefixEnd_6373343 : Nat := 4983230072969 + 3 ^ 40 * 6373343 * 2
def baseEnd_6373343 : Nat := 1090862778322720999967345

theorem tailTrace_6373343 : CollatzResearch.WordTrace tailWord_6373343 prefixEnd_6373343 1090862778322720999967345 := by
  unfold tailWord_6373343
  simp only [CollatzResearch.WordTrace]
  refine ⟨232454916149474266171164683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154969944099649510780776455 232454916149474266171164683)
  ·
    refine ⟨348682374224211399256747025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232454916149474266171164683 348682374224211399256747025)
    ·
      refine ⟨261511780668158549442560269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348682374224211399256747025 261511780668158549442560269)
      ·
        refine ⟨98066917750559456040960101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261511780668158549442560269 98066917750559456040960101)
        ·
          refine ⟨18387547078229898007680019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98066917750559456040960101 18387547078229898007680019)
          ·
            refine ⟨27581320617344847011520029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18387547078229898007680019 27581320617344847011520029)
            ·
              refine ⟨10342995231504317629320011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27581320617344847011520029 10342995231504317629320011)
              ·
                refine ⟨15514492847256476443980017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10342995231504317629320011 15514492847256476443980017)
                ·
                  refine ⟨11635869635442357332985013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15514492847256476443980017 11635869635442357332985013)
                  ·
                    refine ⟨1090862778322720999967345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11635869635442357332985013 1090862778322720999967345)
                    ·
                      rfl

theorem cell23_6373343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 5].length) (baseStart_6373343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373343 prefixEnd_6373343 := by exact prefixLift 6373343
  have htrace : WordTrace (prefixWord ++ tailWord_6373343) baseStart_6373343 baseEnd_6373343 := by
    simpa [prefixWord, tailWord_6373343, baseEnd_6373343] using wordTrace_append hprefix tailTrace_6373343
  have hstable : (prefixWord ++ tailWord_6373343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373343).length < 2 ^ (prefixWord ++ tailWord_6373343).sum := by decide
  have hdescent : baseEnd_6373343 < baseStart_6373343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373373 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_6373373 : Nat := 118140960795 + 6373373 * 2 ^ 59
def prefixEnd_6373373 : Nat := 4983230072969 + 3 ^ 40 * 6373373 * 2
def baseEnd_6373373 : Nat := 1090867913129265960842299

theorem tailTrace_6373373 : CollatzResearch.WordTrace tailWord_6373373 prefixEnd_6373373 1090867913129265960842299 := by
  unfold tailWord_6373373
  simp only [CollatzResearch.WordTrace]
  refine ⟨232456010339365581294756773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154970673559577054196504515 232456010339365581294756773)
  ·
    refine ⟨43585501938631046492766895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232456010339365581294756773 43585501938631046492766895)
    ·
      refine ⟨65378252907946569739150343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43585501938631046492766895 65378252907946569739150343)
      ·
        refine ⟨98067379361919854608725515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65378252907946569739150343 98067379361919854608725515)
        ·
          refine ⟨147101069042879781913088273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98067379361919854608725515 147101069042879781913088273)
          ·
            refine ⟨110325801782159836434816205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147101069042879781913088273 110325801782159836434816205)
            ·
              refine ⟨41372175668309938663056077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110325801782159836434816205 41372175668309938663056077)
              ·
                refine ⟨15514565875616226998646029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41372175668309938663056077 15514565875616226998646029)
                ·
                  refine ⟨5817962203356085124492261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15514565875616226998646029 5817962203356085124492261)
                  ·
                    refine ⟨1090867913129265960842299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5817962203356085124492261 1090867913129265960842299)
                    ·
                      rfl

theorem cell23_6373373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_6373373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373373 prefixEnd_6373373 := by exact prefixLift 6373373
  have htrace : WordTrace (prefixWord ++ tailWord_6373373) baseStart_6373373 baseEnd_6373373 := by
    simpa [prefixWord, tailWord_6373373, baseEnd_6373373] using wordTrace_append hprefix tailTrace_6373373
  have hstable : (prefixWord ++ tailWord_6373373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373373).length < 2 ^ (prefixWord ++ tailWord_6373373).sum := by decide
  have hdescent : baseEnd_6373373 < baseStart_6373373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373383 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_6373383 : Nat := 118140960795 + 6373383 * 2 ^ 59
def prefixEnd_6373383 : Nat := 4983230072969 + 3 ^ 40 * 6373383 * 2
def baseEnd_6373383 : Nat := 3272608874194342843401851

theorem tailTrace_6373383 : CollatzResearch.WordTrace tailWord_6373383 prefixEnd_6373383 3272608874194342843401851 := by
  unfold tailWord_6373383
  simp only [CollatzResearch.WordTrace]
  refine ⟨232456375069329353002620803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154970916712886235335080535 232456375069329353002620803)
  ·
    refine ⟨348684562603994029503931205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232456375069329353002620803 348684562603994029503931205)
    ·
      refine ⟨65378355488248880531987101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348684562603994029503931205 65378355488248880531987101)
      ·
        refine ⟨24516883308093330199495163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65378355488248880531987101 24516883308093330199495163)
        ·
          refine ⟨36775324962139995299242745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24516883308093330199495163 36775324962139995299242745)
          ·
            refine ⟨27581493721604996474432059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36775324962139995299242745 27581493721604996474432059)
            ·
              refine ⟨41372240582407494711648089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27581493721604996474432059 41372240582407494711648089)
              ·
                refine ⟨31029180436805621033736067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41372240582407494711648089 31029180436805621033736067)
                ·
                  refine ⟨46543770655208431550604101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31029180436805621033736067 46543770655208431550604101)
                  ·
                    refine ⟨8726956997851580915738269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46543770655208431550604101 8726956997851580915738269)
                    ·
                      refine ⟨3272608874194342843401851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8726956997851580915738269 3272608874194342843401851)
                      ·
                        rfl

theorem cell23_6373383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_6373383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373383 prefixEnd_6373383 := by exact prefixLift 6373383
  have htrace : WordTrace (prefixWord ++ tailWord_6373383) baseStart_6373383 baseEnd_6373383 := by
    simpa [prefixWord, tailWord_6373383, baseEnd_6373383] using wordTrace_append hprefix tailTrace_6373383
  have hstable : (prefixWord ++ tailWord_6373383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373383).length < 2 ^ (prefixWord ++ tailWord_6373383).sum := by decide
  have hdescent : baseEnd_6373383 < baseStart_6373383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373423 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 3, 5, 2]
def baseStart_6373423 : Nat := 118140960795 + 6373423 * 2 ^ 59
def prefixEnd_6373423 : Nat := 4983230072969 + 3 ^ 40 * 6373423 * 2
def baseEnd_6373423 : Nat := 3272629413420522686901667

theorem tailTrace_6373423 : CollatzResearch.WordTrace tailWord_6373423 prefixEnd_6373423 3272629413420522686901667 := by
  unfold tailWord_6373423
  simp only [CollatzResearch.WordTrace]
  refine ⟨232457833989184439834076923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154971889326122959889384615 232457833989184439834076923)
  ·
    refine ⟨348686750983776659751115385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232457833989184439834076923 348686750983776659751115385)
    ·
      refine ⟨261515063237832494813336539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348686750983776659751115385 261515063237832494813336539)
      ·
        refine ⟨392272594856748742220004809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261515063237832494813336539 392272594856748742220004809)
        ·
          refine ⟨294204446142561556665003607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392272594856748742220004809 294204446142561556665003607)
          ·
            refine ⟨441306669213842334997505411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294204446142561556665003607 441306669213842334997505411)
            ·
              refine ⟨661960003820763502496258117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441306669213842334997505411 661960003820763502496258117)
              ·
                refine ⟨124117500716393156718048397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 661960003820763502496258117 124117500716393156718048397)
                ·
                  refine ⟨46544062768647433769268149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124117500716393156718048397 46544062768647433769268149)
                  ·
                    refine ⟨4363505884560696915868889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46544062768647433769268149 4363505884560696915868889)
                    ·
                      refine ⟨3272629413420522686901667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4363505884560696915868889 3272629413420522686901667)
                      ·
                        rfl

theorem cell23_6373423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 5, 2].length) (baseStart_6373423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373423 prefixEnd_6373423 := by exact prefixLift 6373423
  have htrace : WordTrace (prefixWord ++ tailWord_6373423) baseStart_6373423 baseEnd_6373423 := by
    simpa [prefixWord, tailWord_6373423, baseEnd_6373423] using wordTrace_append hprefix tailTrace_6373423
  have hstable : (prefixWord ++ tailWord_6373423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373423).length < 2 ^ (prefixWord ++ tailWord_6373423).sum := by decide
  have hdescent : baseEnd_6373423 < baseStart_6373423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373456 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 5]
def baseStart_6373456 : Nat := 118140960795 + 6373456 * 2 ^ 59
def prefixEnd_6373456 : Nat := 4983230072969 + 3 ^ 40 * 6373456 * 2
def baseEnd_6373456 : Nat := 3272646358282121057789015

theorem tailTrace_6373456 : CollatzResearch.WordTrace tailWord_6373456 prefixEnd_6373456 3272646358282121057789015 := by
  unfold tailWord_6373456
  simp only [CollatzResearch.WordTrace]
  refine ⟨116229518799032443235014111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154972691732043257646685481 116229518799032443235014111)
  ·
    refine ⟨174344278198548664852521167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116229518799032443235014111 174344278198548664852521167)
    ·
      refine ⟨261516417297822997278781751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174344278198548664852521167 261516417297822997278781751)
      ·
        refine ⟨392274625946734495918172627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261516417297822997278781751 392274625946734495918172627)
        ·
          refine ⟨588411938920101743877258941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392274625946734495918172627 588411938920101743877258941)
          ·
            refine ⟨220654477095038153953972103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 588411938920101743877258941 220654477095038153953972103)
            ·
              refine ⟨330981715642557230930958155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220654477095038153953972103 330981715642557230930958155)
              ·
                refine ⟨496472573463835846396437233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330981715642557230930958155 496472573463835846396437233)
                ·
                  refine ⟨372354430097876884797327925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496472573463835846396437233 372354430097876884797327925)
                  ·
                    refine ⟨34908227821675957949749493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 372354430097876884797327925 34908227821675957949749493)
                    ·
                      refine ⟨3272646358282121057789015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34908227821675957949749493 3272646358282121057789015)
                      ·
                        rfl

theorem cell23_6373456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_6373456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373456 prefixEnd_6373456 := by exact prefixLift 6373456
  have htrace : WordTrace (prefixWord ++ tailWord_6373456) baseStart_6373456 baseEnd_6373456 := by
    simpa [prefixWord, tailWord_6373456, baseEnd_6373456] using wordTrace_append hprefix tailTrace_6373456
  have hstable : (prefixWord ++ tailWord_6373456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373456).length < 2 ^ (prefixWord ++ tailWord_6373456).sum := by decide
  have hdescent : baseEnd_6373456 < baseStart_6373456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373463 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 6, 4]
def baseStart_6373463 : Nat := 118140960795 + 6373463 * 2 ^ 59
def prefixEnd_6373463 : Nat := 4983230072969 + 3 ^ 40 * 6373463 * 2
def baseEnd_6373463 : Nat := 1090883317548900843467161

theorem tailTrace_6373463 : CollatzResearch.WordTrace tailWord_6373463 prefixEnd_6373463 1090883317548900843467161 := by
  unfold tailWord_6373463
  simp only [CollatzResearch.WordTrace]
  refine ⟨232459292909039526665533043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154972861939359684443688695 232459292909039526665533043)
  ·
    refine ⟨348688939363559289998299565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232459292909039526665533043 348688939363559289998299565)
    ·
      refine ⟨130758352261334733749362337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348688939363559289998299565 130758352261334733749362337)
      ·
        refine ⟨98068764196001050312021753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130758352261334733749362337 98068764196001050312021753)
        ·
          refine ⟨73551573147000787734016315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98068764196001050312021753 73551573147000787734016315)
          ·
            refine ⟨110327359720501181601024473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73551573147000787734016315 110327359720501181601024473)
            ·
              refine ⟨82745519790375886200768355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110327359720501181601024473 82745519790375886200768355)
              ·
                refine ⟨124118279685563829301152533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82745519790375886200768355 124118279685563829301152533)
                ·
                  refine ⟨5818044360260804498491525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124118279685563829301152533 5818044360260804498491525)
                  ·
                    refine ⟨1090883317548900843467161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5818044360260804498491525 1090883317548900843467161)
                    ·
                      rfl

theorem cell23_6373463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_6373463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373463 prefixEnd_6373463 := by exact prefixLift 6373463
  have htrace : WordTrace (prefixWord ++ tailWord_6373463) baseStart_6373463 baseEnd_6373463 := by
    simpa [prefixWord, tailWord_6373463, baseEnd_6373463] using wordTrace_append hprefix tailTrace_6373463
  have hstable : (prefixWord ++ tailWord_6373463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373463).length < 2 ^ (prefixWord ++ tailWord_6373463).sum := by decide
  have hdescent : baseEnd_6373463 < baseStart_6373463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373490 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_6373490 : Nat := 118140960795 + 6373490 * 2 ^ 59
def prefixEnd_6373490 : Nat := 4983230072969 + 3 ^ 40 * 6373490 * 2
def baseEnd_6373490 : Nat := 3272663816624373924763859

theorem tailTrace_6373490 : CollatzResearch.WordTrace tailWord_6373490 prefixEnd_6373490 3272663816624373924763859 := by
  unfold tailWord_6373490
  simp only [CollatzResearch.WordTrace]
  refine ⟨58115069419985427569191481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154973518453294473517843949 58115069419985427569191481)
  ·
    refine ⟨43586302064989070676893611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58115069419985427569191481 43586302064989070676893611)
    ·
      refine ⟨65379453097483606015340417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43586302064989070676893611 65379453097483606015340417)
      ·
        refine ⟨49034589823112704511505313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65379453097483606015340417 49034589823112704511505313)
        ·
          refine ⟨36775942367334528383628985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49034589823112704511505313 36775942367334528383628985)
          ·
            refine ⟨27581956775500896287721739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36775942367334528383628985 27581956775500896287721739)
            ·
              refine ⟨41372935163251344431582609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27581956775500896287721739 41372935163251344431582609)
              ·
                refine ⟨31029701372438508323686957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41372935163251344431582609 31029701372438508323686957)
                ·
                  refine ⟨11636138014664440621382609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31029701372438508323686957 11636138014664440621382609)
                  ·
                    refine ⟨8727103510998330466036957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11636138014664440621382609 8727103510998330466036957)
                    ·
                      refine ⟨3272663816624373924763859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8727103510998330466036957 3272663816624373924763859)
                      ·
                        rfl

theorem cell23_6373490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_6373490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373490 prefixEnd_6373490 := by exact prefixLift 6373490
  have htrace : WordTrace (prefixWord ++ tailWord_6373490) baseStart_6373490 baseEnd_6373490 := by
    simpa [prefixWord, tailWord_6373490, baseEnd_6373490] using wordTrace_append hprefix tailTrace_6373490
  have hstable : (prefixWord ++ tailWord_6373490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373490).length < 2 ^ (prefixWord ++ tailWord_6373490).sum := by decide
  have hdescent : baseEnd_6373490 < baseStart_6373490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373500 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_6373500 : Nat := 118140960795 + 6373500 * 2 ^ 59
def prefixEnd_6373500 : Nat := 4983230072969 + 3 ^ 40 * 6373500 * 2
def baseEnd_6373500 : Nat := 3272668951430918885638813

theorem tailTrace_6373500 : CollatzResearch.WordTrace tailWord_6373500 prefixEnd_6373500 3272668951430918885638813 := by
  unfold tailWord_6373500
  simp only [CollatzResearch.WordTrace]
  refine ⟨116230321204952740992314977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154973761606603654656419969 116230321204952740992314977)
  ·
    refine ⟨87172740903714555744236233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116230321204952740992314977 87172740903714555744236233)
    ·
      refine ⟨65379555677785916808177175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87172740903714555744236233 65379555677785916808177175)
      ·
        refine ⟨98069333516678875212265763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65379555677785916808177175 98069333516678875212265763)
        ·
          refine ⟨147104000275018312818398645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98069333516678875212265763 147104000275018312818398645)
          ·
            refine ⟨13791000025782966826724873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147104000275018312818398645 13791000025782966826724873)
            ·
              refine ⟨10343250019337225120043655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13791000025782966826724873 10343250019337225120043655)
              ·
                refine ⟨15514875029005837680065483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10343250019337225120043655 15514875029005837680065483)
                ·
                  refine ⟨23272312543508756520098225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15514875029005837680065483 23272312543508756520098225)
                  ·
                    refine ⟨17454234407631567390073669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23272312543508756520098225 17454234407631567390073669)
                    ·
                      refine ⟨3272668951430918885638813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17454234407631567390073669 3272668951430918885638813)
                      ·
                        rfl

theorem cell23_6373500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_6373500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373500 prefixEnd_6373500 := by exact prefixLift 6373500
  have htrace : WordTrace (prefixWord ++ tailWord_6373500) baseStart_6373500 baseEnd_6373500 := by
    simpa [prefixWord, tailWord_6373500, baseEnd_6373500] using wordTrace_append hprefix tailTrace_6373500
  have hstable : (prefixWord ++ tailWord_6373500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373500).length < 2 ^ (prefixWord ++ tailWord_6373500).sum := by decide
  have hdescent : baseEnd_6373500 < baseStart_6373500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373520 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 4, 1, 3]
def baseStart_6373520 : Nat := 118140960795 + 6373520 * 2 ^ 59
def prefixEnd_6373520 : Nat := 4983230072969 + 3 ^ 40 * 6373520 * 2
def baseEnd_6373520 : Nat := 3272679221044008807388721

theorem tailTrace_6373520 : CollatzResearch.WordTrace tailWord_6373520 prefixEnd_6373520 3272679221044008807388721 := by
  unfold tailWord_6373520
  simp only [CollatzResearch.WordTrace]
  refine ⟨116230685934916512700179007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154974247913222016933572009 116230685934916512700179007)
  ·
    refine ⟨174346028902374769050268511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116230685934916512700179007 174346028902374769050268511)
    ·
      refine ⟨261519043353562153575402767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174346028902374769050268511 261519043353562153575402767)
      ·
        refine ⟨392278565030343230363104151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261519043353562153575402767 392278565030343230363104151)
        ·
          refine ⟨588417847545514845544656227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392278565030343230363104151 588417847545514845544656227)
          ·
            refine ⟨882626771318272268316984341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588417847545514845544656227 882626771318272268316984341)
            ·
              refine ⟨41373129905544012577358641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 882626771318272268316984341 41373129905544012577358641)
              ·
                refine ⟨31029847429158009433018981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41373129905544012577358641 31029847429158009433018981)
                ·
                  refine ⟨5818096392967126768691059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31029847429158009433018981 5818096392967126768691059)
                  ·
                    refine ⟨8727144589450690153036589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5818096392967126768691059 8727144589450690153036589)
                    ·
                      refine ⟨3272679221044008807388721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8727144589450690153036589 3272679221044008807388721)
                      ·
                        rfl

theorem cell23_6373520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 4, 1, 3].length) (baseStart_6373520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373520 prefixEnd_6373520 := by exact prefixLift 6373520
  have htrace : WordTrace (prefixWord ++ tailWord_6373520) baseStart_6373520 baseEnd_6373520 := by
    simpa [prefixWord, tailWord_6373520, baseEnd_6373520] using wordTrace_append hprefix tailTrace_6373520
  have hstable : (prefixWord ++ tailWord_6373520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373520).length < 2 ^ (prefixWord ++ tailWord_6373520).sum := by decide
  have hdescent : baseEnd_6373520 < baseStart_6373520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373537 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 4, 1, 3]
def baseStart_6373537 : Nat := 118140960795 + 6373537 * 2 ^ 59
def prefixEnd_6373537 : Nat := 4983230072969 + 3 ^ 40 * 6373537 * 2
def baseEnd_6373537 : Nat := 3272687950215135240876143

theorem tailTrace_6373537 : CollatzResearch.WordTrace tailWord_6373537 prefixEnd_6373537 3272687950215135240876143 := by
  unfold tailWord_6373537
  simp only [CollatzResearch.WordTrace]
  refine ⟨232461991910771437303726865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154974661273847624869151243 232461991910771437303726865)
  ·
    refine ⟨174346493933078577977795149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232461991910771437303726865 174346493933078577977795149)
    ·
      refine ⟨65379935224904466741673181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174346493933078577977795149 65379935224904466741673181)
      ·
        refine ⟨24517475709339175028127443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65379935224904466741673181 24517475709339175028127443)
        ·
          refine ⟨36776213564008762542191165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24517475709339175028127443 36776213564008762542191165)
          ·
            refine ⟨13791080086503285953321687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36776213564008762542191165 13791080086503285953321687)
            ·
              refine ⟨20686620129754928929982531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13791080086503285953321687 20686620129754928929982531)
              ·
                refine ⟨31029930194632393394973797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20686620129754928929982531 31029930194632393394973797)
                ·
                  refine ⟨5818111911493573761557587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31029930194632393394973797 5818111911493573761557587)
                  ·
                    refine ⟨8727167867240360642336381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5818111911493573761557587 8727167867240360642336381)
                    ·
                      refine ⟨3272687950215135240876143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8727167867240360642336381 3272687950215135240876143)
                      ·
                        rfl

theorem cell23_6373537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_6373537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373537 prefixEnd_6373537 := by exact prefixLift 6373537
  have htrace : WordTrace (prefixWord ++ tailWord_6373537) baseStart_6373537 baseEnd_6373537 := by
    simpa [prefixWord, tailWord_6373537, baseEnd_6373537] using wordTrace_append hprefix tailTrace_6373537
  have hstable : (prefixWord ++ tailWord_6373537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373537).length < 2 ^ (prefixWord ++ tailWord_6373537).sum := by decide
  have hdescent : baseEnd_6373537 < baseStart_6373537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373554 : List Nat := [3, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3]
def baseStart_6373554 : Nat := 118140960795 + 6373554 * 2 ^ 59
def prefixEnd_6373554 : Nat := 4983230072969 + 3 ^ 40 * 6373554 * 2
def baseEnd_6373554 : Nat := 3272696679386261674363565

theorem tailTrace_6373554 : CollatzResearch.WordTrace tailWord_6373554 prefixEnd_6373554 3272696679386261674363565 := by
  unfold tailWord_6373554
  simp only [CollatzResearch.WordTrace]
  refine ⟨58115652987927462301773929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154975074634473232804730477 58115652987927462301773929)
  ·
    refine ⟨43586739740945596726330447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58115652987927462301773929 43586739740945596726330447)
    ·
      refine ⟨65380109611418395089495671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43586739740945596726330447 65380109611418395089495671)
      ·
        refine ⟨98070164417127592634243507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65380109611418395089495671 98070164417127592634243507)
        ·
          refine ⟨147105246625691388951365261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98070164417127592634243507 147105246625691388951365261)
          ·
            refine ⟨55164467484634270856761973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147105246625691388951365261 55164467484634270856761973)
            ·
              refine ⟨5171668826684462892821435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55164467484634270856761973 5171668826684462892821435)
              ·
                refine ⟨7757503240026694339232153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171668826684462892821435 7757503240026694339232153)
                ·
                  refine ⟨5818127430020020754424115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7757503240026694339232153 5818127430020020754424115)
                  ·
                    refine ⟨8727191145030031131636173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5818127430020020754424115 8727191145030031131636173)
                    ·
                      refine ⟨3272696679386261674363565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8727191145030031131636173 3272696679386261674363565)
                      ·
                        rfl

theorem cell23_6373554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_6373554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373554 prefixEnd_6373554 := by exact prefixLift 6373554
  have htrace : WordTrace (prefixWord ++ tailWord_6373554) baseStart_6373554 baseEnd_6373554 := by
    simpa [prefixWord, tailWord_6373554, baseEnd_6373554] using wordTrace_append hprefix tailTrace_6373554
  have hstable : (prefixWord ++ tailWord_6373554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373554).length < 2 ^ (prefixWord ++ tailWord_6373554).sum := by decide
  have hdescent : baseEnd_6373554 < baseStart_6373554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373563 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 5]
def baseStart_6373563 : Nat := 118140960795 + 6373563 * 2 ^ 59
def prefixEnd_6373563 : Nat := 4983230072969 + 3 ^ 40 * 6373563 * 2
def baseEnd_6373563 : Nat := 3272701300712152139151023

theorem tailTrace_6373563 : CollatzResearch.WordTrace tailWord_6373563 prefixEnd_6373563 3272701300712152139151023 := by
  unfold tailWord_6373563
  simp only [CollatzResearch.WordTrace]
  refine ⟨232462940208677243744173343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154975293472451495829448895 232462940208677243744173343)
  ·
    refine ⟨348694410313015865616260015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232462940208677243744173343 348694410313015865616260015)
    ·
      refine ⟨523041615469523798424390023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348694410313015865616260015 523041615469523798424390023)
      ·
        refine ⟨784562423204285697636585035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523041615469523798424390023 784562423204285697636585035)
        ·
          refine ⟨1176843634806428546454877553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784562423204285697636585035 1176843634806428546454877553)
          ·
            refine ⟨882632726104821409841158165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1176843634806428546454877553 882632726104821409841158165)
            ·
              refine ⟨41373409036163503586304289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 882632726104821409841158165 41373409036163503586304289)
              ·
                refine ⟨31030056777122627689728217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41373409036163503586304289 31030056777122627689728217)
                ·
                  refine ⟨23272542582841970767296163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31030056777122627689728217 23272542582841970767296163)
                  ·
                    refine ⟨34908813874262956150944245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23272542582841970767296163 34908813874262956150944245)
                    ·
                      refine ⟨3272701300712152139151023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34908813874262956150944245 3272701300712152139151023)
                      ·
                        rfl

theorem cell23_6373563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 5].length) (baseStart_6373563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373563 prefixEnd_6373563 := by exact prefixLift 6373563
  have htrace : WordTrace (prefixWord ++ tailWord_6373563) baseStart_6373563 baseEnd_6373563 := by
    simpa [prefixWord, tailWord_6373563, baseEnd_6373563] using wordTrace_append hprefix tailTrace_6373563
  have hstable : (prefixWord ++ tailWord_6373563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373563).length < 2 ^ (prefixWord ++ tailWord_6373563).sum := by decide
  have hdescent : baseEnd_6373563 < baseStart_6373563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373573 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_6373573 : Nat := 118140960795 + 6373573 * 2 ^ 59
def prefixEnd_6373573 : Nat := 4983230072969 + 3 ^ 40 * 6373573 * 2
def baseEnd_6373573 : Nat := 3272706435518697100025977

theorem tailTrace_6373573 : CollatzResearch.WordTrace tailWord_6373573 prefixEnd_6373573 3272706435518697100025977 := by
  unfold tailWord_6373573
  simp only [CollatzResearch.WordTrace]
  refine ⟨232463304938641015452037373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154975536625760676968024915 232463304938641015452037373)
  ·
    refine ⟨87173739351990380794514015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232463304938641015452037373 87173739351990380794514015)
    ·
      refine ⟨130760609027985571191771023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87173739351990380794514015 130760609027985571191771023)
      ·
        refine ⟨196140913541978356787656535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130760609027985571191771023 196140913541978356787656535)
        ·
          refine ⟨294211370312967535181484803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196140913541978356787656535 294211370312967535181484803)
          ·
            refine ⟨441317055469451302772227205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294211370312967535181484803 441317055469451302772227205)
            ·
              refine ⟨82746947900522119269792601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 441317055469451302772227205 82746947900522119269792601)
              ·
                refine ⟨62060210925391589452344451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82746947900522119269792601 62060210925391589452344451)
                ·
                  refine ⟨93090316388087384178516677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62060210925391589452344451 93090316388087384178516677)
                  ·
                    refine ⟨17454434322766384533471877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93090316388087384178516677 17454434322766384533471877)
                    ·
                      refine ⟨3272706435518697100025977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17454434322766384533471877 3272706435518697100025977)
                      ·
                        rfl

theorem cell23_6373573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_6373573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373573 prefixEnd_6373573 := by exact prefixLift 6373573
  have htrace : WordTrace (prefixWord ++ tailWord_6373573) baseStart_6373573 baseEnd_6373573 := by
    simpa [prefixWord, tailWord_6373573, baseEnd_6373573] using wordTrace_append hprefix tailTrace_6373573
  have hstable : (prefixWord ++ tailWord_6373573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373573).length < 2 ^ (prefixWord ++ tailWord_6373573).sum := by decide
  have hdescent : baseEnd_6373573 < baseStart_6373573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373610 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_6373610 : Nat := 118140960795 + 6373610 * 2 ^ 59
def prefixEnd_6373610 : Nat := 4983230072969 + 3 ^ 40 * 6373610 * 2
def baseEnd_6373610 : Nat := 3272725434302913455263307

theorem tailTrace_6373610 : CollatzResearch.WordTrace tailWord_6373610 prefixEnd_6373610 3272725434302913455263307 := by
  unfold tailWord_6373610
  simp only [CollatzResearch.WordTrace]
  refine ⟨58116163609876742692783571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154976436293004647180756189 58116163609876742692783571)
  ·
    refine ⟨87174245414815114039175357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58116163609876742692783571 87174245414815114039175357)
    ·
      refine ⟨32690342030555667764690759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87174245414815114039175357 32690342030555667764690759)
      ·
        refine ⟨49035513045833501647036139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32690342030555667764690759 49035513045833501647036139)
        ·
          refine ⟨73553269568750252470554209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49035513045833501647036139 73553269568750252470554209)
          ·
            refine ⟨55164952176562689352915657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73553269568750252470554209 55164952176562689352915657)
            ·
              refine ⟨41373714132422017014686743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55164952176562689352915657 41373714132422017014686743)
              ·
                refine ⟨62060571198633025522030115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41373714132422017014686743 62060571198633025522030115)
                ·
                  refine ⟨93090856797949538283045173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62060571198633025522030115 93090856797949538283045173)
                  ·
                    refine ⟨8727267824807769214035485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93090856797949538283045173 8727267824807769214035485)
                    ·
                      refine ⟨3272725434302913455263307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8727267824807769214035485 3272725434302913455263307)
                      ·
                        rfl

theorem cell23_6373610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_6373610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373610 prefixEnd_6373610 := by exact prefixLift 6373610
  have htrace : WordTrace (prefixWord ++ tailWord_6373610) baseStart_6373610 baseEnd_6373610 := by
    simpa [prefixWord, tailWord_6373610, baseEnd_6373610] using wordTrace_append hprefix tailTrace_6373610
  have hstable : (prefixWord ++ tailWord_6373610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373610).length < 2 ^ (prefixWord ++ tailWord_6373610).sum := by decide
  have hdescent : baseEnd_6373610 < baseStart_6373610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373623 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_6373623 : Nat := 118140960795 + 6373623 * 2 ^ 59
def prefixEnd_6373623 : Nat := 4983230072969 + 3 ^ 40 * 6373623 * 2
def baseEnd_6373623 : Nat := 3272732109551421904400747

theorem tailTrace_6373623 : CollatzResearch.WordTrace tailWord_6373623 prefixEnd_6373623 3272732109551421904400747 := by
  unfold tailWord_6373623
  simp only [CollatzResearch.WordTrace]
  refine ⟨232465128588459873991357523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154976752392306582660905015 232465128588459873991357523)
  ·
    refine ⟨348697692882689810987036285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232465128588459873991357523 348697692882689810987036285)
    ·
      refine ⟨130761634831008679120138607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348697692882689810987036285 130761634831008679120138607)
      ·
        refine ⟨196142452246513018680207911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130761634831008679120138607 196142452246513018680207911)
        ·
          refine ⟨294213678369769528020311867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196142452246513018680207911 294213678369769528020311867)
          ·
            refine ⟨441320517554654292030467801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294213678369769528020311867 441320517554654292030467801)
            ·
              refine ⟨330990388165990719022850851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441320517554654292030467801 330990388165990719022850851)
              ·
                refine ⟨496485582248986078534276277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330990388165990719022850851 496485582248986078534276277)
                ·
                  refine ⟨46545523335842444862588401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 496485582248986078534276277 46545523335842444862588401)
                  ·
                    refine ⟨34909142501881833646941301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46545523335842444862588401 34909142501881833646941301)
                    ·
                      refine ⟨3272732109551421904400747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34909142501881833646941301 3272732109551421904400747)
                      ·
                        rfl

theorem cell23_6373623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_6373623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373623 prefixEnd_6373623 := by exact prefixLift 6373623
  have htrace : WordTrace (prefixWord ++ tailWord_6373623) baseStart_6373623 baseEnd_6373623 := by
    simpa [prefixWord, tailWord_6373623, baseEnd_6373623] using wordTrace_append hprefix tailTrace_6373623
  have hstable : (prefixWord ++ tailWord_6373623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373623).length < 2 ^ (prefixWord ++ tailWord_6373623).sum := by decide
  have hdescent : baseEnd_6373623 < baseStart_6373623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373640 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_6373640 : Nat := 118140960795 + 6373640 * 2 ^ 59
def prefixEnd_6373640 : Nat := 4983230072969 + 3 ^ 40 * 6373640 * 2
def baseEnd_6373640 : Nat := 3272740838722548337888169

theorem tailTrace_6373640 : CollatzResearch.WordTrace tailWord_6373640 prefixEnd_6373640 3272740838722548337888169 := by
  unfold tailWord_6373640
  simp only [CollatzResearch.WordTrace]
  refine ⟨116232874314699142947363187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154977165752932190596484249 116232874314699142947363187)
  ·
    refine ⟨174349311472048714421044781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116232874314699142947363187 174349311472048714421044781)
    ·
      refine ⟨65380991802018267907891793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174349311472048714421044781 65380991802018267907891793)
      ·
        refine ⟨49035743851513700930918845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65380991802018267907891793 49035743851513700930918845)
        ·
          refine ⟨18388403944317637849094567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49035743851513700930918845 18388403944317637849094567)
          ·
            refine ⟨27582605916476456773641851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18388403944317637849094567 27582605916476456773641851)
            ·
              refine ⟨41373908874714685160462777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27582605916476456773641851 41373908874714685160462777)
              ·
                refine ⟨31030431656036013870347083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41373908874714685160462777 31030431656036013870347083)
                ·
                  refine ⟨46545647484054020805520625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31030431656036013870347083 46545647484054020805520625)
                  ·
                    refine ⟨34909235613040515604140469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46545647484054020805520625 34909235613040515604140469)
                    ·
                      refine ⟨3272740838722548337888169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34909235613040515604140469 3272740838722548337888169)
                      ·
                        rfl

theorem cell23_6373640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_6373640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373640 prefixEnd_6373640 := by exact prefixLift 6373640
  have htrace : WordTrace (prefixWord ++ tailWord_6373640) baseStart_6373640 baseEnd_6373640 := by
    simpa [prefixWord, tailWord_6373640, baseEnd_6373640] using wordTrace_append hprefix tailTrace_6373640
  have hstable : (prefixWord ++ tailWord_6373640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373640).length < 2 ^ (prefixWord ++ tailWord_6373640).sum := by decide
  have hdescent : baseEnd_6373640 < baseStart_6373640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373667 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 2, 4, 2]
def baseStart_6373667 : Nat := 118140960795 + 6373667 * 2 ^ 59
def prefixEnd_6373667 : Nat := 4983230072969 + 3 ^ 40 * 6373667 * 2
def baseEnd_6373667 : Nat := 3272754702700219732250545

theorem tailTrace_6373667 : CollatzResearch.WordTrace tailWord_6373667 prefixEnd_6373667 3272754702700219732250545 := by
  unfold tailWord_6373667
  simp only [CollatzResearch.WordTrace]
  refine ⟨232466733400300469505959255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154977822266866979670639503 232466733400300469505959255)
  ·
    refine ⟨348700100100450704258938883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232466733400300469505959255 348700100100450704258938883)
    ·
      refine ⟨523050150150676056388408325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348700100100450704258938883 523050150150676056388408325)
      ·
        refine ⟨98071903153251760572826561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 523050150150676056388408325 98071903153251760572826561)
        ·
          refine ⟨73553927364938820429619921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98071903153251760572826561 73553927364938820429619921)
          ·
            refine ⟨55165445523704115322214941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73553927364938820429619921 55165445523704115322214941)
            ·
              refine ⟨20687042071389043245830603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55165445523704115322214941 20687042071389043245830603)
              ·
                refine ⟨31030563107083564868745905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20687042071389043245830603 31030563107083564868745905)
                ·
                  refine ⟨23272922330312673651559429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31030563107083564868745905 23272922330312673651559429)
                  ·
                    refine ⟨4363672936933626309667393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23272922330312673651559429 4363672936933626309667393)
                    ·
                      refine ⟨3272754702700219732250545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4363672936933626309667393 3272754702700219732250545)
                      ·
                        rfl

theorem cell23_6373667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_6373667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373667 prefixEnd_6373667 := by exact prefixLift 6373667
  have htrace : WordTrace (prefixWord ++ tailWord_6373667) baseStart_6373667 baseEnd_6373667 := by
    simpa [prefixWord, tailWord_6373667, baseEnd_6373667] using wordTrace_append hprefix tailTrace_6373667
  have hstable : (prefixWord ++ tailWord_6373667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373667).length < 2 ^ (prefixWord ++ tailWord_6373667).sum := by decide
  have hdescent : baseEnd_6373667 < baseStart_6373667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373684 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_6373684 : Nat := 118140960795 + 6373684 * 2 ^ 59
def prefixEnd_6373684 : Nat := 4983230072969 + 3 ^ 40 * 6373684 * 2
def baseEnd_6373684 : Nat := 3272763431871346165737967

theorem tailTrace_6373684 : CollatzResearch.WordTrace tailWord_6373684 prefixEnd_6373684 3272763431871346165737967 := by
  unfold tailWord_6373684
  simp only [CollatzResearch.WordTrace]
  refine ⟨116233676720619440704664053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154978235627492587606218737 116233676720619440704664053)
  ·
    refine ⟨10896907192558072566062255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116233676720619440704664053 10896907192558072566062255)
    ·
      refine ⟨16345360788837108849093383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10896907192558072566062255 16345360788837108849093383)
      ·
        refine ⟨24518041183255663273640075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16345360788837108849093383 24518041183255663273640075)
        ·
          refine ⟨36777061774883494910460113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24518041183255663273640075 36777061774883494910460113)
          ·
            refine ⟨27582796331162621182845085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36777061774883494910460113 27582796331162621182845085)
            ·
              refine ⟨10343548624185982943566907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27582796331162621182845085 10343548624185982943566907)
              ·
                refine ⟨15515322936278974415350361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10343548624185982943566907 15515322936278974415350361)
                ·
                  refine ⟨11636492202209230811512771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15515322936278974415350361 11636492202209230811512771)
                  ·
                    refine ⟨17454738303313846217269157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11636492202209230811512771 17454738303313846217269157)
                    ·
                      refine ⟨3272763431871346165737967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17454738303313846217269157 3272763431871346165737967)
                      ·
                        rfl

theorem cell23_6373684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_6373684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373684 prefixEnd_6373684 := by exact prefixLift 6373684
  have htrace : WordTrace (prefixWord ++ tailWord_6373684) baseStart_6373684 baseEnd_6373684 := by
    simpa [prefixWord, tailWord_6373684, baseEnd_6373684] using wordTrace_append hprefix tailTrace_6373684
  have hstable : (prefixWord ++ tailWord_6373684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373684).length < 2 ^ (prefixWord ++ tailWord_6373684).sum := by decide
  have hdescent : baseEnd_6373684 < baseStart_6373684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373720 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 3, 5]
def baseStart_6373720 : Nat := 118140960795 + 6373720 * 2 ^ 59
def prefixEnd_6373720 : Nat := 4983230072969 + 3 ^ 40 * 6373720 * 2
def baseEnd_6373720 : Nat := 1090927305724969341629267

theorem tailTrace_6373720 : CollatzResearch.WordTrace tailWord_6373720 prefixEnd_6373720 1090927305724969341629267 := by
  unfold tailWord_6373720
  simp only [CollatzResearch.WordTrace]
  refine ⟨116234333234554229778819307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154979110979405639705092409 116234333234554229778819307)
  ·
    refine ⟨174351499851831344668228961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116234333234554229778819307 174351499851831344668228961)
    ·
      refine ⟨130763624888873508501171721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174351499851831344668228961 130763624888873508501171721)
      ·
        refine ⟨98072718666655131375878791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130763624888873508501171721 98072718666655131375878791)
        ·
          refine ⟨147109077999982697063818187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98072718666655131375878791 147109077999982697063818187)
          ·
            refine ⟨220663616999974045595727281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147109077999982697063818187 220663616999974045595727281)
            ·
              refine ⟨165497712749980534196795461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220663616999974045595727281 165497712749980534196795461)
              ·
                refine ⟨31030821140621350161899149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165497712749980534196795461 31030821140621350161899149)
                ·
                  refine ⟨11636557927733006310712181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31030821140621350161899149 11636557927733006310712181)
                  ·
                    refine ⟨1090927305724969341629267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11636557927733006310712181 1090927305724969341629267)
                    ·
                      rfl

theorem cell23_6373720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_6373720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373720 prefixEnd_6373720 := by exact prefixLift 6373720
  have htrace : WordTrace (prefixWord ++ tailWord_6373720) baseStart_6373720 baseEnd_6373720 := by
    simpa [prefixWord, tailWord_6373720, baseEnd_6373720] using wordTrace_append hprefix tailTrace_6373720
  have hstable : (prefixWord ++ tailWord_6373720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373720).length < 2 ^ (prefixWord ++ tailWord_6373720).sum := by decide
  have hdescent : baseEnd_6373720 < baseStart_6373720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373727 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 1, 5, 2]
def baseStart_6373727 : Nat := 118140960795 + 6373727 * 2 ^ 59
def prefixEnd_6373727 : Nat := 4983230072969 + 3 ^ 40 * 6373727 * 2
def baseEnd_6373727 : Nat := 3272785511539489497500269

theorem tailTrace_6373727 : CollatzResearch.WordTrace tailWord_6373727 prefixEnd_6373727 3272785511539489497500269 := by
  unfold tailWord_6373727
  simp only [CollatzResearch.WordTrace]
  refine ⟨232468921780083099753143435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154979281186722066502095623 232468921780083099753143435)
  ·
    refine ⟨348703382670124649629715153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232468921780083099753143435 348703382670124649629715153)
    ·
      refine ⟨261527537002593487222286365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348703382670124649629715153 261527537002593487222286365)
      ·
        refine ⟨98072826375972557708357387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261527537002593487222286365 98072826375972557708357387)
        ·
          refine ⟨147109239563958836562536081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98072826375972557708357387 147109239563958836562536081)
          ·
            refine ⟨110331929672969127421902061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147109239563958836562536081 110331929672969127421902061)
            ·
              refine ⟨41374473627363422783213273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110331929672969127421902061 41374473627363422783213273)
              ·
                refine ⟨31030855220522567087409955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41374473627363422783213273 31030855220522567087409955)
                ·
                  refine ⟨46546282830783850631114933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31030855220522567087409955 46546282830783850631114933)
                  ·
                    refine ⟨4363714015385985996667025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46546282830783850631114933 4363714015385985996667025)
                    ·
                      refine ⟨3272785511539489497500269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4363714015385985996667025 3272785511539489497500269)
                      ·
                        rfl

theorem cell23_6373727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_6373727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373727 prefixEnd_6373727 := by exact prefixLift 6373727
  have htrace : WordTrace (prefixWord ++ tailWord_6373727) baseStart_6373727 baseEnd_6373727 := by
    simpa [prefixWord, tailWord_6373727, baseEnd_6373727] using wordTrace_append hprefix tailTrace_6373727
  have hstable : (prefixWord ++ tailWord_6373727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373727).length < 2 ^ (prefixWord ++ tailWord_6373727).sum := by decide
  have hdescent : baseEnd_6373727 < baseStart_6373727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373737 : List Nat := [1, 2, 1, 1, 1, 3, 6, 2, 1, 5]
def baseStart_6373737 : Nat := 118140960795 + 6373737 * 2 ^ 59
def prefixEnd_6373737 : Nat := 4983230072969 + 3 ^ 40 * 6373737 * 2
def baseEnd_6373737 : Nat := 1090930215448678152791741

theorem tailTrace_6373737 : CollatzResearch.WordTrace tailWord_6373737 prefixEnd_6373737 1090930215448678152791741 := by
  unfold tailWord_6373737
  simp only [CollatzResearch.WordTrace]
  refine ⟨232469286510046871461007465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154979524340031247640671643 232469286510046871461007465)
  ·
    refine ⟨174351964882535153595755599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232469286510046871461007465 174351964882535153595755599)
    ·
      refine ⟨261527947323802730393633399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174351964882535153595755599 261527947323802730393633399)
      ·
        refine ⟨392291920985704095590450099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261527947323802730393633399 392291920985704095590450099)
        ·
          refine ⟨588437881478556143385675149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392291920985704095590450099 588437881478556143385675149)
          ·
            refine ⟨220664205554458553769628181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 588437881478556143385675149 220664205554458553769628181)
            ·
              refine ⟨10343634635365244707951321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220664205554458553769628181 10343634635365244707951321)
              ·
                refine ⟨7757725976523933530963491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10343634635365244707951321 7757725976523933530963491)
                ·
                  refine ⟨11636588964785900296445237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7757725976523933530963491 11636588964785900296445237)
                  ·
                    refine ⟨1090930215448678152791741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11636588964785900296445237 1090930215448678152791741)
                    ·
                      rfl

theorem cell23_6373737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 5].length) (baseStart_6373737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373737 prefixEnd_6373737 := by exact prefixLift 6373737
  have htrace : WordTrace (prefixWord ++ tailWord_6373737) baseStart_6373737 baseEnd_6373737 := by
    simpa [prefixWord, tailWord_6373737, baseEnd_6373737] using wordTrace_append hprefix tailTrace_6373737
  have hstable : (prefixWord ++ tailWord_6373737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373737).length < 2 ^ (prefixWord ++ tailWord_6373737).sum := by decide
  have hdescent : baseEnd_6373737 < baseStart_6373737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373761 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_6373761 : Nat := 118140960795 + 6373761 * 2 ^ 59
def prefixEnd_6373761 : Nat := 4983230072969 + 3 ^ 40 * 6373761 * 2
def baseEnd_6373761 : Nat := 3272802969881742364475113

theorem tailTrace_6373761 : CollatzResearch.WordTrace tailWord_6373761 prefixEnd_6373761 3272802969881742364475113 := by
  unfold tailWord_6373761
  simp only [CollatzResearch.WordTrace]
  refine ⟨232470161861959923559881137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154980107907973282373254091 232470161861959923559881137)
  ·
    refine ⟨174352621396469942669910853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232470161861959923559881137 174352621396469942669910853)
    ·
      refine ⟨32691116511838114250608285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174352621396469942669910853 32691116511838114250608285)
      ·
        refine ⟨12259168691939292843978107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32691116511838114250608285 12259168691939292843978107)
        ·
          refine ⟨18388753037908939265967161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12259168691939292843978107 18388753037908939265967161)
          ·
            refine ⟨13791564778431704449475371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18388753037908939265967161 13791564778431704449475371)
            ·
              refine ⟨20687347167647556674213057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13791564778431704449475371 20687347167647556674213057)
              ·
                refine ⟨15515510375735667505659793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20687347167647556674213057 15515510375735667505659793)
                ·
                  refine ⟨11636632781801750629244845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15515510375735667505659793 11636632781801750629244845)
                  ·
                    refine ⟨4363737293175656485966817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11636632781801750629244845 4363737293175656485966817)
                    ·
                      refine ⟨3272802969881742364475113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4363737293175656485966817 3272802969881742364475113)
                      ·
                        rfl

theorem cell23_6373761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_6373761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373761 prefixEnd_6373761 := by exact prefixLift 6373761
  have htrace : WordTrace (prefixWord ++ tailWord_6373761) baseStart_6373761 baseEnd_6373761 := by
    simpa [prefixWord, tailWord_6373761, baseEnd_6373761] using wordTrace_append hprefix tailTrace_6373761
  have hstable : (prefixWord ++ tailWord_6373761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373761).length < 2 ^ (prefixWord ++ tailWord_6373761).sum := by decide
  have hdescent : baseEnd_6373761 < baseStart_6373761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373767 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 4, 4]
def baseStart_6373767 : Nat := 118140960795 + 6373767 * 2 ^ 59
def prefixEnd_6373767 : Nat := 4983230072969 + 3 ^ 40 * 6373767 * 2
def baseEnd_6373767 : Nat := 1090935350255223113666695

theorem tailTrace_6373767 : CollatzResearch.WordTrace tailWord_6373767 prefixEnd_6373767 1090935350255223113666695 := by
  unfold tailWord_6373767
  simp only [CollatzResearch.WordTrace]
  refine ⟨232470380699938186584599555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154980253799958791056399703 232470380699938186584599555)
  ·
    refine ⟨348705571049907279876899333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232470380699938186584599555 348705571049907279876899333)
    ·
      refine ⟨65382294571857614976918625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348705571049907279876899333 65382294571857614976918625)
      ·
        refine ⟨49036720928893211232688969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65382294571857614976918625 49036720928893211232688969)
        ·
          refine ⟨36777540696669908424516727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49036720928893211232688969 36777540696669908424516727)
          ·
            refine ⟨55166311045004862636775091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36777540696669908424516727 55166311045004862636775091)
            ·
              refine ⟨82749466567507293955162637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55166311045004862636775091 82749466567507293955162637)
              ·
                refine ⟨31031049962815235233185989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82749466567507293955162637 31031049962815235233185989)
                ·
                  refine ⟨5818321868027856606222373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31031049962815235233185989 5818321868027856606222373)
                  ·
                    refine ⟨1090935350255223113666695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5818321868027856606222373 1090935350255223113666695)
                    ·
                      rfl

theorem cell23_6373767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_6373767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373767 prefixEnd_6373767 := by exact prefixLift 6373767
  have htrace : WordTrace (prefixWord ++ tailWord_6373767) baseStart_6373767 baseEnd_6373767 := by
    simpa [prefixWord, tailWord_6373767, baseEnd_6373767] using wordTrace_append hprefix tailTrace_6373767
  have hstable : (prefixWord ++ tailWord_6373767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373767).length < 2 ^ (prefixWord ++ tailWord_6373767).sum := by decide
  have hdescent : baseEnd_6373767 < baseStart_6373767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373768 : List Nat := [2, 1, 3, 3, 1, 1, 5, 2, 1, 1, 3]
def baseStart_6373768 : Nat := 118140960795 + 6373768 * 2 ^ 59
def prefixEnd_6373768 : Nat := 4983230072969 + 3 ^ 40 * 6373768 * 2
def baseEnd_6373768 : Nat := 3272806564246323837087581

theorem tailTrace_6373768 : CollatzResearch.WordTrace tailWord_6373768 prefixEnd_6373768 3272806564246323837087581 := by
  unfold tailWord_6373768
  simp only [CollatzResearch.WordTrace]
  refine ⟨116235208586467281877692979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154980278115289709170257305 116235208586467281877692979)
  ·
    refine ⟨174352812879700922816539469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116235208586467281877692979 174352812879700922816539469)
    ·
      refine ⟨65382304829887846056202301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174352812879700922816539469 65382304829887846056202301)
      ·
        refine ⟨24518364311207942271075863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65382304829887846056202301 24518364311207942271075863)
        ·
          refine ⟨36777546466811913406613795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24518364311207942271075863 36777546466811913406613795)
          ·
            refine ⟨55166319700217870109920693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36777546466811913406613795 55166319700217870109920693)
            ·
              refine ⟨5171842471895425322805065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55166319700217870109920693 5171842471895425322805065)
              ·
                refine ⟨3878881853921568992103799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5171842471895425322805065 3878881853921568992103799)
                ·
                  refine ⟨5818322780882353488155699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3878881853921568992103799 5818322780882353488155699)
                  ·
                    refine ⟨8727484171323530232233549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5818322780882353488155699 8727484171323530232233549)
                    ·
                      refine ⟨3272806564246323837087581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8727484171323530232233549 3272806564246323837087581)
                      ·
                        rfl

theorem cell23_6373768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_6373768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373768 prefixEnd_6373768 := by exact prefixLift 6373768
  have htrace : WordTrace (prefixWord ++ tailWord_6373768) baseStart_6373768 baseEnd_6373768 := by
    simpa [prefixWord, tailWord_6373768, baseEnd_6373768] using wordTrace_append hprefix tailTrace_6373768
  have hstable : (prefixWord ++ tailWord_6373768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373768).length < 2 ^ (prefixWord ++ tailWord_6373768).sum := by decide
  have hdescent : baseEnd_6373768 < baseStart_6373768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373794 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_6373794 : Nat := 118140960795 + 6373794 * 2 ^ 59
def prefixEnd_6373794 : Nat := 4983230072969 + 3 ^ 40 * 6373794 * 2
def baseEnd_6373794 : Nat := 3272819914743340735362461

theorem tailTrace_6373794 : CollatzResearch.WordTrace tailWord_6373794 prefixEnd_6373794 3272819914743340735362461 := by
  unfold tailWord_6373794
  simp only [CollatzResearch.WordTrace]
  refine ⟨58117841367710092548958109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154980910313893580130554957 58117841367710092548958109)
  ·
    refine ⟨21794190512891284705859291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58117841367710092548958109 21794190512891284705859291)
    ·
      refine ⟨32691285769336927058788937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21794190512891284705859291 32691285769336927058788937)
      ·
        refine ⟨24518464327002695294091703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32691285769336927058788937 24518464327002695294091703)
        ·
          refine ⟨36777696490504042941137555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24518464327002695294091703 36777696490504042941137555)
          ·
            refine ⟨55166544735756064411706333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36777696490504042941137555 55166544735756064411706333)
            ·
              refine ⟨20687454275908524154389875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55166544735756064411706333 20687454275908524154389875)
              ·
                refine ⟨31031181413862786231584813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20687454275908524154389875 31031181413862786231584813)
                ·
                  refine ⟨11636693030198544836844305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31031181413862786231584813 11636693030198544836844305)
                  ·
                    refine ⟨8727519772648908627633229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11636693030198544836844305 8727519772648908627633229)
                    ·
                      refine ⟨3272819914743340735362461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8727519772648908627633229 3272819914743340735362461)
                      ·
                        rfl

theorem cell23_6373794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_6373794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373794 prefixEnd_6373794 := by exact prefixLift 6373794
  have htrace : WordTrace (prefixWord ++ tailWord_6373794) baseStart_6373794 baseEnd_6373794 := by
    simpa [prefixWord, tailWord_6373794, baseEnd_6373794] using wordTrace_append hprefix tailTrace_6373794
  have hstable : (prefixWord ++ tailWord_6373794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373794).length < 2 ^ (prefixWord ++ tailWord_6373794).sum := by decide
  have hdescent : baseEnd_6373794 < baseStart_6373794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373834 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 5, 3, 2]
def baseStart_6373834 : Nat := 118140960795 + 6373834 * 2 ^ 59
def prefixEnd_6373834 : Nat := 4983230072969 + 3 ^ 40 * 6373834 * 2
def baseEnd_6373834 : Nat := 3272840453969520578862277

theorem tailTrace_6373834 : CollatzResearch.WordTrace tailWord_6373834 prefixEnd_6373834 3272840453969520578862277 := by
  unfold tailWord_6373834
  simp only [CollatzResearch.WordTrace]
  refine ⟨58118206097673864256822139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154981882927130304684859037 58118206097673864256822139)
  ·
    refine ⟨87177309146510796385233209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58118206097673864256822139 87177309146510796385233209)
    ·
      refine ⟨65382981859883097288924907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87177309146510796385233209 65382981859883097288924907)
      ·
        refine ⟨98074472789824645933387361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65382981859883097288924907 98074472789824645933387361)
        ·
          refine ⟨73555854592368484450040521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98074472789824645933387361 73555854592368484450040521)
          ·
            refine ⟨55166890944276363337530391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73555854592368484450040521 55166890944276363337530391)
            ·
              refine ⟨82750336416414545006295587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55166890944276363337530391 82750336416414545006295587)
              ·
                refine ⟨124125504624621817509443381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82750336416414545006295587 124125504624621817509443381)
                ·
                  refine ⟨11636766058558295391510317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124125504624621817509443381 11636766058558295391510317)
                  ·
                    refine ⟨4363787271959360771816369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11636766058558295391510317 4363787271959360771816369)
                    ·
                      refine ⟨3272840453969520578862277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4363787271959360771816369 3272840453969520578862277)
                      ·
                        rfl

theorem cell23_6373834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_6373834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373834 prefixEnd_6373834 := by exact prefixLift 6373834
  have htrace : WordTrace (prefixWord ++ tailWord_6373834) baseStart_6373834 baseEnd_6373834 := by
    simpa [prefixWord, tailWord_6373834, baseEnd_6373834] using wordTrace_append hprefix tailTrace_6373834
  have hstable : (prefixWord ++ tailWord_6373834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373834).length < 2 ^ (prefixWord ++ tailWord_6373834).sum := by decide
  have hdescent : baseEnd_6373834 < baseStart_6373834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373887 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 7]
def baseStart_6373887 : Nat := 118140960795 + 6373887 * 2 ^ 59
def prefixEnd_6373887 : Nat := 4983230072969 + 3 ^ 40 * 6373887 * 2
def baseEnd_6373887 : Nat := 363651963160467652388837

theorem tailTrace_6373887 : CollatzResearch.WordTrace tailWord_6373887 prefixEnd_6373887 363651963160467652388837 := by
  unfold tailWord_6373887
  simp only [CollatzResearch.WordTrace]
  refine ⟨232474757459503447078967915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154983171639668964719311943 232474757459503447078967915)
  ·
    refine ⟨348712136189255170618451873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232474757459503447078967915 348712136189255170618451873)
    ·
      refine ⟨261534102141941377963838905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348712136189255170618451873 261534102141941377963838905)
      ·
        refine ⟨196150576606456033472879179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261534102141941377963838905 196150576606456033472879179)
        ·
          refine ⟨294225864909684050209318769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196150576606456033472879179 294225864909684050209318769)
          ·
            refine ⟨220669398682263037656989077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294225864909684050209318769 220669398682263037656989077)
            ·
              refine ⟨10343878063231079890171363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220669398682263037656989077 10343878063231079890171363)
              ·
                refine ⟨15515817094846619835257045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10343878063231079890171363 15515817094846619835257045)
                ·
                  refine ⟨363651963160467652388837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15515817094846619835257045 363651963160467652388837)
                  ·
                    rfl

theorem cell23_6373887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 7].length) (baseStart_6373887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373887 prefixEnd_6373887 := by exact prefixLift 6373887
  have htrace : WordTrace (prefixWord ++ tailWord_6373887) baseStart_6373887 baseEnd_6373887 := by
    simpa [prefixWord, tailWord_6373887, baseEnd_6373887] using wordTrace_append hprefix tailTrace_6373887
  have hstable : (prefixWord ++ tailWord_6373887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373887).length < 2 ^ (prefixWord ++ tailWord_6373887).sum := by decide
  have hdescent : baseEnd_6373887 < baseStart_6373887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373897 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 1, 5, 3]
def baseStart_6373897 : Nat := 118140960795 + 6373897 * 2 ^ 59
def prefixEnd_6373897 : Nat := 4983230072969 + 3 ^ 40 * 6373897 * 2
def baseEnd_6373897 : Nat := 3272872803250753832374487

theorem tailTrace_6373897 : CollatzResearch.WordTrace tailWord_6373897 prefixEnd_6373897 3272872803250753832374487 := by
  unfold tailWord_6373897
  simp only [CollatzResearch.WordTrace]
  refine ⟨232475122189467218786831945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154983414792978145857887963 232475122189467218786831945)
  ·
    refine ⟨174356341642100414090123959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232475122189467218786831945 174356341642100414090123959)
    ·
      refine ⟨261534512463150621135185939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174356341642100414090123959 261534512463150621135185939)
      ·
        refine ⟨392301768694725931702778909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261534512463150621135185939 392301768694725931702778909)
        ·
          refine ⟨147113163260522224388542091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392301768694725931702778909 147113163260522224388542091)
          ·
            refine ⟨220669744890783336582813137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147113163260522224388542091 220669744890783336582813137)
            ·
              refine ⟨165502308668087502437109853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220669744890783336582813137 165502308668087502437109853)
              ·
                refine ⟨62063365750532813413916195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165502308668087502437109853 62063365750532813413916195)
                ·
                  refine ⟨93095048625799220120874293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62063365750532813413916195 93095048625799220120874293)
                  ·
                    refine ⟨8727660808668676886331965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93095048625799220120874293 8727660808668676886331965)
                    ·
                      refine ⟨3272872803250753832374487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8727660808668676886331965 3272872803250753832374487)
                      ·
                        rfl

theorem cell23_6373897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5, 3].length) (baseStart_6373897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373897 prefixEnd_6373897 := by exact prefixLift 6373897
  have htrace : WordTrace (prefixWord ++ tailWord_6373897) baseStart_6373897 baseEnd_6373897 := by
    simpa [prefixWord, tailWord_6373897, baseEnd_6373897] using wordTrace_append hprefix tailTrace_6373897
  have hstable : (prefixWord ++ tailWord_6373897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373897).length < 2 ^ (prefixWord ++ tailWord_6373897).sum := by decide
  have hdescent : baseEnd_6373897 < baseStart_6373897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373964 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 5, 4]
def baseStart_6373964 : Nat := 118140960795 + 6373964 * 2 ^ 59
def prefixEnd_6373964 : Nat := 4983230072969 + 3 ^ 40 * 6373964 * 2
def baseEnd_6373964 : Nat := 1090969068818201690078893

theorem tailTrace_6373964 : CollatzResearch.WordTrace tailWord_6373964 prefixEnd_6373964 1090969068818201690078893 := by
  unfold tailWord_6373964
  simp only [CollatzResearch.WordTrace]
  refine ⟨116238782940112244614760473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154985043920149659486347297 116238782940112244614760473)
  ·
    refine ⟨87179087205084183461070355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116238782940112244614760473 87179087205084183461070355)
    ·
      refine ⟨130768630807626275191605533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87179087205084183461070355 130768630807626275191605533)
      ·
        refine ⟨49038236552859853196852075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130768630807626275191605533 49038236552859853196852075)
        ·
          refine ⟨73557354829289779795278113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49038236552859853196852075 73557354829289779795278113)
          ·
            refine ⟨55168016121967334846458585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73557354829289779795278113 55168016121967334846458585)
            ·
              refine ⟨41376012091475501134843939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55168016121967334846458585 41376012091475501134843939)
              ·
                refine ⟨62064018137213251702265909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41376012091475501134843939 62064018137213251702265909)
                ·
                  refine ⟨5818501700363742347087429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62064018137213251702265909 5818501700363742347087429)
                  ·
                    refine ⟨1090969068818201690078893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5818501700363742347087429 1090969068818201690078893)
                    ·
                      rfl

theorem cell23_6373964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_6373964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373964 prefixEnd_6373964 := by exact prefixLift 6373964
  have htrace : WordTrace (prefixWord ++ tailWord_6373964) baseStart_6373964 baseEnd_6373964 := by
    simpa [prefixWord, tailWord_6373964, baseEnd_6373964] using wordTrace_append hprefix tailTrace_6373964
  have hstable : (prefixWord ++ tailWord_6373964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373964).length < 2 ^ (prefixWord ++ tailWord_6373964).sum := by decide
  have hdescent : baseEnd_6373964 < baseStart_6373964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373967 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 4]
def baseStart_6373967 : Nat := 118140960795 + 6373967 * 2 ^ 59
def prefixEnd_6373967 : Nat := 4983230072969 + 3 ^ 40 * 6373967 * 2
def baseEnd_6373967 : Nat := 3272908746896568558499165

theorem tailTrace_6373967 : CollatzResearch.WordTrace tailWord_6373967 prefixEnd_6373967 3272908746896568558499165 := by
  unfold tailWord_6373967
  simp only [CollatzResearch.WordTrace]
  refine ⟨232477675299213620741880155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154985116866142413827920103 232477675299213620741880155)
  ·
    refine ⟨348716512948820431112820233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232477675299213620741880155 348716512948820431112820233)
    ·
      refine ⟨261537384711615323334615175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348716512948820431112820233 261537384711615323334615175)
      ·
        refine ⟨392306077067422985001922763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261537384711615323334615175 392306077067422985001922763)
        ·
          refine ⟨588459115601134477502884145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392306077067422985001922763 588459115601134477502884145)
          ·
            refine ⟨441344336700850858127163109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588459115601134477502884145 441344336700850858127163109)
            ·
              refine ⟨82752063131409535898843083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 441344336700850858127163109 82752063131409535898843083)
              ·
                refine ⟨124128094697114303848264625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82752063131409535898843083 124128094697114303848264625)
                ·
                  refine ⟨93096071022835727886198469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124128094697114303848264625 93096071022835727886198469)
                  ·
                    refine ⟨17455513316781698978662213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93096071022835727886198469 17455513316781698978662213)
                    ·
                      refine ⟨3272908746896568558499165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17455513316781698978662213 3272908746896568558499165)
                      ·
                        rfl

theorem cell23_6373967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_6373967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6373967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6373967 prefixEnd_6373967 := by exact prefixLift 6373967
  have htrace : WordTrace (prefixWord ++ tailWord_6373967) baseStart_6373967 baseEnd_6373967 := by
    simpa [prefixWord, tailWord_6373967, baseEnd_6373967] using wordTrace_append hprefix tailTrace_6373967
  have hstable : (prefixWord ++ tailWord_6373967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373967).length < 2 ^ (prefixWord ++ tailWord_6373967).sum := by decide
  have hdescent : baseEnd_6373967 < baseStart_6373967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374021 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 5, 1, 3]
def baseStart_6374021 : Nat := 118140960795 + 6374021 * 2 ^ 59
def prefixEnd_6374021 : Nat := 4983230072969 + 3 ^ 40 * 6374021 * 2
def baseEnd_6374021 : Nat := 3272936474851911347223917

theorem tailTrace_6374021 : CollatzResearch.WordTrace tailWord_6374021 prefixEnd_6374021 3272936474851911347223917 := by
  unfold tailWord_6374021
  simp only [CollatzResearch.WordTrace]
  refine ⟨232479644841017987964345917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154986429894011991976230611 232479644841017987964345917)
  ·
    refine ⟨87179866815381745486629719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232479644841017987964345917 87179866815381745486629719)
    ·
      refine ⟨130769800223072618229944579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87179866815381745486629719 130769800223072618229944579)
      ·
        refine ⟨196154700334608927344916869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130769800223072618229944579 196154700334608927344916869)
        ·
          refine ⟨36779006312739173877171913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196154700334608927344916869 36779006312739173877171913)
          ·
            refine ⟨27584254734554380407878935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36779006312739173877171913 27584254734554380407878935)
            ·
              refine ⟨41376382101831570611818403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27584254734554380407878935 41376382101831570611818403)
              ·
                refine ⟨62064573152747355917727605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41376382101831570611818403 62064573152747355917727605)
                ·
                  refine ⟨5818553733070064617286963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62064573152747355917727605 5818553733070064617286963)
                  ·
                    refine ⟨8727830599605096925930445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5818553733070064617286963 8727830599605096925930445)
                    ·
                      refine ⟨3272936474851911347223917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8727830599605096925930445 3272936474851911347223917)
                      ·
                        rfl

theorem cell23_6374021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_6374021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374021 prefixEnd_6374021 := by exact prefixLift 6374021
  have htrace : WordTrace (prefixWord ++ tailWord_6374021) baseStart_6374021 baseEnd_6374021 := by
    simpa [prefixWord, tailWord_6374021, baseEnd_6374021] using wordTrace_append hprefix tailTrace_6374021
  have hstable : (prefixWord ++ tailWord_6374021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374021).length < 2 ^ (prefixWord ++ tailWord_6374021).sum := by decide
  have hdescent : baseEnd_6374021 < baseStart_6374021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374074 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_6374074 : Nat := 118140960795 + 6374074 * 2 ^ 59
def prefixEnd_6374074 : Nat := 4983230072969 + 3 ^ 40 * 6374074 * 2
def baseEnd_6374074 : Nat := 3272963689326599639861173

theorem tailTrace_6374074 : CollatzResearch.WordTrace tailWord_6374074 prefixEnd_6374074 3272963689326599639861173 := by
  unfold tailWord_6374074
  simp only [CollatzResearch.WordTrace]
  refine ⟨58120394477456494504006319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154987718606550652010683517 58120394477456494504006319)
  ·
    refine ⟨87180591716184741756009479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58120394477456494504006319 87180591716184741756009479)
    ·
      refine ⟨130770887574277112634014219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87180591716184741756009479 130770887574277112634014219)
      ·
        refine ⟨196156331361415668951021329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130770887574277112634014219 196156331361415668951021329)
        ·
          refine ⟨147117248521061751713265997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196156331361415668951021329 147117248521061751713265997)
          ·
            refine ⟨55168968195398156892474749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147117248521061751713265997 55168968195398156892474749)
            ·
              refine ⟨20688363073274308834678031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55168968195398156892474749 20688363073274308834678031)
              ·
                refine ⟨31032544609911463252017047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20688363073274308834678031 31032544609911463252017047)
                ·
                  refine ⟨46548816914867194878025571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31032544609911463252017047 46548816914867194878025571)
                  ·
                    refine ⟨69823225372300792317038357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46548816914867194878025571 69823225372300792317038357)
                    ·
                      refine ⟨3272963689326599639861173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69823225372300792317038357 3272963689326599639861173)
                      ·
                        rfl

theorem cell23_6374074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_6374074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374074 prefixEnd_6374074 := by exact prefixLift 6374074
  have htrace : WordTrace (prefixWord ++ tailWord_6374074) baseStart_6374074 baseEnd_6374074 := by
    simpa [prefixWord, tailWord_6374074, baseEnd_6374074] using wordTrace_append hprefix tailTrace_6374074
  have hstable : (prefixWord ++ tailWord_6374074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374074).length < 2 ^ (prefixWord ++ tailWord_6374074).sum := by decide
  have hdescent : baseEnd_6374074 < baseStart_6374074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374078 : List Nat := [4, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_6374078 : Nat := 118140960795 + 6374078 * 2 ^ 59
def prefixEnd_6374078 : Nat := 4983230072969 + 3 ^ 40 * 6374078 * 2
def baseEnd_6374078 : Nat := 3272965743249217624211155

theorem tailTrace_6374078 : CollatzResearch.WordTrace tailWord_6374078 prefixEnd_6374078 3272965743249217624211155 := by
  unfold tailWord_6374078
  simp only [CollatzResearch.WordTrace]
  refine ⟨29060215475226435837396361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154987815867874324466113925 29060215475226435837396361)
  ·
    refine ⟨21795161606419826878047271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29060215475226435837396361 21795161606419826878047271)
    ·
      refine ⟨32692742409629740317070907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21795161606419826878047271 32692742409629740317070907)
      ·
        refine ⟨49039113614444610475606361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32692742409629740317070907 49039113614444610475606361)
        ·
          refine ⟨36779335210833457856704771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49039113614444610475606361 36779335210833457856704771)
          ·
            refine ⟨55169002816250186785057157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36779335210833457856704771 55169002816250186785057157)
            ·
              refine ⟨10344188028046910022198217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55169002816250186785057157 10344188028046910022198217)
              ·
                refine ⟨7758141021035182516648663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10344188028046910022198217 7758141021035182516648663)
                ·
                  refine ⟨11637211531552773774972995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7758141021035182516648663 11637211531552773774972995)
                  ·
                    refine ⟨17455817297329160662459493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11637211531552773774972995 17455817297329160662459493)
                    ·
                      refine ⟨3272965743249217624211155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17455817297329160662459493 3272965743249217624211155)
                      ·
                        rfl

theorem cell23_6374078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_6374078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374078 prefixEnd_6374078 := by exact prefixLift 6374078
  have htrace : WordTrace (prefixWord ++ tailWord_6374078) baseStart_6374078 baseEnd_6374078 := by
    simpa [prefixWord, tailWord_6374078, baseEnd_6374078] using wordTrace_append hprefix tailTrace_6374078
  have hstable : (prefixWord ++ tailWord_6374078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374078).length < 2 ^ (prefixWord ++ tailWord_6374078).sum := by decide
  have hdescent : baseEnd_6374078 < baseStart_6374078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374098 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_6374098 : Nat := 118140960795 + 6374098 * 2 ^ 59
def prefixEnd_6374098 : Nat := 4983230072969 + 3 ^ 40 * 6374098 * 2
def baseEnd_6374098 : Nat := 3272976012862307545961063

theorem tailTrace_6374098 : CollatzResearch.WordTrace tailWord_6374098 prefixEnd_6374098 3272976012862307545961063 := by
  unfold tailWord_6374098
  simp only [CollatzResearch.WordTrace]
  refine ⟨58120613315434757528724737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154988302174492686743265965 58120613315434757528724737)
  ·
    refine ⟨43590459986576068146543553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58120613315434757528724737 43590459986576068146543553)
    ·
      refine ⟨32692844989932051109907665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43590459986576068146543553 32692844989932051109907665)
      ·
        refine ⟨24519633742449038332430749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32692844989932051109907665 24519633742449038332430749)
        ·
          refine ⟨9194862653418389374661531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24519633742449038332430749 9194862653418389374661531)
          ·
            refine ⟨13792293980127584061992297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9194862653418389374661531 13792293980127584061992297)
            ·
              refine ⟨10344220485095688046494223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13792293980127584061992297 10344220485095688046494223)
              ·
                refine ⟨15516330727643532069741335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10344220485095688046494223 15516330727643532069741335)
                ·
                  refine ⟨23274496091465298104612003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15516330727643532069741335 23274496091465298104612003)
                  ·
                    refine ⟨34911744137197947156918005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23274496091465298104612003 34911744137197947156918005)
                    ·
                      refine ⟨3272976012862307545961063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34911744137197947156918005 3272976012862307545961063)
                      ·
                        rfl

theorem cell23_6374098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_6374098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374098 prefixEnd_6374098 := by exact prefixLift 6374098
  have htrace : WordTrace (prefixWord ++ tailWord_6374098) baseStart_6374098 baseEnd_6374098 := by
    simpa [prefixWord, tailWord_6374098, baseEnd_6374098] using wordTrace_append hprefix tailTrace_6374098
  have hstable : (prefixWord ++ tailWord_6374098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374098).length < 2 ^ (prefixWord ++ tailWord_6374098).sum := by decide
  have hdescent : baseEnd_6374098 < baseStart_6374098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374128 : List Nat := [2, 1, 1, 1, 3, 1, 5, 3, 2, 1, 3]
def baseStart_6374128 : Nat := 118140960795 + 6374128 * 2 ^ 59
def prefixEnd_6374128 : Nat := 4983230072969 + 3 ^ 40 * 6374128 * 2
def baseEnd_6374128 : Nat := 3272991417281942428585925

theorem tailTrace_6374128 : CollatzResearch.WordTrace tailWord_6374128 prefixEnd_6374128 3272991417281942428585925 := by
  unfold tailWord_6374128
  simp only [CollatzResearch.WordTrace]
  refine ⟨116241773725815172619245519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154989031634420230158994025 116241773725815172619245519)
  ·
    refine ⟨174362660588722758928868279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116241773725815172619245519 174362660588722758928868279)
    ·
      refine ⟨261543990883084138393302419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174362660588722758928868279 261543990883084138393302419)
      ·
        refine ⟨392315986324626207589953629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261543990883084138393302419 392315986324626207589953629)
        ·
          refine ⟨147118494871734827846232611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392315986324626207589953629 147118494871734827846232611)
          ·
            refine ⟨220677742307602241769348917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147118494871734827846232611 220677742307602241769348917)
            ·
              refine ⟨20688538341337710165876461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220677742307602241769348917 20688538341337710165876461)
              ·
                refine ⟨7758201878001641312203673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20688538341337710165876461 7758201878001641312203673)
                ·
                  refine ⟨5818651408501230984152755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7758201878001641312203673 5818651408501230984152755)
                  ·
                    refine ⟨8727977112751846476229133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5818651408501230984152755 8727977112751846476229133)
                    ·
                      refine ⟨3272991417281942428585925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8727977112751846476229133 3272991417281942428585925)
                      ·
                        rfl

theorem cell23_6374128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 2, 1, 3].length) (baseStart_6374128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374128 prefixEnd_6374128 := by exact prefixLift 6374128
  have htrace : WordTrace (prefixWord ++ tailWord_6374128) baseStart_6374128 baseEnd_6374128 := by
    simpa [prefixWord, tailWord_6374128, baseEnd_6374128] using wordTrace_append hprefix tailTrace_6374128
  have hstable : (prefixWord ++ tailWord_6374128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374128).length < 2 ^ (prefixWord ++ tailWord_6374128).sum := by decide
  have hdescent : baseEnd_6374128 < baseStart_6374128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374132 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_6374132 : Nat := 118140960795 + 6374132 * 2 ^ 59
def prefixEnd_6374132 : Nat := 4983230072969 + 3 ^ 40 * 6374132 * 2
def baseEnd_6374132 : Nat := 3272993471204560412935907

theorem tailTrace_6374132 : CollatzResearch.WordTrace tailWord_6374132 prefixEnd_6374132 3272993471204560412935907 := by
  unfold tailWord_6374132
  simp only [CollatzResearch.WordTrace]
  refine ⟨116241846671807926960818325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154989128895743902614424433 116241846671807926960818325)
  ·
    refine ⟨5448836562740996576288359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116241846671807926960818325 5448836562740996576288359)
    ·
      refine ⟨8173254844111494864432539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5448836562740996576288359 8173254844111494864432539)
      ·
        refine ⟨12259882266167242296648809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8173254844111494864432539 12259882266167242296648809)
        ·
          refine ⟨9194911699625431722486607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12259882266167242296648809 9194911699625431722486607)
          ·
            refine ⟨13792367549438147583729911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9194911699625431722486607 13792367549438147583729911)
            ·
              refine ⟨20688551324157221375594867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13792367549438147583729911 20688551324157221375594867)
              ·
                refine ⟨31032826986235832063392301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20688551324157221375594867 31032826986235832063392301)
                ·
                  refine ⟨11637310119838437023772113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31032826986235832063392301 11637310119838437023772113)
                  ·
                    refine ⟨8727982589878827767829085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11637310119838437023772113 8727982589878827767829085)
                    ·
                      refine ⟨3272993471204560412935907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8727982589878827767829085 3272993471204560412935907)
                      ·
                        rfl

theorem cell23_6374132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_6374132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374132 prefixEnd_6374132 := by exact prefixLift 6374132
  have htrace : WordTrace (prefixWord ++ tailWord_6374132) baseStart_6374132 baseEnd_6374132 := by
    simpa [prefixWord, tailWord_6374132, baseEnd_6374132] using wordTrace_append hprefix tailTrace_6374132
  have hstable : (prefixWord ++ tailWord_6374132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374132).length < 2 ^ (prefixWord ++ tailWord_6374132).sum := by decide
  have hdescent : baseEnd_6374132 < baseStart_6374132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374181 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_6374181 : Nat := 118140960795 + 6374181 * 2 ^ 59
def prefixEnd_6374181 : Nat := 4983230072969 + 3 ^ 40 * 6374181 * 2
def baseEnd_6374181 : Nat := 3273018631756630721223181

theorem tailTrace_6374181 : CollatzResearch.WordTrace tailWord_6374181 prefixEnd_6374181 3273018631756630721223181 := by
  unfold tailWord_6374181
  simp only [CollatzResearch.WordTrace]
  refine ⟨232485480520438335290170397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154990320346958890193446931 232485480520438335290170397)
  ·
    refine ⟨87182055195164375733813899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232485480520438335290170397 87182055195164375733813899)
    ·
      refine ⟨130773082792746563600720849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87182055195164375733813899 130773082792746563600720849)
      ·
        refine ⟨98079812094559922700540637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130773082792746563600720849 98079812094559922700540637)
        ·
          refine ⟨36779929535459971012702739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98079812094559922700540637 36779929535459971012702739)
          ·
            refine ⟨55169894303189956519054109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36779929535459971012702739 55169894303189956519054109)
            ·
              refine ⟨20688710363696233694645291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55169894303189956519054109 20688710363696233694645291)
              ·
                refine ⟨31033065545544350541967937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20688710363696233694645291 31033065545544350541967937)
                ·
                  refine ⟨23274799159158262906475953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31033065545544350541967937 23274799159158262906475953)
                  ·
                    refine ⟨17456099369368697179856965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23274799159158262906475953 17456099369368697179856965)
                    ·
                      refine ⟨3273018631756630721223181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17456099369368697179856965 3273018631756630721223181)
                      ·
                        rfl

theorem cell23_6374181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_6374181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374181 prefixEnd_6374181 := by exact prefixLift 6374181
  have htrace : WordTrace (prefixWord ++ tailWord_6374181) baseStart_6374181 baseEnd_6374181 := by
    simpa [prefixWord, tailWord_6374181, baseEnd_6374181] using wordTrace_append hprefix tailTrace_6374181
  have hstable : (prefixWord ++ tailWord_6374181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374181).length < 2 ^ (prefixWord ++ tailWord_6374181).sum := by decide
  have hdescent : baseEnd_6374181 < baseStart_6374181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374206 : List Nat := [4, 2, 1, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_6374206 : Nat := 118140960795 + 6374206 * 2 ^ 59
def prefixEnd_6374206 : Nat := 4983230072969 + 3 ^ 40 * 6374206 * 2
def baseEnd_6374206 : Nat := 3273031468772993123410567

theorem tailTrace_6374206 : CollatzResearch.WordTrace tailWord_6374206 prefixEnd_6374206 3273031468772993123410567 := by
  unfold tailWord_6374206
  simp only [CollatzResearch.WordTrace]
  refine ⟨29060799043168470569978809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154990928230231843039886981 29060799043168470569978809)
  ·
    refine ⟨21795599282376352927484107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29060799043168470569978809 21795599282376352927484107)
    ·
      refine ⟨32693398923564529391226161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21795599282376352927484107 32693398923564529391226161)
      ·
        refine ⟨24520049192673397043419621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32693398923564529391226161 24520049192673397043419621)
        ·
          refine ⟨4597509223626261945641179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24520049192673397043419621 4597509223626261945641179)
          ·
            refine ⟨6896263835439392918461769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4597509223626261945641179 6896263835439392918461769)
            ·
              refine ⟨5172197876579544688846327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6896263835439392918461769 5172197876579544688846327)
              ·
                refine ⟨7758296814869317033269491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5172197876579544688846327 7758296814869317033269491)
                ·
                  refine ⟨11637445222303975549904237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7758296814869317033269491 11637445222303975549904237)
                  ·
                    refine ⟨4364041958363990831214089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11637445222303975549904237 4364041958363990831214089)
                    ·
                      refine ⟨3273031468772993123410567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4364041958363990831214089 3273031468772993123410567)
                      ·
                        rfl

theorem cell23_6374206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_6374206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374206 prefixEnd_6374206 := by exact prefixLift 6374206
  have htrace : WordTrace (prefixWord ++ tailWord_6374206) baseStart_6374206 baseEnd_6374206 := by
    simpa [prefixWord, tailWord_6374206, baseEnd_6374206] using wordTrace_append hprefix tailTrace_6374206
  have hstable : (prefixWord ++ tailWord_6374206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374206).length < 2 ^ (prefixWord ++ tailWord_6374206).sum := by decide
  have hdescent : baseEnd_6374206 < baseStart_6374206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374241 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_6374241 : Nat := 118140960795 + 6374241 * 2 ^ 59
def prefixEnd_6374241 : Nat := 4983230072969 + 3 ^ 40 * 6374241 * 2
def baseEnd_6374241 : Nat := 3273049440595900486472905

theorem tailTrace_6374241 : CollatzResearch.WordTrace tailWord_6374241 prefixEnd_6374241 3273049440595900486472905 := by
  unfold tailWord_6374241
  simp only [CollatzResearch.WordTrace]
  refine ⟨232487668900220965537354577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154991779266813977024903051 232487668900220965537354577)
  ·
    refine ⟨174365751675165724153015933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232487668900220965537354577 174365751675165724153015933)
    ·
      refine ⟨65387156878187146557380975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174365751675165724153015933 65387156878187146557380975)
      ·
        refine ⟨98080735317280719836071463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65387156878187146557380975 98080735317280719836071463)
        ·
          refine ⟨147121102975921079754107195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98080735317280719836071463 147121102975921079754107195)
          ·
            refine ⟨220681654463881619631160793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147121102975921079754107195 220681654463881619631160793)
            ·
              refine ⟨165511240847911214723370595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220681654463881619631160793 165511240847911214723370595)
              ·
                refine ⟨248266861271866822085055893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165511240847911214723370595 248266861271866822085055893)
                ·
                  refine ⟨11637509122118757285236995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 248266861271866822085055893 11637509122118757285236995)
                  ·
                    refine ⟨17456263683178135927855493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11637509122118757285236995 17456263683178135927855493)
                    ·
                      refine ⟨3273049440595900486472905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17456263683178135927855493 3273049440595900486472905)
                      ·
                        rfl

theorem cell23_6374241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_6374241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374241 prefixEnd_6374241 := by exact prefixLift 6374241
  have htrace : WordTrace (prefixWord ++ tailWord_6374241) baseStart_6374241 baseEnd_6374241 := by
    simpa [prefixWord, tailWord_6374241, baseEnd_6374241] using wordTrace_append hprefix tailTrace_6374241
  have hstable : (prefixWord ++ tailWord_6374241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374241).length < 2 ^ (prefixWord ++ tailWord_6374241).sum := by decide
  have hdescent : baseEnd_6374241 < baseStart_6374241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374258 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 1, 6, 2]
def baseStart_6374258 : Nat := 118140960795 + 6374258 * 2 ^ 59
def prefixEnd_6374258 : Nat := 4983230072969 + 3 ^ 40 * 6374258 * 2
def baseEnd_6374258 : Nat := 3273058169767026919960327

theorem tailTrace_6374258 : CollatzResearch.WordTrace tailWord_6374258 prefixEnd_6374258 3273058169767026919960327 := by
  unfold tailWord_6374258
  simp only [CollatzResearch.WordTrace]
  refine ⟨58122072235289844360180857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154992192627439584960482285 58122072235289844360180857)
  ·
    refine ⟨43591554176467383270135643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58122072235289844360180857 43591554176467383270135643)
    ·
      refine ⟨65387331264701074905203465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43591554176467383270135643 65387331264701074905203465)
      ·
        refine ⟨49040498448525806178902599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65387331264701074905203465 49040498448525806178902599)
        ·
          refine ⟨73560747672788709268353899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49040498448525806178902599 73560747672788709268353899)
          ·
            refine ⟨110341121509183063902530849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73560747672788709268353899 110341121509183063902530849)
            ·
              refine ⟨82755841131887297926898137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110341121509183063902530849 82755841131887297926898137)
              ·
                refine ⟨62066880848915473445173603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82755841131887297926898137 62066880848915473445173603)
                ·
                  refine ⟨93100321273373210167760405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62066880848915473445173603 93100321273373210167760405)
                  ·
                    refine ⟨4364077559689369226613769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93100321273373210167760405 4364077559689369226613769)
                    ·
                      refine ⟨3273058169767026919960327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4364077559689369226613769 3273058169767026919960327)
                      ·
                        rfl

theorem cell23_6374258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_6374258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374258 prefixEnd_6374258 := by exact prefixLift 6374258
  have htrace : WordTrace (prefixWord ++ tailWord_6374258) baseStart_6374258 baseEnd_6374258 := by
    simpa [prefixWord, tailWord_6374258, baseEnd_6374258] using wordTrace_append hprefix tailTrace_6374258
  have hstable : (prefixWord ++ tailWord_6374258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374258).length < 2 ^ (prefixWord ++ tailWord_6374258).sum := by decide
  have hdescent : baseEnd_6374258 < baseStart_6374258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374281 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 8]
def baseStart_6374281 : Nat := 118140960795 + 6374281 * 2 ^ 59
def prefixEnd_6374281 : Nat := 4983230072969 + 3 ^ 40 * 6374281 * 2
def baseEnd_6374281 : Nat := 363674442202453369996969

theorem tailTrace_6374281 : CollatzResearch.WordTrace tailWord_6374281 prefixEnd_6374281 363674442202453369996969 := by
  unfold tailWord_6374281
  simp only [CollatzResearch.WordTrace]
  refine ⟨232489127820076052368810697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154992751880050701579207131 232489127820076052368810697)
  ·
    refine ⟨174366845865057039276608023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232489127820076052368810697 174366845865057039276608023)
    ·
      refine ⟨261550268797585558914912035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174366845865057039276608023 261550268797585558914912035)
      ·
        refine ⟨392325403196378338372368053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261550268797585558914912035 392325403196378338372368053)
        ·
          refine ⟨36780506549660469222409505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 392325403196378338372368053 36780506549660469222409505)
          ·
            refine ⟨27585379912245351916807129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36780506549660469222409505 27585379912245351916807129)
            ·
              refine ⟨20689034934184013937605347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27585379912245351916807129 20689034934184013937605347)
              ·
                refine ⟨31033552401276020906408021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20689034934184013937605347 31033552401276020906408021)
                ·
                  refine ⟨363674442202453369996969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31033552401276020906408021 363674442202453369996969)
                  ·
                    rfl

theorem cell23_6374281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 8].length) (baseStart_6374281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374281 prefixEnd_6374281 := by exact prefixLift 6374281
  have htrace : WordTrace (prefixWord ++ tailWord_6374281) baseStart_6374281 baseEnd_6374281 := by
    simpa [prefixWord, tailWord_6374281, baseEnd_6374281] using wordTrace_append hprefix tailTrace_6374281
  have hstable : (prefixWord ++ tailWord_6374281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374281).length < 2 ^ (prefixWord ++ tailWord_6374281).sum := by decide
  have hdescent : baseEnd_6374281 < baseStart_6374281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374291 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 3]
def baseStart_6374291 : Nat := 118140960795 + 6374291 * 2 ^ 59
def prefixEnd_6374291 : Nat := 4983230072969 + 3 ^ 40 * 6374291 * 2
def baseEnd_6374291 : Nat := 3273075114628625290847675

theorem tailTrace_6374291 : CollatzResearch.WordTrace tailWord_6374291 prefixEnd_6374291 3273075114628625290847675 := by
  unfold tailWord_6374291
  simp only [CollatzResearch.WordTrace]
  refine ⟨232489492550039824076674727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154992995033359882717783151 232489492550039824076674727)
  ·
    refine ⟨348734238825059736115012091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232489492550039824076674727 348734238825059736115012091)
    ·
      refine ⟨523101358237589604172518137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348734238825059736115012091 523101358237589604172518137)
      ·
        refine ⟨392326018678192203129388603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523101358237589604172518137 392326018678192203129388603)
        ·
          refine ⟨588489028017288304694082905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392326018678192203129388603 588489028017288304694082905)
          ·
            refine ⟨441366771012966228520562179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588489028017288304694082905 441366771012966228520562179)
            ·
              refine ⟨662050156519449342780843269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441366771012966228520562179 662050156519449342780843269)
              ·
                refine ⟨124134404347396751771408113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 662050156519449342780843269 124134404347396751771408113)
                ·
                  refine ⟨93100803260547563828556085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124134404347396751771408113 93100803260547563828556085)
                  ·
                    refine ⟨8728200305676334108927133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93100803260547563828556085 8728200305676334108927133)
                    ·
                      refine ⟨3273075114628625290847675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8728200305676334108927133 3273075114628625290847675)
                      ·
                        rfl

theorem cell23_6374291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 3].length) (baseStart_6374291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374291 prefixEnd_6374291 := by exact prefixLift 6374291
  have htrace : WordTrace (prefixWord ++ tailWord_6374291) baseStart_6374291 baseEnd_6374291 := by
    simpa [prefixWord, tailWord_6374291, baseEnd_6374291] using wordTrace_append hprefix tailTrace_6374291
  have hstable : (prefixWord ++ tailWord_6374291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374291).length < 2 ^ (prefixWord ++ tailWord_6374291).sum := by decide
  have hdescent : baseEnd_6374291 < baseStart_6374291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374348 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 5, 1, 4]
def baseStart_6374348 : Nat := 118140960795 + 6374348 * 2 ^ 59
def prefixEnd_6374348 : Nat := 4983230072969 + 3 ^ 40 * 6374348 * 2
def baseEnd_6374348 : Nat := 3273104383025931567834913

theorem tailTrace_6374348 : CollatzResearch.WordTrace tailWord_6374348 prefixEnd_6374348 3273104383025931567834913 := by
  unfold tailWord_6374348
  simp only [CollatzResearch.WordTrace]
  refine ⟨116245785755416661405749849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154994381007222215207666465 116245785755416661405749849)
  ·
    refine ⟨87184339316562496054312387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116245785755416661405749849 87184339316562496054312387)
    ·
      refine ⟨130776508974843744081468581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87184339316562496054312387 130776508974843744081468581)
      ·
        refine ⟨24520595432783202015275359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130776508974843744081468581 24520595432783202015275359)
        ·
          refine ⟨36780893149174803022913039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24520595432783202015275359 36780893149174803022913039)
          ·
            refine ⟨55171339723762204534369559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36780893149174803022913039 55171339723762204534369559)
            ·
              refine ⟨82757009585643306801554339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55171339723762204534369559 82757009585643306801554339)
              ·
                refine ⟨124135514378464960202331509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82757009585643306801554339 124135514378464960202331509)
                ·
                  refine ⟨11637704472981090018968579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124135514378464960202331509 11637704472981090018968579)
                  ·
                    refine ⟨17456556709471635028452869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11637704472981090018968579 17456556709471635028452869)
                    ·
                      refine ⟨3273104383025931567834913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17456556709471635028452869 3273104383025931567834913)
                      ·
                        rfl

theorem cell23_6374348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_6374348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374348 prefixEnd_6374348 := by exact prefixLift 6374348
  have htrace : WordTrace (prefixWord ++ tailWord_6374348) baseStart_6374348 baseEnd_6374348 := by
    simpa [prefixWord, tailWord_6374348, baseEnd_6374348] using wordTrace_append hprefix tailTrace_6374348
  have hstable : (prefixWord ++ tailWord_6374348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374348).length < 2 ^ (prefixWord ++ tailWord_6374348).sum := by decide
  have hdescent : baseEnd_6374348 < baseStart_6374348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374365 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_6374365 : Nat := 118140960795 + 6374365 * 2 ^ 59
def prefixEnd_6374365 : Nat := 4983230072969 + 3 ^ 40 * 6374365 * 2
def baseEnd_6374365 : Nat := 3273113112197058001322335

theorem tailTrace_6374365 : CollatzResearch.WordTrace tailWord_6374365 prefixEnd_6374365 3273113112197058001322335 := by
  unfold tailWord_6374365
  simp only [CollatzResearch.WordTrace]
  refine ⟨232492191551771734714868549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154994794367847823143245699 232492191551771734714868549)
  ·
    refine ⟨43592285915957200259037853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232492191551771734714868549 43592285915957200259037853)
    ·
      refine ⟨16347107218483950097139195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43592285915957200259037853 16347107218483950097139195)
      ·
        refine ⟨24520660827725925145708793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16347107218483950097139195 24520660827725925145708793)
        ·
          refine ⟨18390495620794443859281595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24520660827725925145708793 18390495620794443859281595)
          ·
            refine ⟨27585743431191665788922393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18390495620794443859281595 27585743431191665788922393)
            ·
              refine ⟨20689307573393749341691795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27585743431191665788922393 20689307573393749341691795)
              ·
                refine ⟨31033961360090624012537693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20689307573393749341691795 31033961360090624012537693)
                ·
                  refine ⟨11637735510033984004701635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31033961360090624012537693 11637735510033984004701635)
                  ·
                    refine ⟨17456603265050976007052453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11637735510033984004701635 17456603265050976007052453)
                    ·
                      refine ⟨3273113112197058001322335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17456603265050976007052453 3273113112197058001322335)
                      ·
                        rfl

theorem cell23_6374365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_6374365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374365 prefixEnd_6374365 := by exact prefixLift 6374365
  have htrace : WordTrace (prefixWord ++ tailWord_6374365) baseStart_6374365 baseEnd_6374365 := by
    simpa [prefixWord, tailWord_6374365, baseEnd_6374365] using wordTrace_append hprefix tailTrace_6374365
  have hstable : (prefixWord ++ tailWord_6374365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374365).length < 2 ^ (prefixWord ++ tailWord_6374365).sum := by decide
  have hdescent : baseEnd_6374365 < baseStart_6374365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374382 : List Nat := [4, 1, 2, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_6374382 : Nat := 118140960795 + 6374382 * 2 ^ 59
def prefixEnd_6374382 : Nat := 4983230072969 + 3 ^ 40 * 6374382 * 2
def baseEnd_6374382 : Nat := 3273121841368184434809757

theorem tailTrace_6374382 : CollatzResearch.WordTrace tailWord_6374382 prefixEnd_6374382 3273121841368184434809757 := by
  unfold tailWord_6374382
  simp only [CollatzResearch.WordTrace]
  refine ⟨29061601449088768327279675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154995207728473431078824933 29061601449088768327279675)
  ·
    refine ⟨43592402173633152490919513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29061601449088768327279675 43592402173633152490919513)
    ·
      refine ⟨32694301630224864368189635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43592402173633152490919513 32694301630224864368189635)
      ·
        refine ⟨49041452445337296552284453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32694301630224864368189635 49041452445337296552284453)
        ·
          refine ⟨9195272333500743103553335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49041452445337296552284453 9195272333500743103553335)
          ·
            refine ⟨13792908500251114655330003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9195272333500743103553335 13792908500251114655330003)
            ·
              refine ⟨20689362750376671982995005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13792908500251114655330003 20689362750376671982995005)
              ·
                refine ⟨7758511031391251993623127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20689362750376671982995005 7758511031391251993623127)
                ·
                  refine ⟨11637766547086877990434691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7758511031391251993623127 11637766547086877990434691)
                  ·
                    refine ⟨17456649820630316985652037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11637766547086877990434691 17456649820630316985652037)
                    ·
                      refine ⟨3273121841368184434809757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17456649820630316985652037 3273121841368184434809757)
                      ·
                        rfl

theorem cell23_6374382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_6374382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374382 prefixEnd_6374382 := by exact prefixLift 6374382
  have htrace : WordTrace (prefixWord ++ tailWord_6374382) baseStart_6374382 baseEnd_6374382 := by
    simpa [prefixWord, tailWord_6374382, baseEnd_6374382] using wordTrace_append hprefix tailTrace_6374382
  have hstable : (prefixWord ++ tailWord_6374382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374382).length < 2 ^ (prefixWord ++ tailWord_6374382).sum := by decide
  have hdescent : baseEnd_6374382 < baseStart_6374382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374425 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 3, 3, 2]
def baseStart_6374425 : Nat := 118140960795 + 6374425 * 2 ^ 59
def prefixEnd_6374425 : Nat := 4983230072969 + 3 ^ 40 * 6374425 * 2
def baseEnd_6374425 : Nat := 3273143921036327766572059

theorem tailTrace_6374425 : CollatzResearch.WordTrace tailWord_6374425 prefixEnd_6374425 3273143921036327766572059 := by
  unfold tailWord_6374425
  simp only [CollatzResearch.WordTrace]
  refine ⟨232494379931554364962052729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154996253287702909974701819 232494379931554364962052729)
  ·
    refine ⟨174370784948665773721539547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232494379931554364962052729 174370784948665773721539547)
    ·
      refine ⟨261556177422998660582309321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174370784948665773721539547 261556177422998660582309321)
      ·
        refine ⟨196167133067248995436731991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261556177422998660582309321 196167133067248995436731991)
        ·
          refine ⟨294250699600873493155097987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196167133067248995436731991 294250699600873493155097987)
          ·
            refine ⟨441376049401310239732646981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294250699600873493155097987 441376049401310239732646981)
            ·
              refine ⟨82758009262745669949871309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 441376049401310239732646981 82758009262745669949871309)
              ·
                refine ⟨31034253473529626231201741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82758009262745669949871309 31034253473529626231201741)
                ·
                  refine ⟨11637845052573609836700653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31034253473529626231201741 11637845052573609836700653)
                  ·
                    refine ⟨4364191894715103688762745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11637845052573609836700653 4364191894715103688762745)
                    ·
                      refine ⟨3273143921036327766572059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4364191894715103688762745 3273143921036327766572059)
                      ·
                        rfl

theorem cell23_6374425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 3, 2].length) (baseStart_6374425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374425 prefixEnd_6374425 := by exact prefixLift 6374425
  have htrace : WordTrace (prefixWord ++ tailWord_6374425) baseStart_6374425 baseEnd_6374425 := by
    simpa [prefixWord, tailWord_6374425, baseEnd_6374425] using wordTrace_append hprefix tailTrace_6374425
  have hstable : (prefixWord ++ tailWord_6374425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374425).length < 2 ^ (prefixWord ++ tailWord_6374425).sum := by decide
  have hdescent : baseEnd_6374425 < baseStart_6374425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374478 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 9]
def baseStart_6374478 : Nat := 118140960795 + 6374478 * 2 ^ 59
def prefixEnd_6374478 : Nat := 4983230072969 + 3 ^ 40 * 6374478 * 2
def baseEnd_6374478 : Nat := 363685681723446228801035

theorem tailTrace_6374478 : CollatzResearch.WordTrace tailWord_6374478 prefixEnd_6374478 363685681723446228801035 := by
  unfold tailWord_6374478
  simp only [CollatzResearch.WordTrace]
  refine ⟨29062039125045294376716511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154997542000241570009154725 29062039125045294376716511)
  ·
    refine ⟨43593058687567941565074767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29062039125045294376716511 43593058687567941565074767)
    ·
      refine ⟨65389588031351912347612151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43593058687567941565074767 65389588031351912347612151)
      ·
        refine ⟨98084382047027868521418227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65389588031351912347612151 98084382047027868521418227)
        ·
          refine ⟨147126573070541802782127341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98084382047027868521418227 147126573070541802782127341)
          ·
            refine ⟨55172464901453176043297753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147126573070541802782127341 55172464901453176043297753)
            ·
              refine ⟨41379348676089882032473315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55172464901453176043297753 41379348676089882032473315)
              ·
                refine ⟨62069023014134823048709973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41379348676089882032473315 62069023014134823048709973)
                ·
                  refine ⟨363685681723446228801035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62069023014134823048709973 363685681723446228801035)
                  ·
                    rfl

theorem cell23_6374478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_6374478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374478 prefixEnd_6374478 := by exact prefixLift 6374478
  have htrace : WordTrace (prefixWord ++ tailWord_6374478) baseStart_6374478 baseEnd_6374478 := by
    simpa [prefixWord, tailWord_6374478, baseEnd_6374478] using wordTrace_append hprefix tailTrace_6374478
  have hstable : (prefixWord ++ tailWord_6374478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374478).length < 2 ^ (prefixWord ++ tailWord_6374478).sum := by decide
  have hdescent : baseEnd_6374478 < baseStart_6374478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374493 : List Nat := [1, 4, 4, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_6374493 : Nat := 118140960795 + 6374493 * 2 ^ 59
def prefixEnd_6374493 : Nat := 4983230072969 + 3 ^ 40 * 6374493 * 2
def baseEnd_6374493 : Nat := 3273178837720833500521747

theorem tailTrace_6374493 : CollatzResearch.WordTrace tailWord_6374493 prefixEnd_6374493 3273178837720833500521747 := by
  unfold tailWord_6374493
  simp only [CollatzResearch.WordTrace]
  refine ⟨232496860095308012575528133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154997906730205341717018755 232496860095308012575528133)
  ·
    refine ⟨43593161267870252357911525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232496860095308012575528133 43593161267870252357911525)
    ·
      refine ⟨8173717737725672317108411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43593161267870252357911525 8173717737725672317108411)
      ·
        refine ⟨12260576606588508475662617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8173717737725672317108411 12260576606588508475662617)
        ·
          refine ⟨9195432454941381356746963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12260576606588508475662617 9195432454941381356746963)
          ·
            refine ⟨13793148682412072035120445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9195432454941381356746963 13793148682412072035120445)
            ·
              refine ⟨5172430755904527013170167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13793148682412072035120445 5172430755904527013170167)
              ·
                refine ⟨7758646133856790519755251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5172430755904527013170167 7758646133856790519755251)
                ·
                  refine ⟨11637969200785185779632877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7758646133856790519755251 11637969200785185779632877)
                  ·
                    refine ⟨4364238450294444667362329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11637969200785185779632877 4364238450294444667362329)
                    ·
                      refine ⟨3273178837720833500521747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4364238450294444667362329 3273178837720833500521747)
                      ·
                        rfl

theorem cell23_6374493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_6374493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374493 prefixEnd_6374493 := by exact prefixLift 6374493
  have htrace : WordTrace (prefixWord ++ tailWord_6374493) baseStart_6374493 baseEnd_6374493 := by
    simpa [prefixWord, tailWord_6374493, baseEnd_6374493] using wordTrace_append hprefix tailTrace_6374493
  have hstable : (prefixWord ++ tailWord_6374493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374493).length < 2 ^ (prefixWord ++ tailWord_6374493).sum := by decide
  have hdescent : baseEnd_6374493 < baseStart_6374493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374495 : List Nat := [1, 1, 2, 3, 1, 1, 4, 5, 5]
def baseStart_6374495 : Nat := 118140960795 + 6374495 * 2 ^ 59
def prefixEnd_6374495 : Nat := 4983230072969 + 3 ^ 40 * 6374495 * 2
def baseEnd_6374495 : Nat := 363686651631349165855193

theorem tailTrace_6374495 : CollatzResearch.WordTrace tailWord_6374495 prefixEnd_6374495 363686651631349165855193 := by
  unfold tailWord_6374495
  simp only [CollatzResearch.WordTrace]
  refine ⟨232496933041300766917100939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154997955360867177944733959 232496933041300766917100939)
  ·
    refine ⟨348745399561951150375651409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232496933041300766917100939 348745399561951150375651409)
    ·
      refine ⟨261559049671463362781738557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348745399561951150375651409 261559049671463362781738557)
      ·
        refine ⟨98084643626798761043151959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261559049671463362781738557 98084643626798761043151959)
        ·
          refine ⟨147126965440198141564727939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98084643626798761043151959 147126965440198141564727939)
          ·
            refine ⟨220690448160297212347091909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147126965440198141564727939 220690448160297212347091909)
            ·
              refine ⟨41379459030055727315079733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220690448160297212347091909 41379459030055727315079733)
              ·
                refine ⟨3879324284067724435788725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41379459030055727315079733 3879324284067724435788725)
                ·
                  refine ⟨363686651631349165855193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3879324284067724435788725 363686651631349165855193)
                  ·
                    rfl

theorem cell23_6374495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 5].length) (baseStart_6374495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374495 prefixEnd_6374495 := by exact prefixLift 6374495
  have htrace : WordTrace (prefixWord ++ tailWord_6374495) baseStart_6374495 baseEnd_6374495 := by
    simpa [prefixWord, tailWord_6374495, baseEnd_6374495] using wordTrace_append hprefix tailTrace_6374495
  have hstable : (prefixWord ++ tailWord_6374495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374495).length < 2 ^ (prefixWord ++ tailWord_6374495).sum := by decide
  have hdescent : baseEnd_6374495 < baseStart_6374495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374506 : List Nat := [3, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_6374506 : Nat := 118140960795 + 6374506 * 2 ^ 59
def prefixEnd_6374506 : Nat := 4983230072969 + 3 ^ 40 * 6374506 * 2
def baseEnd_6374506 : Nat := 3273185512969341949659187

theorem tailTrace_6374506 : CollatzResearch.WordTrace tailWord_6374506 prefixEnd_6374506 3273185512969341949659187 := by
  unfold tailWord_6374506
  simp only [CollatzResearch.WordTrace]
  refine ⟨58124333561065228948937843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154998222829507277197167581 58124333561065228948937843)
  ·
    refine ⟨87186500341597843423406765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58124333561065228948937843 87186500341597843423406765)
    ·
      refine ⟨32694937628099191283777537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87186500341597843423406765 32694937628099191283777537)
      ·
        refine ⟨24521203221074393462833153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32694937628099191283777537 24521203221074393462833153)
        ·
          refine ⟨18390902415805795097124865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24521203221074393462833153 18390902415805795097124865)
          ·
            refine ⟨13793176811854346322843649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18390902415805795097124865 13793176811854346322843649)
            ·
              refine ⟨10344882608890759742132737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13793176811854346322843649 10344882608890759742132737)
              ·
                refine ⟨7758661956668069806599553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10344882608890759742132737 7758661956668069806599553)
                ·
                  refine ⟨5818996467501052354949665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7758661956668069806599553 5818996467501052354949665)
                  ·
                    refine ⟨4364247350625789266212249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5818996467501052354949665 4364247350625789266212249)
                    ·
                      refine ⟨3273185512969341949659187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4364247350625789266212249 3273185512969341949659187)
                      ·
                        rfl

theorem cell23_6374506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_6374506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374506 prefixEnd_6374506 := by exact prefixLift 6374506
  have htrace : WordTrace (prefixWord ++ tailWord_6374506) baseStart_6374506 baseEnd_6374506 := by
    simpa [prefixWord, tailWord_6374506, baseEnd_6374506] using wordTrace_append hprefix tailTrace_6374506
  have hstable : (prefixWord ++ tailWord_6374506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374506).length < 2 ^ (prefixWord ++ tailWord_6374506).sum := by decide
  have hdescent : baseEnd_6374506 < baseStart_6374506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374542 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_6374542 : Nat := 118140960795 + 6374542 * 2 ^ 59
def prefixEnd_6374542 : Nat := 4983230072969 + 3 ^ 40 * 6374542 * 2
def baseEnd_6374542 : Nat := 1091067999424301269603007

theorem tailTrace_6374542 : CollatzResearch.WordTrace tailWord_6374542 prefixEnd_6374542 1091067999424301269603007 := by
  unfold tailWord_6374542
  simp only [CollatzResearch.WordTrace]
  refine ⟨29062330909016311743007735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154999098181420329296041253 29062330909016311743007735)
  ·
    refine ⟨43593496363524467614511603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29062330909016311743007735 43593496363524467614511603)
    ·
      refine ⟨65390244545286701421767405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43593496363524467614511603 65390244545286701421767405)
      ·
        refine ⟨24521341704482513033162777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65390244545286701421767405 24521341704482513033162777)
        ·
          refine ⟨18391006278361884774872083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24521341704482513033162777 18391006278361884774872083)
          ·
            refine ⟨27586509417542827162308125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18391006278361884774872083 27586509417542827162308125)
            ·
              refine ⟨10344941031578560185865547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27586509417542827162308125 10344941031578560185865547)
              ·
                refine ⟨15517411547367840278798321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10344941031578560185865547 15517411547367840278798321)
                ·
                  refine ⟨11638058660525880209098741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15517411547367840278798321 11638058660525880209098741)
                  ·
                    refine ⟨1091067999424301269603007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11638058660525880209098741 1091067999424301269603007)
                    ·
                      rfl

theorem cell23_6374542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_6374542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374542 prefixEnd_6374542 := by exact prefixLift 6374542
  have htrace : WordTrace (prefixWord ++ tailWord_6374542) baseStart_6374542 baseEnd_6374542 := by
    simpa [prefixWord, tailWord_6374542, baseEnd_6374542] using wordTrace_append hprefix tailTrace_6374542
  have hstable : (prefixWord ++ tailWord_6374542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374542).length < 2 ^ (prefixWord ++ tailWord_6374542).sum := by decide
  have hdescent : baseEnd_6374542 < baseStart_6374542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374679 : List Nat := [1, 1, 3, 4, 1, 1, 4, 2, 2, 4]
def baseStart_6374679 : Nat := 118140960795 + 6374679 * 2 ^ 59
def prefixEnd_6374679 : Nat := 4983230072969 + 3 ^ 40 * 6374679 * 2
def baseEnd_6374679 : Nat := 1091091448374189924265297

theorem tailTrace_6374679 : CollatzResearch.WordTrace tailWord_6374679 prefixEnd_6374679 1091091448374189924265297 := by
  unfold tailWord_6374679
  simp only [CollatzResearch.WordTrace]
  refine ⟨232503644072634166341799091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155002429381756110894532727 232503644072634166341799091)
  ·
    refine ⟨348755466108951249512698637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232503644072634166341799091 348755466108951249512698637)
    ·
      refine ⟨130783299790856718567261989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348755466108951249512698637 130783299790856718567261989)
      ·
        refine ⟨24521868710785634731361623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130783299790856718567261989 24521868710785634731361623)
        ·
          refine ⟨36782803066178452097042435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24521868710785634731361623 36782803066178452097042435)
          ·
            refine ⟨55174204599267678145563653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36782803066178452097042435 55174204599267678145563653)
            ·
              refine ⟨10345163362362689652293185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55174204599267678145563653 10345163362362689652293185)
              ·
                refine ⟨7758872521772017239219889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10345163362362689652293185 7758872521772017239219889)
                ·
                  refine ⟨5819154391329012929414917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7758872521772017239219889 5819154391329012929414917)
                  ·
                    refine ⟨1091091448374189924265297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5819154391329012929414917 1091091448374189924265297)
                    ·
                      rfl

theorem cell23_6374679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_6374679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374679 prefixEnd_6374679 := by exact prefixLift 6374679
  have htrace : WordTrace (prefixWord ++ tailWord_6374679) baseStart_6374679 baseEnd_6374679 := by
    simpa [prefixWord, tailWord_6374679, baseEnd_6374679] using wordTrace_append hprefix tailTrace_6374679
  have hstable : (prefixWord ++ tailWord_6374679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374679).length < 2 ^ (prefixWord ++ tailWord_6374679).sum := by decide
  have hdescent : baseEnd_6374679 < baseStart_6374679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374726 : List Nat := [6, 1, 1, 3, 1, 1, 10]
def baseStart_6374726 : Nat := 118140960795 + 6374726 * 2 ^ 59
def prefixEnd_6374726 : Nat := 4983230072969 + 3 ^ 40 * 6374726 * 2
def baseEnd_6374726 : Nat := 40411092329794210974175

theorem tailTrace_6374726 : CollatzResearch.WordTrace tailWord_6374726 prefixEnd_6374726 40411092329794210974175 := by
  unfold tailWord_6374726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7265792446983246667773751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 155003572202309262245840021 7265792446983246667773751)
  ·
    refine ⟨10898688670474870001660627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7265792446983246667773751 10898688670474870001660627)
    ·
      refine ⟨16348033005712305002490941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10898688670474870001660627 16348033005712305002490941)
      ·
        refine ⟨6130512377142114375934103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16348033005712305002490941 6130512377142114375934103)
        ·
          refine ⟨9195768565713171563901155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6130512377142114375934103 9195768565713171563901155)
          ·
            refine ⟨13793652848569757345851733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9195768565713171563901155 13793652848569757345851733)
            ·
              refine ⟨40411092329794210974175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13793652848569757345851733 40411092329794210974175)
              ·
                rfl

theorem cell23_6374726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 10].length) (baseStart_6374726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374726 prefixEnd_6374726 := by exact prefixLift 6374726
  have htrace : WordTrace (prefixWord ++ tailWord_6374726) baseStart_6374726 baseEnd_6374726 := by
    simpa [prefixWord, tailWord_6374726, baseEnd_6374726] using wordTrace_append hprefix tailTrace_6374726
  have hstable : (prefixWord ++ tailWord_6374726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374726).length < 2 ^ (prefixWord ++ tailWord_6374726).sum := by decide
  have hdescent : baseEnd_6374726 < baseStart_6374726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374752 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 2, 6]
def baseStart_6374752 : Nat := 118140960795 + 6374752 * 2 ^ 59
def prefixEnd_6374752 : Nat := 4983230072969 + 3 ^ 40 * 6374752 * 2
def baseEnd_6374752 : Nat := 1091103943070115995727685

theorem tailTrace_6374752 : CollatzResearch.WordTrace tailWord_6374752 prefixEnd_6374752 1091103943070115995727685 := by
  unfold tailWord_6374752
  simp only [CollatzResearch.WordTrace]
  refine ⟨116253153300684849904603255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155004204400913133206137673 116253153300684849904603255)
  ·
    refine ⟨174379729951027274856904883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116253153300684849904603255 174379729951027274856904883)
    ·
      refine ⟨261569594926540912285357325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174379729951027274856904883 261569594926540912285357325)
      ·
        refine ⟨98088598097452842107008997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261569594926540912285357325 98088598097452842107008997)
        ·
          refine ⟨18391612143272407895064187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98088598097452842107008997 18391612143272407895064187)
          ·
            refine ⟨27587418214908611842596281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18391612143272407895064187 27587418214908611842596281)
            ·
              refine ⟨20690563661181458881947211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27587418214908611842596281 20690563661181458881947211)
              ·
                refine ⟨31035845491772188322920817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20690563661181458881947211 31035845491772188322920817)
                ·
                  refine ⟨23276884118829141242190613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31035845491772188322920817 23276884118829141242190613)
                  ·
                    refine ⟨1091103943070115995727685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23276884118829141242190613 1091103943070115995727685)
                    ·
                      rfl

theorem cell23_6374752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 2, 6].length) (baseStart_6374752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374752 prefixEnd_6374752 := by exact prefixLift 6374752
  have htrace : WordTrace (prefixWord ++ tailWord_6374752) baseStart_6374752 baseEnd_6374752 := by
    simpa [prefixWord, tailWord_6374752, baseEnd_6374752] using wordTrace_append hprefix tailTrace_6374752
  have hstable : (prefixWord ++ tailWord_6374752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374752).length < 2 ^ (prefixWord ++ tailWord_6374752).sum := by decide
  have hdescent : baseEnd_6374752 < baseStart_6374752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374869 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_6374869 : Nat := 118140960795 + 6374869 * 2 ^ 59
def prefixEnd_6374869 : Nat := 4983230072969 + 3 ^ 40 * 6374869 * 2
def baseEnd_6374869 : Nat := 3273371906446924029420017

theorem tailTrace_6374869 : CollatzResearch.WordTrace tailWord_6374869 prefixEnd_6374869 3273371906446924029420017 := by
  unfold tailWord_6374869
  simp only [CollatzResearch.WordTrace]
  refine ⟨232510573941945828791215661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155007049294630552527477107 232510573941945828791215661)
  ·
    refine ⟨87191465228229685796705873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232510573941945828791215661 87191465228229685796705873)
    ·
      refine ⟨65393598921172264347529405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87191465228229685796705873 65393598921172264347529405)
      ·
        refine ⟨24522599595439599130323527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65393598921172264347529405 24522599595439599130323527)
        ·
          refine ⟨36783899393159398695485291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24522599595439599130323527 36783899393159398695485291)
          ·
            refine ⟨55175849089739098043227937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36783899393159398695485291 55175849089739098043227937)
            ·
              refine ⟨41381886817304323532420953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55175849089739098043227937 41381886817304323532420953)
              ·
                refine ⟨31036415112978242649315715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41381886817304323532420953 31036415112978242649315715)
                ·
                  refine ⟨46554622669467363973973573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31036415112978242649315715 46554622669467363973973573)
                  ·
                    refine ⟨8728991750525130745120045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46554622669467363973973573 8728991750525130745120045)
                    ·
                      refine ⟨3273371906446924029420017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8728991750525130745120045 3273371906446924029420017)
                      ·
                        rfl

theorem cell23_6374869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_6374869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374869 prefixEnd_6374869 := by exact prefixLift 6374869
  have htrace : WordTrace (prefixWord ++ tailWord_6374869) baseStart_6374869 baseEnd_6374869 := by
    simpa [prefixWord, tailWord_6374869, baseEnd_6374869] using wordTrace_append hprefix tailTrace_6374869
  have hstable : (prefixWord ++ tailWord_6374869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374869).length < 2 ^ (prefixWord ++ tailWord_6374869).sum := by decide
  have hdescent : baseEnd_6374869 < baseStart_6374869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374910 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_6374910 : Nat := 118140960795 + 6374910 * 2 ^ 59
def prefixEnd_6374910 : Nat := 4983230072969 + 3 ^ 40 * 6374910 * 2
def baseEnd_6374910 : Nat := 1091130986384586123002443

theorem tailTrace_6374910 : CollatzResearch.WordTrace tailWord_6374910 prefixEnd_6374910 1091130986384586123002443 := by
  unfold tailWord_6374910
  simp only [CollatzResearch.WordTrace]
  refine ⟨29064008666849661599182273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155008046223198195195638789 29064008666849661599182273)
  ·
    refine ⟨21798006500137246199386705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29064008666849661599182273 21798006500137246199386705)
    ·
      refine ⟨16348504875102934649540029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21798006500137246199386705 16348504875102934649540029)
      ·
        refine ⟨6130689328163600493577511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16348504875102934649540029 6130689328163600493577511)
        ·
          refine ⟨9196033992245400740366267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6130689328163600493577511 9196033992245400740366267)
          ·
            refine ⟨13794050988368101110549401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9196033992245400740366267 13794050988368101110549401)
            ·
              refine ⟨10345538241276075832912051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13794050988368101110549401 10345538241276075832912051)
              ·
                refine ⟨15518307361914113749368077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10345538241276075832912051 15518307361914113749368077)
                ·
                  refine ⟨5819365260717792656013029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15518307361914113749368077 5819365260717792656013029)
                  ·
                    refine ⟨1091130986384586123002443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5819365260717792656013029 1091130986384586123002443)
                    ·
                      rfl

theorem cell23_6374910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_6374910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374910 prefixEnd_6374910 := by exact prefixLift 6374910
  have htrace : WordTrace (prefixWord ++ tailWord_6374910) baseStart_6374910 baseEnd_6374910 := by
    simpa [prefixWord, tailWord_6374910, baseEnd_6374910] using wordTrace_append hprefix tailTrace_6374910
  have hstable : (prefixWord ++ tailWord_6374910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374910).length < 2 ^ (prefixWord ++ tailWord_6374910).sum := by decide
  have hdescent : baseEnd_6374910 < baseStart_6374910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374969 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 6]
def baseStart_6374969 : Nat := 118140960795 + 6374969 * 2 ^ 59
def prefixEnd_6374969 : Nat := 4983230072969 + 3 ^ 40 * 6374969 * 2
def baseEnd_6374969 : Nat := 3273423254512373638169557

theorem tailTrace_6374969 : CollatzResearch.WordTrace tailWord_6374969 prefixEnd_6374969 3273423254512373638169557 := by
  unfold tailWord_6374969
  simp only [CollatzResearch.WordTrace]
  refine ⟨232514221241583545869855961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155009480827722363913237307 232514221241583545869855961)
  ·
    refine ⟨174385665931187659402391971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232514221241583545869855961 174385665931187659402391971)
    ·
      refine ⟨261578498896781489103587957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174385665931187659402391971 261578498896781489103587957)
      ·
        refine ⟨24522984271573264603461371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 261578498896781489103587957 24522984271573264603461371)
        ·
          refine ⟨36784476407359896905192057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24522984271573264603461371 36784476407359896905192057)
          ·
            refine ⟨27588357305519922678894043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36784476407359896905192057 27588357305519922678894043)
            ·
              refine ⟨41382535958279884018341065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27588357305519922678894043 41382535958279884018341065)
              ·
                refine ⟨31036901968709913013755799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41382535958279884018341065 31036901968709913013755799)
                ·
                  refine ⟨46555352953064869520633699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31036901968709913013755799 46555352953064869520633699)
                  ·
                    refine ⟨69833029429597304280950549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46555352953064869520633699 69833029429597304280950549)
                    ·
                      refine ⟨3273423254512373638169557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69833029429597304280950549 3273423254512373638169557)
                      ·
                        rfl

theorem cell23_6374969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_6374969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374969 prefixEnd_6374969 := by exact prefixLift 6374969
  have htrace : WordTrace (prefixWord ++ tailWord_6374969) baseStart_6374969 baseEnd_6374969 := by
    simpa [prefixWord, tailWord_6374969, baseEnd_6374969] using wordTrace_append hprefix tailTrace_6374969
  have hstable : (prefixWord ++ tailWord_6374969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374969).length < 2 ^ (prefixWord ++ tailWord_6374969).sum := by decide
  have hdescent : baseEnd_6374969 < baseStart_6374969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6374983 : List Nat := [1, 1, 4, 1, 5, 1, 1, 3, 2, 4]
def baseStart_6374983 : Nat := 118140960795 + 6374983 * 2 ^ 59
def prefixEnd_6374983 : Nat := 4983230072969 + 3 ^ 40 * 6374983 * 2
def baseEnd_6374983 : Nat := 1091143481080512194464831

theorem tailTrace_6374983 : CollatzResearch.WordTrace tailWord_6374983 prefixEnd_6374983 1091143481080512194464831 := by
  unfold tailWord_6374983
  simp only [CollatzResearch.WordTrace]
  refine ⟨232514731863532826260865603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155009821242355217507243735 232514731863532826260865603)
  ·
    refine ⟨348772097795299239391298405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232514731863532826260865603 348772097795299239391298405)
    ·
      refine ⟨65394768336618607385868451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348772097795299239391298405 65394768336618607385868451)
      ·
        refine ⟨98092152504927911078802677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65394768336618607385868451 98092152504927911078802677)
        ·
          refine ⟨9196139297336991663637751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98092152504927911078802677 9196139297336991663637751)
          ·
            refine ⟨13794208946005487495456627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9196139297336991663637751 13794208946005487495456627)
            ·
              refine ⟨20691313419008231243184941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13794208946005487495456627 20691313419008231243184941)
              ·
                refine ⟨7759242532128086716194353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20691313419008231243184941 7759242532128086716194353)
                ·
                  refine ⟨5819431899096065037145765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7759242532128086716194353 5819431899096065037145765)
                  ·
                    refine ⟨1091143481080512194464831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5819431899096065037145765 1091143481080512194464831)
                    ·
                      rfl

theorem cell23_6374983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_6374983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6374983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6374983 prefixEnd_6374983 := by exact prefixLift 6374983
  have htrace : WordTrace (prefixWord ++ tailWord_6374983) baseStart_6374983 baseEnd_6374983 := by
    simpa [prefixWord, tailWord_6374983, baseEnd_6374983] using wordTrace_append hprefix tailTrace_6374983
  have hstable : (prefixWord ++ tailWord_6374983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6374983).length < 2 ^ (prefixWord ++ tailWord_6374983).sum := by decide
  have hdescent : baseEnd_6374983 < baseStart_6374983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6374983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375024 : List Nat := [2, 1, 1, 1, 6, 3, 2, 2, 1, 2, 2]
def baseStart_6375024 : Nat := 118140960795 + 6375024 * 2 ^ 59
def prefixEnd_6375024 : Nat := 4983230072969 + 3 ^ 40 * 6375024 * 2
def baseEnd_6375024 : Nat := 3273451495948370922981805

theorem tailTrace_6375024 : CollatzResearch.WordTrace tailWord_6375024 prefixEnd_6375024 3273451495948370922981805 := by
  unfold tailWord_6375024
  simp only [CollatzResearch.WordTrace]
  refine ⟨116258113628192145131554063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155010818170922860175405417 116258113628192145131554063)
  ·
    refine ⟨174387170442288217697331095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116258113628192145131554063 174387170442288217697331095)
    ·
      refine ⟨261580755663432326545996643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174387170442288217697331095 261580755663432326545996643)
      ·
        refine ⟨392371133495148489818994965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261580755663432326545996643 392371133495148489818994965)
        ·
          refine ⟨18392396882585085460265389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 392371133495148489818994965 18392396882585085460265389)
          ·
            refine ⟨6897148830969407047599521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18392396882585085460265389 6897148830969407047599521)
            ·
              refine ⟨5172861623227055285699641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6897148830969407047599521 5172861623227055285699641)
              ·
                refine ⟨3879646217420291464274731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5172861623227055285699641 3879646217420291464274731)
                ·
                  refine ⟨5819469326130437196412097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3879646217420291464274731 5819469326130437196412097)
                  ·
                    refine ⟨4364601994597827897309073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5819469326130437196412097 4364601994597827897309073)
                    ·
                      refine ⟨3273451495948370922981805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4364601994597827897309073 3273451495948370922981805)
                      ·
                        rfl

theorem cell23_6375024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 1, 2, 2].length) (baseStart_6375024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375024 prefixEnd_6375024 := by exact prefixLift 6375024
  have htrace : WordTrace (prefixWord ++ tailWord_6375024) baseStart_6375024 baseEnd_6375024 := by
    simpa [prefixWord, tailWord_6375024, baseEnd_6375024] using wordTrace_append hprefix tailTrace_6375024
  have hstable : (prefixWord ++ tailWord_6375024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375024).length < 2 ^ (prefixWord ++ tailWord_6375024).sum := by decide
  have hdescent : baseEnd_6375024 < baseStart_6375024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375049 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 4, 1, 5]
def baseStart_6375049 : Nat := 118140960795 + 6375049 * 2 ^ 59
def prefixEnd_6375049 : Nat := 4983230072969 + 3 ^ 40 * 6375049 * 2
def baseEnd_6375049 : Nat := 3273464332964733325169189

theorem tailTrace_6375049 : CollatzResearch.WordTrace tailWord_6375049 prefixEnd_6375049 3273464332964733325169189 := by
  unfold tailWord_6375049
  simp only [CollatzResearch.WordTrace]
  refine ⟨232517139081293719532768201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155011426054195813021845467 232517139081293719532768201)
  ·
    refine ⟨174387854310970289649576151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232517139081293719532768201 174387854310970289649576151)
    ·
      refine ⟨261581781466455434474364227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174387854310970289649576151 261581781466455434474364227)
      ·
        refine ⟨392372672199683151711546341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261581781466455434474364227 392372672199683151711546341)
        ·
          refine ⟨73569876037440590945914939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 392372672199683151711546341 73569876037440590945914939)
          ·
            refine ⟨110354814056160886418872409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73569876037440590945914939 110354814056160886418872409)
            ·
              refine ⟨82766110542120664814154307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110354814056160886418872409 82766110542120664814154307)
              ·
                refine ⟨124149165813180997221231461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82766110542120664814154307 124149165813180997221231461)
                ·
                  refine ⟨23277968589971436978980899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124149165813180997221231461 23277968589971436978980899)
                  ·
                    refine ⟨34916952884957155468471349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23277968589971436978980899 34916952884957155468471349)
                    ·
                      refine ⟨3273464332964733325169189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34916952884957155468471349 3273464332964733325169189)
                      ·
                        rfl

theorem cell23_6375049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_6375049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375049 prefixEnd_6375049 := by exact prefixLift 6375049
  have htrace : WordTrace (prefixWord ++ tailWord_6375049) baseStart_6375049 baseEnd_6375049 := by
    simpa [prefixWord, tailWord_6375049, baseEnd_6375049] using wordTrace_append hprefix tailTrace_6375049
  have hstable : (prefixWord ++ tailWord_6375049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375049).length < 2 ^ (prefixWord ++ tailWord_6375049).sum := by decide
  have hdescent : baseEnd_6375049 < baseStart_6375049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375059 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 4]
def baseStart_6375059 : Nat := 118140960795 + 6375059 * 2 ^ 59
def prefixEnd_6375059 : Nat := 4983230072969 + 3 ^ 40 * 6375059 * 2
def baseEnd_6375059 : Nat := 3273469467771278286044143

theorem tailTrace_6375059 : CollatzResearch.WordTrace tailWord_6375059 prefixEnd_6375059 3273469467771278286044143 := by
  unfold tailWord_6375059
  simp only [CollatzResearch.WordTrace]
  refine ⟨232517503811257491240632231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155011669207504994160421487 232517503811257491240632231)
  ·
    refine ⟨348776255716886236860948347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232517503811257491240632231 348776255716886236860948347)
    ·
      refine ⟨523164383575329355291422521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348776255716886236860948347 523164383575329355291422521)
      ·
        refine ⟨392373287681497016468566891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523164383575329355291422521 392373287681497016468566891)
        ·
          refine ⟨588559931522245524702850337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392373287681497016468566891 588559931522245524702850337)
          ·
            refine ⟨441419948641684143527137753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588559931522245524702850337 441419948641684143527137753)
            ·
              refine ⟨331064961481263107645353315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441419948641684143527137753 331064961481263107645353315)
              ·
                refine ⟨496597442221894661468029973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331064961481263107645353315 496597442221894661468029973)
                ·
                  refine ⟨23278005104151312256313905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 496597442221894661468029973 23278005104151312256313905)
                  ·
                    refine ⟨17458503828113484192235429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23278005104151312256313905 17458503828113484192235429)
                    ·
                      refine ⟨3273469467771278286044143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17458503828113484192235429 3273469467771278286044143)
                      ·
                        rfl

theorem cell23_6375059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_6375059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375059 prefixEnd_6375059 := by exact prefixLift 6375059
  have htrace : WordTrace (prefixWord ++ tailWord_6375059) baseStart_6375059 baseEnd_6375059 := by
    simpa [prefixWord, tailWord_6375059, baseEnd_6375059] using wordTrace_append hprefix tailTrace_6375059
  have hstable : (prefixWord ++ tailWord_6375059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375059).length < 2 ^ (prefixWord ++ tailWord_6375059).sum := by decide
  have hdescent : baseEnd_6375059 < baseStart_6375059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375063 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 1, 4, 2]
def baseStart_6375063 : Nat := 118140960795 + 6375063 * 2 ^ 59
def prefixEnd_6375063 : Nat := 4983230072969 + 3 ^ 40 * 6375063 * 2
def baseEnd_6375063 : Nat := 3273471521693896270394125

theorem tailTrace_6375063 : CollatzResearch.WordTrace tailWord_6375063 prefixEnd_6375063 3273471521693896270394125 := by
  unfold tailWord_6375063
  simp only [CollatzResearch.WordTrace]
  refine ⟨232517649703242999923777843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155011766468828666615851895 232517649703242999923777843)
  ·
    refine ⟨348776474554864499885666765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232517649703242999923777843 348776474554864499885666765)
    ·
      refine ⟨130791177958074187457125037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348776474554864499885666765 130791177958074187457125037)
      ·
        refine ⟨49046691734277820296421889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130791177958074187457125037 49046691734277820296421889)
        ·
          refine ⟨36785018800708365222316417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49046691734277820296421889 36785018800708365222316417)
          ·
            refine ⟨27588764100531273916737313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36785018800708365222316417 27588764100531273916737313)
            ·
              refine ⟨20691573075398455437552985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27588764100531273916737313 20691573075398455437552985)
              ·
                refine ⟨15518679806548841578164739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20691573075398455437552985 15518679806548841578164739)
                ·
                  refine ⟨23278019709823262367247109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15518679806548841578164739 23278019709823262367247109)
                  ·
                    refine ⟨4364628695591861693858833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23278019709823262367247109 4364628695591861693858833)
                    ·
                      refine ⟨3273471521693896270394125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4364628695591861693858833 3273471521693896270394125)
                      ·
                        rfl

theorem cell23_6375063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_6375063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375063 prefixEnd_6375063 := by exact prefixLift 6375063
  have htrace : WordTrace (prefixWord ++ tailWord_6375063) baseStart_6375063 baseEnd_6375063 := by
    simpa [prefixWord, tailWord_6375063, baseEnd_6375063] using wordTrace_append hprefix tailTrace_6375063
  have hstable : (prefixWord ++ tailWord_6375063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375063).length < 2 ^ (prefixWord ++ tailWord_6375063).sum := by decide
  have hdescent : baseEnd_6375063 < baseStart_6375063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375069 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 11]
def baseStart_6375069 : Nat := 118140960795 + 6375069 * 2 ^ 59
def prefixEnd_6375069 : Nat := 4983230072969 + 3 ^ 40 * 6375069 * 2
def baseEnd_6375069 : Nat := 363719400286424805213233

theorem tailTrace_6375069 : CollatzResearch.WordTrace tailWord_6375069 prefixEnd_6375069 363719400286424805213233 := by
  unfold tailWord_6375069
  simp only [CollatzResearch.WordTrace]
  refine ⟨232517868541221262948496261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155011912360814175298997507 232517868541221262948496261)
  ·
    refine ⟨43597100351478986802843049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232517868541221262948496261 43597100351478986802843049)
    ·
      refine ⟨32697825263609240102132287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43597100351478986802843049 32697825263609240102132287)
      ·
        refine ⟨49046737895413860153198431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32697825263609240102132287 49046737895413860153198431)
        ·
          refine ⟨73570106843120790229797647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49046737895413860153198431 73570106843120790229797647)
          ·
            refine ⟨110355160264681185344696471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73570106843120790229797647 110355160264681185344696471)
            ·
              refine ⟨165532740397021778017044707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110355160264681185344696471 165532740397021778017044707)
              ·
                refine ⟨248299110595532667025567061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165532740397021778017044707 248299110595532667025567061)
                ·
                  refine ⟨363719400286424805213233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 248299110595532667025567061 363719400286424805213233)
                  ·
                    rfl

theorem cell23_6375069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_6375069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375069 prefixEnd_6375069 := by exact prefixLift 6375069
  have htrace : WordTrace (prefixWord ++ tailWord_6375069) baseStart_6375069 baseEnd_6375069 := by
    simpa [prefixWord, tailWord_6375069, baseEnd_6375069] using wordTrace_append hprefix tailTrace_6375069
  have hstable : (prefixWord ++ tailWord_6375069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375069).length < 2 ^ (prefixWord ++ tailWord_6375069).sum := by decide
  have hdescent : baseEnd_6375069 < baseStart_6375069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375074 : List Nat := [3, 3, 1, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_6375074 : Nat := 118140960795 + 6375074 * 2 ^ 59
def prefixEnd_6375074 : Nat := 4983230072969 + 3 ^ 40 * 6375074 * 2
def baseEnd_6375074 : Nat := 3273477169981095727356575

theorem tailTrace_6375074 : CollatzResearch.WordTrace tailWord_6375074 prefixEnd_6375074 3273477169981095727356575 := by
  unfold tailWord_6375074
  simp only [CollatzResearch.WordTrace]
  refine ⟨58129512726550787200607069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155012033937468765868285517 58129512726550787200607069)
  ·
    refine ⟨21798567272456545200227651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58129512726550787200607069 21798567272456545200227651)
    ·
      refine ⟨32697850908684817800341477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21798567272456545200227651 32697850908684817800341477)
      ·
        refine ⟨6130847045378403337564027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32697850908684817800341477 6130847045378403337564027)
        ·
          refine ⟨9196270568067605006346041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6130847045378403337564027 9196270568067605006346041)
          ·
            refine ⟨6897202926050703754759531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9196270568067605006346041 6897202926050703754759531)
            ·
              refine ⟨10345804389076055632139297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6897202926050703754759531 10345804389076055632139297)
              ·
                refine ⟨7759353291807041724104473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10345804389076055632139297 7759353291807041724104473)
                ·
                  refine ⟨5819514968855281293078355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7759353291807041724104473 5819514968855281293078355)
                  ·
                    refine ⟨8729272453282921939617533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5819514968855281293078355 8729272453282921939617533)
                    ·
                      refine ⟨3273477169981095727356575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8729272453282921939617533 3273477169981095727356575)
                      ·
                        rfl

theorem cell23_6375074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_6375074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375074 prefixEnd_6375074 := by exact prefixLift 6375074
  have htrace : WordTrace (prefixWord ++ tailWord_6375074) baseStart_6375074 baseEnd_6375074 := by
    simpa [prefixWord, tailWord_6375074, baseEnd_6375074] using wordTrace_append hprefix tailTrace_6375074
  have hstable : (prefixWord ++ tailWord_6375074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375074).length < 2 ^ (prefixWord ++ tailWord_6375074).sum := by decide
  have hdescent : baseEnd_6375074 < baseStart_6375074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375076 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_6375076 : Nat := 118140960795 + 6375076 * 2 ^ 59
def prefixEnd_6375076 : Nat := 4983230072969 + 3 ^ 40 * 6375076 * 2
def baseEnd_6375076 : Nat := 3273478196942404719531565

theorem tailTrace_6375076 : CollatzResearch.WordTrace tailWord_6375076 prefixEnd_6375076 3273478196942404719531565 := by
  unfold tailWord_6375076
  simp only [CollatzResearch.WordTrace]
  refine ⟨116259061926097951572000541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155012082568130602096000721 116259061926097951572000541)
  ·
    refine ⟨43597148222286731839500203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116259061926097951572000541 43597148222286731839500203)
    ·
      refine ⟨65395722333430097759250305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43597148222286731839500203 65395722333430097759250305)
      ·
        refine ⟨49046791750072573319437729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65395722333430097759250305 49046791750072573319437729)
        ·
          refine ⟨36785093812554429989578297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49046791750072573319437729 36785093812554429989578297)
          ·
            refine ⟨27588820359415822492183723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36785093812554429989578297 27588820359415822492183723)
            ·
              refine ⟨41383230539123733738275585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27588820359415822492183723 41383230539123733738275585)
              ·
                refine ⟨31037422904342800303706689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41383230539123733738275585 31037422904342800303706689)
                ·
                  refine ⟨23278067178257100227780017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31037422904342800303706689 23278067178257100227780017)
                  ·
                    refine ⟨17458550383692825170835013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23278067178257100227780017 17458550383692825170835013)
                    ·
                      refine ⟨3273478196942404719531565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17458550383692825170835013 3273478196942404719531565)
                      ·
                        rfl

theorem cell23_6375076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_6375076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375076 prefixEnd_6375076 := by exact prefixLift 6375076
  have htrace : WordTrace (prefixWord ++ tailWord_6375076) baseStart_6375076 baseEnd_6375076 := by
    simpa [prefixWord, tailWord_6375076, baseEnd_6375076] using wordTrace_append hprefix tailTrace_6375076
  have hstable : (prefixWord ++ tailWord_6375076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375076).length < 2 ^ (prefixWord ++ tailWord_6375076).sum := by decide
  have hdescent : baseEnd_6375076 < baseStart_6375076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375109 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_6375109 : Nat := 118140960795 + 6375109 * 2 ^ 59
def prefixEnd_6375109 : Nat := 4983230072969 + 3 ^ 40 * 6375109 * 2
def baseEnd_6375109 : Nat := 3273495141804003090418913

theorem tailTrace_6375109 : CollatzResearch.WordTrace tailWord_6375109 prefixEnd_6375109 3273495141804003090418913 := by
  unfold tailWord_6375109
  simp only [CollatzResearch.WordTrace]
  refine ⟨232519327461076349779952381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155012884974050899853301587 232519327461076349779952381)
  ·
    refine ⟨87194747797903631167482143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232519327461076349779952381 87194747797903631167482143)
    ·
      refine ⟨130792121696855446751223215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87194747797903631167482143 130792121696855446751223215)
      ·
        refine ⟨196188182545283170126834823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130792121696855446751223215 196188182545283170126834823)
        ·
          refine ⟨294282273817924755190252235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196188182545283170126834823 294282273817924755190252235)
          ·
            refine ⟨441423410726887132785378353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294282273817924755190252235 441423410726887132785378353)
            ·
              refine ⟨331067558045165349589033765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441423410726887132785378353 331067558045165349589033765)
              ·
                refine ⟨62075167133468503047943831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331067558045165349589033765 62075167133468503047943831)
                ·
                  refine ⟨93112750700202754571915747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62075167133468503047943831 93112750700202754571915747)
                  ·
                    refine ⟨139669126050304131857873621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93112750700202754571915747 139669126050304131857873621)
                    ·
                      refine ⟨3273495141804003090418913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139669126050304131857873621 3273495141804003090418913)
                      ·
                        rfl

theorem cell23_6375109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_6375109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375109 prefixEnd_6375109 := by exact prefixLift 6375109
  have htrace : WordTrace (prefixWord ++ tailWord_6375109) baseStart_6375109 baseEnd_6375109 := by
    simpa [prefixWord, tailWord_6375109, baseEnd_6375109] using wordTrace_append hprefix tailTrace_6375109
  have hstable : (prefixWord ++ tailWord_6375109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375109).length < 2 ^ (prefixWord ++ tailWord_6375109).sum := by decide
  have hdescent : baseEnd_6375109 < baseStart_6375109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375136 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 4]
def baseStart_6375136 : Nat := 118140960795 + 6375136 * 2 ^ 59
def prefixEnd_6375136 : Nat := 4983230072969 + 3 ^ 40 * 6375136 * 2
def baseEnd_6375136 : Nat := 3273509005781674484781289

theorem tailTrace_6375136 : CollatzResearch.WordTrace tailWord_6375136 prefixEnd_6375136 3273509005781674484781289 := by
  unfold tailWord_6375136
  simp only [CollatzResearch.WordTrace]
  refine ⟨116260156115989266695592631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155013541487985688927456841 116260156115989266695592631)
  ·
    refine ⟨174390234173983900043388947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116260156115989266695592631 174390234173983900043388947)
    ·
      refine ⟨261585351260975850065083421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174390234173983900043388947 261585351260975850065083421)
      ·
        refine ⟨98094506722865943774406283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261585351260975850065083421 98094506722865943774406283)
        ·
          refine ⟨147141760084298915661609425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98094506722865943774406283 147141760084298915661609425)
          ·
            refine ⟨110356320063224186746207069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147141760084298915661609425 110356320063224186746207069)
            ·
              refine ⟨41383620023709070029827651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110356320063224186746207069 41383620023709070029827651)
              ·
                refine ⟨62075430035563605044741477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41383620023709070029827651 62075430035563605044741477)
                ·
                  refine ⟨11639143131668175945889027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62075430035563605044741477 11639143131668175945889027)
                  ·
                    refine ⟨17458714697502263918833541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11639143131668175945889027 17458714697502263918833541)
                    ·
                      refine ⟨3273509005781674484781289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17458714697502263918833541 3273509005781674484781289)
                      ·
                        rfl

theorem cell23_6375136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_6375136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375136 prefixEnd_6375136 := by exact prefixLift 6375136
  have htrace : WordTrace (prefixWord ++ tailWord_6375136) baseStart_6375136 baseEnd_6375136 := by
    simpa [prefixWord, tailWord_6375136, baseEnd_6375136] using wordTrace_append hprefix tailTrace_6375136
  have hstable : (prefixWord ++ tailWord_6375136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375136).length < 2 ^ (prefixWord ++ tailWord_6375136).sum := by decide
  have hdescent : baseEnd_6375136 < baseStart_6375136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375170 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_6375170 : Nat := 118140960795 + 6375170 * 2 ^ 59
def prefixEnd_6375170 : Nat := 4983230072969 + 3 ^ 40 * 6375170 * 2
def baseEnd_6375170 : Nat := 3273526464123927351756133

theorem tailTrace_6375170 : CollatzResearch.WordTrace tailWord_6375170 prefixEnd_6375170 3273526464123927351756133 := by
  unfold tailWord_6375170
  simp only [CollatzResearch.WordTrace]
  refine ⟨58130388078463839299480741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155014368209236904798615309 58130388078463839299480741)
  ·
    refine ⟨10899447764711969868652639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58130388078463839299480741 10899447764711969868652639)
    ·
      refine ⟨16349171647067954802978959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10899447764711969868652639 16349171647067954802978959)
      ·
        refine ⟨24523757470601932204468439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16349171647067954802978959 24523757470601932204468439)
        ·
          refine ⟨36785636205902898306702659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24523757470601932204468439 36785636205902898306702659)
          ·
            refine ⟨55178454308854347460053989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36785636205902898306702659 55178454308854347460053989)
            ·
              refine ⟨10345960182910190148760123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55178454308854347460053989 10345960182910190148760123)
              ·
                refine ⟨15518940274365285223140185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10345960182910190148760123 15518940274365285223140185)
                ·
                  refine ⟨11639205205773963917355139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15518940274365285223140185 11639205205773963917355139)
                  ·
                    refine ⟨17458807808660945876032709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11639205205773963917355139 17458807808660945876032709)
                    ·
                      refine ⟨3273526464123927351756133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17458807808660945876032709 3273526464123927351756133)
                      ·
                        rfl

theorem cell23_6375170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_6375170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375170 prefixEnd_6375170 := by exact prefixLift 6375170
  have htrace : WordTrace (prefixWord ++ tailWord_6375170) baseStart_6375170 baseEnd_6375170 := by
    simpa [prefixWord, tailWord_6375170, baseEnd_6375170] using wordTrace_append hprefix tailTrace_6375170
  have hstable : (prefixWord ++ tailWord_6375170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375170).length < 2 ^ (prefixWord ++ tailWord_6375170).sum := by decide
  have hdescent : baseEnd_6375170 < baseStart_6375170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375188 : List Nat := [2, 4, 4, 1, 2, 1, 2, 2, 5]
def baseStart_6375188 : Nat := 118140960795 + 6375188 * 2 ^ 59
def prefixEnd_6375188 : Nat := 4983230072969 + 3 ^ 40 * 6375188 * 2
def baseEnd_6375188 : Nat := 363726189641745364592339

theorem tailTrace_6375188 : CollatzResearch.WordTrace tailWord_6375188 prefixEnd_6375188 363726189641745364592339 := by
  unfold tailWord_6375188
  simp only [CollatzResearch.WordTrace]
  refine ⟨116261104413895073136039109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155014805885193430848052145 116261104413895073136039109)
  ·
    refine ⟨21798957077605326213007333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116261104413895073136039109 21798957077605326213007333)
    ·
      refine ⟨4087304452050998664938875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21798957077605326213007333 4087304452050998664938875)
      ·
        refine ⟨6130956678076497997408313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4087304452050998664938875 6130956678076497997408313)
        ·
          refine ⟨4598217508557373498056235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6130956678076497997408313 4598217508557373498056235)
          ·
            refine ⟨6897326262836060247084353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4598217508557373498056235 6897326262836060247084353)
            ·
              refine ⟨5172994697127045185313265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6897326262836060247084353 5172994697127045185313265)
              ·
                refine ⟨3879746022845283888984949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5172994697127045185313265 3879746022845283888984949)
                ·
                  refine ⟨363726189641745364592339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3879746022845283888984949 363726189641745364592339)
                  ·
                    rfl

theorem cell23_6375188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_6375188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375188 prefixEnd_6375188 := by exact prefixLift 6375188
  have htrace : WordTrace (prefixWord ++ tailWord_6375188) baseStart_6375188 baseEnd_6375188 := by
    simpa [prefixWord, tailWord_6375188, baseEnd_6375188] using wordTrace_append hprefix tailTrace_6375188
  have hstable : (prefixWord ++ tailWord_6375188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375188).length < 2 ^ (prefixWord ++ tailWord_6375188).sum := by decide
  have hdescent : baseEnd_6375188 < baseStart_6375188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375196 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_6375196 : Nat := 118140960795 + 6375196 * 2 ^ 59
def prefixEnd_6375196 : Nat := 4983230072969 + 3 ^ 40 * 6375196 * 2
def baseEnd_6375196 : Nat := 3273539814620944250031013

theorem tailTrace_6375196 : CollatzResearch.WordTrace tailWord_6375196 prefixEnd_6375196 3273539814620944250031013 := by
  unfold tailWord_6375196
  simp only [CollatzResearch.WordTrace]
  refine ⟨116261250305880581819184721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155015000407840775758912961 116261250305880581819184721)
  ·
    refine ⟨87195937729410436364388541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116261250305880581819184721 87195937729410436364388541)
    ·
      refine ⟨32698476648528913636645703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87195937729410436364388541 32698476648528913636645703)
      ·
        refine ⟨49047714972793370454968555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32698476648528913636645703 49047714972793370454968555)
        ·
          refine ⟨73571572459190055682452833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49047714972793370454968555 73571572459190055682452833)
          ·
            refine ⟨55178679344392541761839625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73571572459190055682452833 55178679344392541761839625)
            ·
              refine ⟨41384009508294406321379719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55178679344392541761839625 41384009508294406321379719)
              ·
                refine ⟨62076014262441609482069579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41384009508294406321379719 62076014262441609482069579)
                ·
                  refine ⟨93114021393662414223104369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62076014262441609482069579 93114021393662414223104369)
                  ·
                    refine ⟨69835516045246810667328277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93114021393662414223104369 69835516045246810667328277)
                    ·
                      refine ⟨3273539814620944250031013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69835516045246810667328277 3273539814620944250031013)
                      ·
                        rfl

theorem cell23_6375196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_6375196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375196 prefixEnd_6375196 := by exact prefixLift 6375196
  have htrace : WordTrace (prefixWord ++ tailWord_6375196) baseStart_6375196 baseEnd_6375196 := by
    simpa [prefixWord, tailWord_6375196, baseEnd_6375196] using wordTrace_append hprefix tailTrace_6375196
  have hstable : (prefixWord ++ tailWord_6375196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375196).length < 2 ^ (prefixWord ++ tailWord_6375196).sum := by decide
  have hdescent : baseEnd_6375196 < baseStart_6375196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375237 : List Nat := [1, 3, 1, 1, 1, 2, 6, 3, 1, 1, 3]
def baseStart_6375237 : Nat := 118140960795 + 6375237 * 2 ^ 59
def prefixEnd_6375237 : Nat := 4983230072969 + 3 ^ 40 * 6375237 * 2
def baseEnd_6375237 : Nat := 3273560867327778589618325

theorem tailTrace_6375237 : CollatzResearch.WordTrace tailWord_6375237 prefixEnd_6375237 3273560867327778589618325 := by
  unfold tailWord_6375237
  simp only [CollatzResearch.WordTrace]
  refine ⟨232523996004612627640611965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155015997336408418427074643 232523996004612627640611965)
  ·
    refine ⟨87196498501729735365229487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232523996004612627640611965 87196498501729735365229487)
    ·
      refine ⟨130794747752594603047844231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87196498501729735365229487 130794747752594603047844231)
      ·
        refine ⟨196192121628891904571766347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130794747752594603047844231 196192121628891904571766347)
        ·
          refine ⟨294288182443337856857649521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196192121628891904571766347 294288182443337856857649521)
          ·
            refine ⟨220716136832503392643237141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294288182443337856857649521 220716136832503392643237141)
            ·
              refine ⟨10346068914023596530151741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220716136832503392643237141 10346068914023596530151741)
              ·
                refine ⟨3879775842758848698806903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10346068914023596530151741 3879775842758848698806903)
                ·
                  refine ⟨5819663764138273048210355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3879775842758848698806903 5819663764138273048210355)
                  ·
                    refine ⟨8729495646207409572315533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5819663764138273048210355 8729495646207409572315533)
                    ·
                      refine ⟨3273560867327778589618325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8729495646207409572315533 3273560867327778589618325)
                      ·
                        rfl

theorem cell23_6375237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 1, 1, 3].length) (baseStart_6375237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375237 prefixEnd_6375237 := by exact prefixLift 6375237
  have htrace : WordTrace (prefixWord ++ tailWord_6375237) baseStart_6375237 baseEnd_6375237 := by
    simpa [prefixWord, tailWord_6375237, baseEnd_6375237] using wordTrace_append hprefix tailTrace_6375237
  have hstable : (prefixWord ++ tailWord_6375237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375237).length < 2 ^ (prefixWord ++ tailWord_6375237).sum := by decide
  have hdescent : baseEnd_6375237 < baseStart_6375237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375240 : List Nat := [2, 1, 3, 1, 1, 4, 4, 1, 1, 5]
def baseStart_6375240 : Nat := 118140960795 + 6375240 * 2 ^ 59
def prefixEnd_6375240 : Nat := 4983230072969 + 3 ^ 40 * 6375240 * 2
def baseEnd_6375240 : Nat := 1091187469256580692626937

theorem tailTrace_6375240 : CollatzResearch.WordTrace tailWord_6375240 prefixEnd_6375240 1091187469256580692626937 := by
  unfold tailWord_6375240
  simp only [CollatzResearch.WordTrace]
  refine ⟨116262052711800879576485587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155016070282401172768647449 116262052711800879576485587)
  ·
    refine ⟨174393079067701319364728381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116262052711800879576485587 174393079067701319364728381)
    ·
      refine ⟨65397404650387994761773143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174393079067701319364728381 65397404650387994761773143)
      ·
        refine ⟨98096106975581992142659715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65397404650387994761773143 98096106975581992142659715)
        ·
          refine ⟨147144160463372988213989573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98096106975581992142659715 147144160463372988213989573)
          ·
            refine ⟨27589530086882435290123045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147144160463372988213989573 27589530086882435290123045)
            ·
              refine ⟨5173036891290456616898071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27589530086882435290123045 5173036891290456616898071)
              ·
                refine ⟨7759555336935684925347107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5173036891290456616898071 7759555336935684925347107)
                ·
                  refine ⟨11639333005403527388020661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7759555336935684925347107 11639333005403527388020661)
                  ·
                    refine ⟨1091187469256580692626937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11639333005403527388020661 1091187469256580692626937)
                    ·
                      rfl

theorem cell23_6375240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_6375240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375240 prefixEnd_6375240 := by exact prefixLift 6375240
  have htrace : WordTrace (prefixWord ++ tailWord_6375240) baseStart_6375240 baseEnd_6375240 := by
    simpa [prefixWord, tailWord_6375240, baseEnd_6375240] using wordTrace_append hprefix tailTrace_6375240
  have hstable : (prefixWord ++ tailWord_6375240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375240).length < 2 ^ (prefixWord ++ tailWord_6375240).sum := by decide
  have hdescent : baseEnd_6375240 < baseStart_6375240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375256 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_6375256 : Nat := 118140960795 + 6375256 * 2 ^ 59
def prefixEnd_6375256 : Nat := 4983230072969 + 3 ^ 40 * 6375256 * 2
def baseEnd_6375256 : Nat := 3273570623460214015280737

theorem tailTrace_6375256 : CollatzResearch.WordTrace tailWord_6375256 prefixEnd_6375256 3273570623460214015280737 := by
  unfold tailWord_6375256
  simp only [CollatzResearch.WordTrace]
  refine ⟨116262344495771896942776811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155016459327695862590369081 116262344495771896942776811)
  ·
    refine ⟨174393516743657845414165217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116262344495771896942776811 174393516743657845414165217)
    ·
      refine ⟨130795137557743384060623913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174393516743657845414165217 130795137557743384060623913)
      ·
        refine ⟨98096353168307538045467935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130795137557743384060623913 98096353168307538045467935)
        ·
          refine ⟨147144529752461307068201903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98096353168307538045467935 147144529752461307068201903)
          ·
            refine ⟨220716794628691960602302855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147144529752461307068201903 220716794628691960602302855)
            ·
              refine ⟨331075191943037940903454283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220716794628691960602302855 331075191943037940903454283)
              ·
                refine ⟨496612787914556911355181425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331075191943037940903454283 496612787914556911355181425)
                ·
                  refine ⟨372459590935917683516386069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496612787914556911355181425 372459590935917683516386069)
                  ·
                    refine ⟨17459043325121141414830597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 372459590935917683516386069 17459043325121141414830597)
                    ·
                      refine ⟨3273570623460214015280737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17459043325121141414830597 3273570623460214015280737)
                      ·
                        rfl

theorem cell23_6375256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_6375256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375256 prefixEnd_6375256 := by exact prefixLift 6375256
  have htrace : WordTrace (prefixWord ++ tailWord_6375256) baseStart_6375256 baseEnd_6375256 := by
    simpa [prefixWord, tailWord_6375256, baseEnd_6375256] using wordTrace_append hprefix tailTrace_6375256
  have hstable : (prefixWord ++ tailWord_6375256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375256).length < 2 ^ (prefixWord ++ tailWord_6375256).sum := by decide
  have hdescent : baseEnd_6375256 < baseStart_6375256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375263 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 5]
def baseStart_6375263 : Nat := 118140960795 + 6375263 * 2 ^ 59
def prefixEnd_6375263 : Nat := 4983230072969 + 3 ^ 40 * 6375263 * 2
def baseEnd_6375263 : Nat := 3273574217824795487893205

theorem tailTrace_6375263 : CollatzResearch.WordTrace tailWord_6375263 prefixEnd_6375263 3273574217824795487893205 := by
  unfold tailWord_6375263
  simp only [CollatzResearch.WordTrace]
  refine ⟨232524944302518434081058443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155016629535012289387372295 232524944302518434081058443)
  ·
    refine ⟨348787416453777651121587665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232524944302518434081058443 348787416453777651121587665)
    ·
      refine ⟨261590562340333238341190749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348787416453777651121587665 261590562340333238341190749)
      ·
        refine ⟨98096460877624964377946531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261590562340333238341190749 98096460877624964377946531)
        ·
          refine ⟨147144691316437446566919797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98096460877624964377946531 147144691316437446566919797)
          ·
            refine ⟨13794814810916010615648731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147144691316437446566919797 13794814810916010615648731)
            ·
              refine ⟨20692222216374015923473097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13794814810916010615648731 20692222216374015923473097)
              ·
                refine ⟨15519166662280511942604823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20692222216374015923473097 15519166662280511942604823)
                ·
                  refine ⟨23278749993420767913907235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15519166662280511942604823 23278749993420767913907235)
                  ·
                    refine ⟨34918124990131151870860853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23278749993420767913907235 34918124990131151870860853)
                    ·
                      refine ⟨3273574217824795487893205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34918124990131151870860853 3273574217824795487893205)
                      ·
                        rfl

theorem cell23_6375263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_6375263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375263 prefixEnd_6375263 := by exact prefixLift 6375263
  have htrace : WordTrace (prefixWord ++ tailWord_6375263) baseStart_6375263 baseEnd_6375263 := by
    simpa [prefixWord, tailWord_6375263, baseEnd_6375263] using wordTrace_append hprefix tailTrace_6375263
  have hstable : (prefixWord ++ tailWord_6375263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375263).length < 2 ^ (prefixWord ++ tailWord_6375263).sum := by decide
  have hdescent : baseEnd_6375263 < baseStart_6375263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375277 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_6375277 : Nat := 118140960795 + 6375277 * 2 ^ 59
def prefixEnd_6375277 : Nat := 4983230072969 + 3 ^ 40 * 6375277 * 2
def baseEnd_6375277 : Nat := 3273581406553958433118141

theorem tailTrace_6375277 : CollatzResearch.WordTrace tailWord_6375277 prefixEnd_6375277 3273581406553958433118141 := by
  unfold tailWord_6375277
  simp only [CollatzResearch.WordTrace]
  refine ⟨232525454924467714472068085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155016969949645142981378723 232525454924467714472068085)
  ·
    refine ⟨21799261399168848231756383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232525454924467714472068085 21799261399168848231756383)
    ·
      refine ⟨32698892098753272347634575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21799261399168848231756383 32698892098753272347634575)
      ·
        refine ⟨49048338148129908521451863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32698892098753272347634575 49048338148129908521451863)
        ·
          refine ⟨73572507222194862782177795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49048338148129908521451863 73572507222194862782177795)
          ·
            refine ⟨110358760833292294173266693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73572507222194862782177795 110358760833292294173266693)
            ·
              refine ⟨20692267656242305157487505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110358760833292294173266693 20692267656242305157487505)
              ·
                refine ⟨15519200742181728868115629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20692267656242305157487505 15519200742181728868115629)
                ·
                  refine ⟨5819700278318148325543361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15519200742181728868115629 5819700278318148325543361)
                  ·
                    refine ⟨4364775208738611244157521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5819700278318148325543361 4364775208738611244157521)
                    ·
                      refine ⟨3273581406553958433118141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4364775208738611244157521 3273581406553958433118141)
                      ·
                        rfl

theorem cell23_6375277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_6375277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375277 prefixEnd_6375277 := by exact prefixLift 6375277
  have htrace : WordTrace (prefixWord ++ tailWord_6375277) baseStart_6375277 baseEnd_6375277 := by
    simpa [prefixWord, tailWord_6375277, baseEnd_6375277] using wordTrace_append hprefix tailTrace_6375277
  have hstable : (prefixWord ++ tailWord_6375277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375277).length < 2 ^ (prefixWord ++ tailWord_6375277).sum := by decide
  have hdescent : baseEnd_6375277 < baseStart_6375277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375293 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_6375293 : Nat := 118140960795 + 6375293 * 2 ^ 59
def prefixEnd_6375293 : Nat := 4983230072969 + 3 ^ 40 * 6375293 * 2
def baseEnd_6375293 : Nat := 3273589622244430370518067

theorem tailTrace_6375293 : CollatzResearch.WordTrace tailWord_6375293 prefixEnd_6375293 3273589622244430370518067 := by
  unfold tailWord_6375293
  simp only [CollatzResearch.WordTrace]
  refine ⟨232526038492409749204650533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155017358994939832803100355 232526038492409749204650533)
  ·
    refine ⟨43598632217326827975871975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232526038492409749204650533 43598632217326827975871975)
    ·
      refine ⟨65397948325990241963807963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43598632217326827975871975 65397948325990241963807963)
      ·
        refine ⟨98096922488985362945711945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65397948325990241963807963 98096922488985362945711945)
        ·
          refine ⟨73572691866739022209283959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98096922488985362945711945 73572691866739022209283959)
          ·
            refine ⟨110359037800108533313925939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73572691866739022209283959 110359037800108533313925939)
            ·
              refine ⟨165538556700162799970888909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110359037800108533313925939 165538556700162799970888909)
              ·
                refine ⟨62076958762561049989083341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165538556700162799970888909 62076958762561049989083341)
                ·
                  refine ⟨23278859535960393745906253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62076958762561049989083341 23278859535960393745906253)
                  ·
                    refine ⟨8729572325985147654714845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23278859535960393745906253 8729572325985147654714845)
                    ·
                      refine ⟨3273589622244430370518067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8729572325985147654714845 3273589622244430370518067)
                      ·
                        rfl

theorem cell23_6375293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_6375293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375293 prefixEnd_6375293 := by exact prefixLift 6375293
  have htrace : WordTrace (prefixWord ++ tailWord_6375293) baseStart_6375293 baseEnd_6375293 := by
    simpa [prefixWord, tailWord_6375293, baseEnd_6375293] using wordTrace_append hprefix tailTrace_6375293
  have hstable : (prefixWord ++ tailWord_6375293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375293).length < 2 ^ (prefixWord ++ tailWord_6375293).sum := by decide
  have hdescent : baseEnd_6375293 < baseStart_6375293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375297 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_6375297 : Nat := 118140960795 + 6375297 * 2 ^ 59
def prefixEnd_6375297 : Nat := 4983230072969 + 3 ^ 40 * 6375297 * 2
def baseEnd_6375297 : Nat := 3273591676167048354868049

theorem tailTrace_6375297 : CollatzResearch.WordTrace tailWord_6375297 prefixEnd_6375297 3273591676167048354868049 := by
  unfold tailWord_6375297
  simp only [CollatzResearch.WordTrace]
  refine ⟨232526184384395257887796145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155017456256263505258530763 232526184384395257887796145)
  ·
    refine ⟨174394638288296443415847109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232526184384395257887796145 174394638288296443415847109)
    ·
      refine ⟨32698994679055583140471333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174394638288296443415847109 32698994679055583140471333)
      ·
        refine ⟨6131061502322921838838375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32698994679055583140471333 6131061502322921838838375)
        ·
          refine ⟨9196592253484382758257563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6131061502322921838838375 9196592253484382758257563)
          ·
            refine ⟨13794888380226574137386345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9196592253484382758257563 13794888380226574137386345)
            ·
              refine ⟨10346166285169930603039759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13794888380226574137386345 10346166285169930603039759)
              ·
                refine ⟨15519249427754895904559639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10346166285169930603039759 15519249427754895904559639)
                ·
                  refine ⟨23278874141632343856839459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15519249427754895904559639 23278874141632343856839459)
                  ·
                    refine ⟨34918311212448515785259189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23278874141632343856839459 34918311212448515785259189)
                    ·
                      refine ⟨3273591676167048354868049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34918311212448515785259189 3273591676167048354868049)
                      ·
                        rfl

theorem cell23_6375297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_6375297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375297 prefixEnd_6375297 := by exact prefixLift 6375297
  have htrace : WordTrace (prefixWord ++ tailWord_6375297) baseStart_6375297 baseEnd_6375297 := by
    simpa [prefixWord, tailWord_6375297, baseEnd_6375297] using wordTrace_append hprefix tailTrace_6375297
  have hstable : (prefixWord ++ tailWord_6375297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375297).length < 2 ^ (prefixWord ++ tailWord_6375297).sum := by decide
  have hdescent : baseEnd_6375297 < baseStart_6375297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375353 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 2, 1, 5]
def baseStart_6375353 : Nat := 118140960795 + 6375353 * 2 ^ 59
def prefixEnd_6375353 : Nat := 4983230072969 + 3 ^ 40 * 6375353 * 2
def baseEnd_6375353 : Nat := 3273620431083700135767791

theorem tailTrace_6375353 : CollatzResearch.WordTrace tailWord_6375353 prefixEnd_6375353 3273620431083700135767791 := by
  unfold tailWord_6375353
  simp only [CollatzResearch.WordTrace]
  refine ⟨232528226872192379451834713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155018817914794919634556475 232528226872192379451834713)
  ·
    refine ⟨174396170154144284588876035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232528226872192379451834713 174396170154144284588876035)
    ·
      refine ⟨261594255231216426883314053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174396170154144284588876035 261594255231216426883314053)
      ·
        refine ⟨49048922855853080040621385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261594255231216426883314053 49048922855853080040621385)
        ·
          refine ⟨36786692141889810030466039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49048922855853080040621385 36786692141889810030466039)
          ·
            refine ⟨55180038212834715045699059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36786692141889810030466039 55180038212834715045699059)
            ·
              refine ⟨82770057319252072568548589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55180038212834715045699059 82770057319252072568548589)
              ·
                refine ⟨31038771494719527213205721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82770057319252072568548589 31038771494719527213205721)
                ·
                  refine ⟨23279078621039645409904291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31038771494719527213205721 23279078621039645409904291)
                  ·
                    refine ⟨34918617931559468114856437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23279078621039645409904291 34918617931559468114856437)
                    ·
                      refine ⟨3273620431083700135767791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34918617931559468114856437 3273620431083700135767791)
                      ·
                        rfl

theorem cell23_6375353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_6375353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375353 prefixEnd_6375353 := by exact prefixLift 6375353
  have htrace : WordTrace (prefixWord ++ tailWord_6375353) baseStart_6375353 baseEnd_6375353 := by
    simpa [prefixWord, tailWord_6375353, baseEnd_6375353] using wordTrace_append hprefix tailTrace_6375353
  have hstable : (prefixWord ++ tailWord_6375353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375353).length < 2 ^ (prefixWord ++ tailWord_6375353).sum := by decide
  have hdescent : baseEnd_6375353 < baseStart_6375353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375380 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_6375380 : Nat := 118140960795 + 6375380 * 2 ^ 59
def prefixEnd_6375380 : Nat := 4983230072969 + 3 ^ 40 * 6375380 * 2
def baseEnd_6375380 : Nat := 3273634295061371530130167

theorem tailTrace_6375380 : CollatzResearch.WordTrace tailWord_6375380 prefixEnd_6375380 3273634295061371530130167 := by
  unfold tailWord_6375380
  simp only [CollatzResearch.WordTrace]
  refine ⟨116264605821547281531533797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155019474428729708708711729 116264605821547281531533797)
  ·
    refine ⟨21799613591540115287162587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116264605821547281531533797 21799613591540115287162587)
    ·
      refine ⟨32699420387310172930743881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21799613591540115287162587 32699420387310172930743881)
      ·
        refine ⟨24524565290482629698057911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32699420387310172930743881 24524565290482629698057911)
        ·
          refine ⟨36786847935723944547086867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24524565290482629698057911 36786847935723944547086867)
          ·
            refine ⟨55180271903585916820630301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36786847935723944547086867 55180271903585916820630301)
            ·
              refine ⟨20692601963844718807736363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55180271903585916820630301 20692601963844718807736363)
              ·
                refine ⟨31038902945767078211604545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20692601963844718807736363 31038902945767078211604545)
                ·
                  refine ⟨23279177209325308658703409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31038902945767078211604545 23279177209325308658703409)
                  ·
                    refine ⟨17459382906993981494027557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23279177209325308658703409 17459382906993981494027557)
                    ·
                      refine ⟨3273634295061371530130167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17459382906993981494027557 3273634295061371530130167)
                      ·
                        rfl

theorem cell23_6375380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_6375380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375380 prefixEnd_6375380 := by exact prefixLift 6375380
  have htrace : WordTrace (prefixWord ++ tailWord_6375380) baseStart_6375380 baseEnd_6375380 := by
    simpa [prefixWord, tailWord_6375380, baseEnd_6375380] using wordTrace_append hprefix tailTrace_6375380
  have hstable : (prefixWord ++ tailWord_6375380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375380).length < 2 ^ (prefixWord ++ tailWord_6375380).sum := by decide
  have hdescent : baseEnd_6375380 < baseStart_6375380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375405 : List Nat := [1, 5, 1, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_6375405 : Nat := 118140960795 + 6375405 * 2 ^ 59
def prefixEnd_6375405 : Nat := 4983230072969 + 3 ^ 40 * 6375405 * 2
def baseEnd_6375405 : Nat := 3273647132077733932317553

theorem tailTrace_6375405 : CollatzResearch.WordTrace tailWord_6375405 prefixEnd_6375405 3273647132077733932317553 := by
  unfold tailWord_6375405
  simp only [CollatzResearch.WordTrace]
  refine ⟨232530123468003992332727669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155020082312002661555151779 232530123468003992332727669)
  ·
    refine ⟨21799699075125374281193219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232530123468003992332727669 21799699075125374281193219)
    ·
      refine ⟨32699548612688061421789829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21799699075125374281193219 32699548612688061421789829)
      ·
        refine ⟨6131165364879011516585593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32699548612688061421789829 6131165364879011516585593)
        ·
          refine ⟨4598374023659258637439195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6131165364879011516585593 4598374023659258637439195)
          ·
            refine ⟨6897561035488887956158793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4598374023659258637439195 6897561035488887956158793)
            ·
              refine ⟨5173170776616665967119095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6897561035488887956158793 5173170776616665967119095)
              ·
                refine ⟨7759756164924998950678643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5173170776616665967119095 7759756164924998950678643)
                ·
                  refine ⟨11639634247387498426017965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7759756164924998950678643 11639634247387498426017965)
                  ·
                    refine ⟨4364862842770311909756737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11639634247387498426017965 4364862842770311909756737)
                    ·
                      refine ⟨3273647132077733932317553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4364862842770311909756737 3273647132077733932317553)
                      ·
                        rfl

theorem cell23_6375405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_6375405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375405 prefixEnd_6375405 := by exact prefixLift 6375405
  have htrace : WordTrace (prefixWord ++ tailWord_6375405) baseStart_6375405 baseEnd_6375405 := by
    simpa [prefixWord, tailWord_6375405, baseEnd_6375405] using wordTrace_append hprefix tailTrace_6375405
  have hstable : (prefixWord ++ tailWord_6375405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375405).length < 2 ^ (prefixWord ++ tailWord_6375405).sum := by decide
  have hdescent : baseEnd_6375405 < baseStart_6375405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375467 : List Nat := [1, 1, 1, 1, 2, 1, 4, 7, 1, 4]
def baseStart_6375467 : Nat := 118140960795 + 6375467 * 2 ^ 59
def prefixEnd_6375467 : Nat := 4983230072969 + 3 ^ 40 * 6375467 * 2
def baseEnd_6375467 : Nat := 1091226322626104229914089

theorem tailTrace_6375467 : CollatzResearch.WordTrace tailWord_6375467 prefixEnd_6375467 1091226322626104229914089 := by
  unfold tailWord_6375467
  simp only [CollatzResearch.WordTrace]
  refine ⟨232532384793779376921484655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155021589862519584614323103 232532384793779376921484655)
  ·
    refine ⟨348798577190669065382226983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232532384793779376921484655 348798577190669065382226983)
    ·
      refine ⟨523197865786003598073340475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348798577190669065382226983 523197865786003598073340475)
      ·
        refine ⟨784796798679005397110010713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523197865786003598073340475 784796798679005397110010713)
        ·
          refine ⟨588597599009254047832508035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784796798679005397110010713 588597599009254047832508035)
          ·
            refine ⟨882896398513881071748762053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588597599009254047832508035 882896398513881071748762053)
            ·
              refine ⟨165543074721352700952892885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 882896398513881071748762053 165543074721352700952892885)
              ·
                refine ⟨3879915813781703928583427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 165543074721352700952892885 3879915813781703928583427)
                ·
                  refine ⟨5819873720672555892875141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3879915813781703928583427 5819873720672555892875141)
                  ·
                    refine ⟨1091226322626104229914089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5819873720672555892875141 1091226322626104229914089)
                    ·
                      rfl

theorem cell23_6375467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 1, 4].length) (baseStart_6375467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375467 prefixEnd_6375467 := by exact prefixLift 6375467
  have htrace : WordTrace (prefixWord ++ tailWord_6375467) baseStart_6375467 baseEnd_6375467 := by
    simpa [prefixWord, tailWord_6375467, baseEnd_6375467] using wordTrace_append hprefix tailTrace_6375467
  have hstable : (prefixWord ++ tailWord_6375467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375467).length < 2 ^ (prefixWord ++ tailWord_6375467).sum := by decide
  have hdescent : baseEnd_6375467 < baseStart_6375467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375493 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 2, 9]
def baseStart_6375493 : Nat := 118140960795 + 6375493 * 2 ^ 59
def prefixEnd_6375493 : Nat := 4983230072969 + 3 ^ 40 * 6375493 * 2
def baseEnd_6375493 : Nat := 1091230772791776529339049

theorem tailTrace_6375493 : CollatzResearch.WordTrace tailWord_6375493 prefixEnd_6375493 1091230772791776529339049 := by
  unfold tailWord_6375493
  simp only [CollatzResearch.WordTrace]
  refine ⟨232533333091685183361931133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155022222061123455574620755 232533333091685183361931133)
  ·
    refine ⟨87199999909381943760724175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232533333091685183361931133 87199999909381943760724175)
    ·
      refine ⟨130799999864072915641086263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87199999909381943760724175 130799999864072915641086263)
      ·
        refine ⟨196199999796109373461629395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130799999864072915641086263 196199999796109373461629395)
        ·
          refine ⟨294299999694164060192444093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196199999796109373461629395 294299999694164060192444093)
          ·
            refine ⟨110362499885311522572166535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294299999694164060192444093 110362499885311522572166535)
            ·
              refine ⟨165543749827967283858249803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110362499885311522572166535 165543749827967283858249803)
              ·
                refine ⟨248315624741950925787374705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165543749827967283858249803 248315624741950925787374705)
                ·
                  refine ⟨186236718556463194340531029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248315624741950925787374705 186236718556463194340531029)
                  ·
                    refine ⟨1091230772791776529339049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 186236718556463194340531029 1091230772791776529339049)
                    ·
                      rfl

theorem cell23_6375493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_6375493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375493 prefixEnd_6375493 := by exact prefixLift 6375493
  have htrace : WordTrace (prefixWord ++ tailWord_6375493) baseStart_6375493 baseEnd_6375493 := by
    simpa [prefixWord, tailWord_6375493, baseEnd_6375493] using wordTrace_append hprefix tailTrace_6375493
  have hstable : (prefixWord ++ tailWord_6375493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375493).length < 2 ^ (prefixWord ++ tailWord_6375493).sum := by decide
  have hdescent : baseEnd_6375493 < baseStart_6375493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375494 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_6375494 : Nat := 118140960795 + 6375494 * 2 ^ 59
def prefixEnd_6375494 : Nat := 4983230072969 + 3 ^ 40 * 6375494 * 2
def baseEnd_6375494 : Nat := 3273692831855984084104643

theorem tailTrace_6375494 : CollatzResearch.WordTrace tailWord_6375494 prefixEnd_6375494 3273692831855984084104643 := by
  unfold tailWord_6375494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7266667798896298766647423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 155022246376454373688478357 7266667798896298766647423)
  ·
    refine ⟨10900001698344448149971135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7266667798896298766647423 10900001698344448149971135)
    ·
      refine ⟨16350002547516672224956703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10900001698344448149971135 16350002547516672224956703)
      ·
        refine ⟨24525003821275008337435055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16350002547516672224956703 24525003821275008337435055)
        ·
          refine ⟨36787505731912512506152583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24525003821275008337435055 36787505731912512506152583)
          ·
            refine ⟨55181258597868768759228875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36787505731912512506152583 55181258597868768759228875)
            ·
              refine ⟨82771887896803153138843313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55181258597868768759228875 82771887896803153138843313)
              ·
                refine ⟨62078915922602364854132485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82771887896803153138843313 62078915922602364854132485)
                ·
                  refine ⟨11639796735487943410149841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62078915922602364854132485 11639796735487943410149841)
                  ·
                    refine ⟨8729847551615957557612381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11639796735487943410149841 8729847551615957557612381)
                    ·
                      refine ⟨3273692831855984084104643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8729847551615957557612381 3273692831855984084104643)
                      ·
                        rfl

theorem cell23_6375494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_6375494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375494 prefixEnd_6375494 := by exact prefixLift 6375494
  have htrace : WordTrace (prefixWord ++ tailWord_6375494) baseStart_6375494 baseEnd_6375494 := by
    simpa [prefixWord, tailWord_6375494, baseEnd_6375494] using wordTrace_append hprefix tailTrace_6375494
  have hstable : (prefixWord ++ tailWord_6375494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375494).length < 2 ^ (prefixWord ++ tailWord_6375494).sum := by decide
  have hdescent : baseEnd_6375494 < baseStart_6375494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375503 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 7]
def baseStart_6375503 : Nat := 118140960795 + 6375503 * 2 ^ 59
def prefixEnd_6375503 : Nat := 4983230072969 + 3 ^ 40 * 6375503 * 2
def baseEnd_6375503 : Nat := 3273697453181874548892101

theorem tailTrace_6375503 : CollatzResearch.WordTrace tailWord_6375503 prefixEnd_6375503 3273697453181874548892101 := by
  unfold tailWord_6375503
  simp only [CollatzResearch.WordTrace]
  refine ⟨232533697821648955069795163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155022465214432636713196775 232533697821648955069795163)
  ·
    refine ⟨348800546732473432604692745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232533697821648955069795163 348800546732473432604692745)
    ·
      refine ⟨261600410049355074453519559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348800546732473432604692745 261600410049355074453519559)
      ·
        refine ⟨392400615074032611680279339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261600410049355074453519559 392400615074032611680279339)
        ·
          refine ⟨588600922611048917520419009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392400615074032611680279339 588600922611048917520419009)
          ·
            refine ⟨441450691958286688140314257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588600922611048917520419009 441450691958286688140314257)
            ·
              refine ⟨331088018968715016105235693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441450691958286688140314257 331088018968715016105235693)
              ·
                refine ⟨124158007113268131039463385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331088018968715016105235693 124158007113268131039463385)
                ·
                  refine ⟨93118505334951098279597539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124158007113268131039463385 93118505334951098279597539)
                  ·
                    refine ⟨139677758002426647419396309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93118505334951098279597539 139677758002426647419396309)
                    ·
                      refine ⟨3273697453181874548892101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139677758002426647419396309 3273697453181874548892101)
                      ·
                        rfl

theorem cell23_6375503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_6375503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375503 prefixEnd_6375503 := by exact prefixLift 6375503
  have htrace : WordTrace (prefixWord ++ tailWord_6375503) baseStart_6375503 baseEnd_6375503 := by
    simpa [prefixWord, tailWord_6375503, baseEnd_6375503] using wordTrace_append hprefix tailTrace_6375503
  have hstable : (prefixWord ++ tailWord_6375503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375503).length < 2 ^ (prefixWord ++ tailWord_6375503).sum := by decide
  have hdescent : baseEnd_6375503 < baseStart_6375503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375534 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_6375534 : Nat := 118140960795 + 6375534 * 2 ^ 59
def prefixEnd_6375534 : Nat := 4983230072969 + 3 ^ 40 * 6375534 * 2
def baseEnd_6375534 : Nat := 3273713371082163927604459

theorem tailTrace_6375534 : CollatzResearch.WordTrace tailWord_6375534 prefixEnd_6375534 3273713371082163927604459 := by
  unfold tailWord_6375534
  simp only [CollatzResearch.WordTrace]
  refine ⟨29066853560567080920521707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155023218989691098242782437 29066853560567080920521707)
  ·
    refine ⟨43600280340850621380782561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29066853560567080920521707 43600280340850621380782561)
    ·
      refine ⟨32700210255637966035586921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43600280340850621380782561 32700210255637966035586921)
      ·
        refine ⟨24525157691728474526690191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32700210255637966035586921 24525157691728474526690191)
        ·
          refine ⟨36787736537592711790035287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24525157691728474526690191 36787736537592711790035287)
          ·
            refine ⟨55181604806389067685052931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36787736537592711790035287 55181604806389067685052931)
            ·
              refine ⟨82772407209583601527579397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55181604806389067685052931 82772407209583601527579397)
              ·
                refine ⟨15519826351796925286421137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82772407209583601527579397 15519826351796925286421137)
                ·
                  refine ⟨11639869763847693964815853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15519826351796925286421137 11639869763847693964815853)
                  ·
                    refine ⟨4364951161442885236805945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11639869763847693964815853 4364951161442885236805945)
                    ·
                      refine ⟨3273713371082163927604459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4364951161442885236805945 3273713371082163927604459)
                      ·
                        rfl

theorem cell23_6375534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_6375534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375534 prefixEnd_6375534 := by exact prefixLift 6375534
  have htrace : WordTrace (prefixWord ++ tailWord_6375534) baseStart_6375534 baseEnd_6375534 := by
    simpa [prefixWord, tailWord_6375534, baseEnd_6375534] using wordTrace_append hprefix tailTrace_6375534
  have hstable : (prefixWord ++ tailWord_6375534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375534).length < 2 ^ (prefixWord ++ tailWord_6375534).sum := by decide
  have hdescent : baseEnd_6375534 < baseStart_6375534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375557 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 1, 6]
def baseStart_6375557 : Nat := 118140960795 + 6375557 * 2 ^ 59
def prefixEnd_6375557 : Nat := 4983230072969 + 3 ^ 40 * 6375557 * 2
def baseEnd_6375557 : Nat := 1091241727045739112538951

theorem tailTrace_6375557 : CollatzResearch.WordTrace tailWord_6375557 prefixEnd_6375557 1091241727045739112538951 := by
  unfold tailWord_6375557
  simp only [CollatzResearch.WordTrace]
  refine ⟨232535667363453322292260925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155023778242302214861507283 232535667363453322292260925)
  ·
    refine ⟨87200875261294995859597847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232535667363453322292260925 87200875261294995859597847)
    ·
      refine ⟨130801312891942493789396771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87200875261294995859597847 130801312891942493789396771)
      ·
        refine ⟨196201969337913740684095157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130801312891942493789396771 196201969337913740684095157)
        ·
          refine ⟨18393934625429413189133921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196201969337913740684095157 18393934625429413189133921)
          ·
            refine ⟨13795450969072059891850441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18393934625429413189133921 13795450969072059891850441)
            ·
              refine ⟨10346588226804044918887831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13795450969072059891850441 10346588226804044918887831)
              ·
                refine ⟨15519882340206067378331747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10346588226804044918887831 15519882340206067378331747)
                ·
                  refine ⟨23279823510309101067497621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15519882340206067378331747 23279823510309101067497621)
                  ·
                    refine ⟨1091241727045739112538951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23279823510309101067497621 1091241727045739112538951)
                    ·
                      rfl

theorem cell23_6375557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_6375557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375557 prefixEnd_6375557 := by exact prefixLift 6375557
  have htrace : WordTrace (prefixWord ++ tailWord_6375557) baseStart_6375557 baseEnd_6375557 := by
    simpa [prefixWord, tailWord_6375557, baseEnd_6375557] using wordTrace_append hprefix tailTrace_6375557
  have hstable : (prefixWord ++ tailWord_6375557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375557).length < 2 ^ (prefixWord ++ tailWord_6375557).sum := by decide
  have hdescent : baseEnd_6375557 < baseStart_6375557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375578 : List Nat := [3, 1, 1, 5, 3, 1, 2, 1, 1, 5]
def baseStart_6375578 : Nat := 118140960795 + 6375578 * 2 ^ 59
def prefixEnd_6375578 : Nat := 4983230072969 + 3 ^ 40 * 6375578 * 2
def baseEnd_6375578 : Nat := 1091245321410320585151419

theorem tailTrace_6375578 : CollatzResearch.WordTrace tailWord_6375578 prefixEnd_6375578 1091245321410320585151419 := by
  unfold tailWord_6375578
  simp only [CollatzResearch.WordTrace]
  refine ⟨58134108324094310719693847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155024288864251495252516925 58134108324094310719693847)
  ·
    refine ⟨87201162486141466079540771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58134108324094310719693847 87201162486141466079540771)
    ·
      refine ⟨130801743729212199119311157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87201162486141466079540771 130801743729212199119311157)
      ·
        refine ⟨12262663474613643667435421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130801743729212199119311157 12262663474613643667435421)
        ·
          refine ⟨4598498802980116375288283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12262663474613643667435421 4598498802980116375288283)
          ·
            refine ⟨6897748204470174562932425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4598498802980116375288283 6897748204470174562932425)
            ·
              refine ⟨5173311153352630922199319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6897748204470174562932425 5173311153352630922199319)
              ·
                refine ⟨7759966730028946383298979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5173311153352630922199319 7759966730028946383298979)
                ·
                  refine ⟨11639950095043419574948469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7759966730028946383298979 11639950095043419574948469)
                  ·
                    refine ⟨1091245321410320585151419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11639950095043419574948469 1091245321410320585151419)
                    ·
                      rfl

theorem cell23_6375578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_6375578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375578 prefixEnd_6375578 := by exact prefixLift 6375578
  have htrace : WordTrace (prefixWord ++ tailWord_6375578) baseStart_6375578 baseEnd_6375578 := by
    simpa [prefixWord, tailWord_6375578, baseEnd_6375578] using wordTrace_append hprefix tailTrace_6375578
  have hstable : (prefixWord ++ tailWord_6375578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375578).length < 2 ^ (prefixWord ++ tailWord_6375578).sum := by decide
  have hdescent : baseEnd_6375578 < baseStart_6375578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375581 : List Nat := [1, 4, 2, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_6375581 : Nat := 118140960795 + 6375581 * 2 ^ 59
def prefixEnd_6375581 : Nat := 4983230072969 + 3 ^ 40 * 6375581 * 2
def baseEnd_6375581 : Nat := 3273737504672925243716743

theorem tailTrace_6375581 : CollatzResearch.WordTrace tailWord_6375581 prefixEnd_6375581 3273737504672925243716743 := by
  unfold tailWord_6375581
  simp only [CollatzResearch.WordTrace]
  refine ⟨232536542715366374391134597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155024361810244249594089731 232536542715366374391134597)
  ·
    refine ⟨43600601759131195198337737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232536542715366374391134597 43600601759131195198337737)
    ·
      refine ⟨32700451319348396398753303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43600601759131195198337737 32700451319348396398753303)
      ·
        refine ⟨49050676979022594598129955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32700451319348396398753303 49050676979022594598129955)
        ·
          refine ⟨73576015468533891897194933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49050676979022594598129955 73576015468533891897194933)
          ·
            refine ⟨6897751450175052365362025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73576015468533891897194933 6897751450175052365362025)
            ·
              refine ⟨5173313587631289274021519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6897751450175052365362025 5173313587631289274021519)
              ·
                refine ⟨7759970381446933911032279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5173313587631289274021519 7759970381446933911032279)
                ·
                  refine ⟨11639955572170400866548419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7759970381446933911032279 11639955572170400866548419)
                  ·
                    refine ⟨17459933358255601299822629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11639955572170400866548419 17459933358255601299822629)
                    ·
                      refine ⟨3273737504672925243716743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17459933358255601299822629 3273737504672925243716743)
                      ·
                        rfl

theorem cell23_6375581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_6375581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375581 prefixEnd_6375581 := by exact prefixLift 6375581
  have htrace : WordTrace (prefixWord ++ tailWord_6375581) baseStart_6375581 baseEnd_6375581 := by
    simpa [prefixWord, tailWord_6375581, baseEnd_6375581] using wordTrace_append hprefix tailTrace_6375581
  have hstable : (prefixWord ++ tailWord_6375581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375581).length < 2 ^ (prefixWord ++ tailWord_6375581).sum := by decide
  have hdescent : baseEnd_6375581 < baseStart_6375581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375584 : List Nat := [2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 3]
def baseStart_6375584 : Nat := 118140960795 + 6375584 * 2 ^ 59
def prefixEnd_6375584 : Nat := 4983230072969 + 3 ^ 40 * 6375584 * 2
def baseEnd_6375584 : Nat := 3273739045114888731979229

theorem tailTrace_6375584 : CollatzResearch.WordTrace tailWord_6375584 prefixEnd_6375584 3273739045114888731979229 := by
  unfold tailWord_6375584
  simp only [CollatzResearch.WordTrace]
  refine ⟨116268326067177752951746903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155024434756237003935662537 116268326067177752951746903)
  ·
    refine ⟨174402489100766629427620355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116268326067177752951746903 174402489100766629427620355)
    ·
      refine ⟨261603733651149944141430533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174402489100766629427620355 261603733651149944141430533)
      ·
        refine ⟨49050700059590614526518225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261603733651149944141430533 49050700059590614526518225)
        ·
          refine ⟨36788025044692960894888669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49050700059590614526518225 36788025044692960894888669)
          ·
            refine ⟨13795509391759860335583251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36788025044692960894888669 13795509391759860335583251)
            ·
              refine ⟨20693264087639790503374877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13795509391759860335583251 20693264087639790503374877)
              ·
                refine ⟨7759974032864921438765579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20693264087639790503374877 7759974032864921438765579)
                ·
                  refine ⟨11639961049297382158148369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7759974032864921438765579 11639961049297382158148369)
                  ·
                    refine ⟨8729970786973036618611277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11639961049297382158148369 8729970786973036618611277)
                    ·
                      refine ⟨3273739045114888731979229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8729970786973036618611277 3273739045114888731979229)
                      ·
                        rfl

theorem cell23_6375584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_6375584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375584 prefixEnd_6375584 := by exact prefixLift 6375584
  have htrace : WordTrace (prefixWord ++ tailWord_6375584) baseStart_6375584 baseEnd_6375584 := by
    simpa [prefixWord, tailWord_6375584, baseEnd_6375584] using wordTrace_append hprefix tailTrace_6375584
  have hstable : (prefixWord ++ tailWord_6375584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375584).length < 2 ^ (prefixWord ++ tailWord_6375584).sum := by decide
  have hdescent : baseEnd_6375584 < baseStart_6375584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375618 : List Nat := [3, 5, 1, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_6375618 : Nat := 118140960795 + 6375618 * 2 ^ 59
def prefixEnd_6375618 : Nat := 4983230072969 + 3 ^ 40 * 6375618 * 2
def baseEnd_6375618 : Nat := 3273756503457141598954073

theorem tailTrace_6375618 : CollatzResearch.WordTrace tailWord_6375618 prefixEnd_6375618 3273756503457141598954073 := by
  unfold tailWord_6375618
  simp only [CollatzResearch.WordTrace]
  refine ⟨58134473054058082427557877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155025261477488219806821005 58134473054058082427557877)
  ·
    refine ⟨5450106848817945227583551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58134473054058082427557877 5450106848817945227583551)
    ·
      refine ⟨8175160273226917841375327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5450106848817945227583551 8175160273226917841375327)
      ·
        refine ⟨12262740409840376762062991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8175160273226917841375327 12262740409840376762062991)
        ·
          refine ⟨18394110614760565143094487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12262740409840376762062991 18394110614760565143094487)
          ·
            refine ⟨27591165922140847714641731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18394110614760565143094487 27591165922140847714641731)
            ·
              refine ⟨41386748883211271571962597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27591165922140847714641731 41386748883211271571962597)
              ·
                refine ⟨7760015415602113419742987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41386748883211271571962597 7760015415602113419742987)
                ·
                  refine ⟨11640023123403170129614481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7760015415602113419742987 11640023123403170129614481)
                  ·
                    refine ⟨8730017342552377597210861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11640023123403170129614481 8730017342552377597210861)
                    ·
                      refine ⟨3273756503457141598954073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8730017342552377597210861 3273756503457141598954073)
                      ·
                        rfl

theorem cell23_6375618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_6375618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375618 prefixEnd_6375618 := by exact prefixLift 6375618
  have htrace : WordTrace (prefixWord ++ tailWord_6375618) baseStart_6375618 baseEnd_6375618 := by
    simpa [prefixWord, tailWord_6375618, baseEnd_6375618] using wordTrace_append hprefix tailTrace_6375618
  have hstable : (prefixWord ++ tailWord_6375618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375618).length < 2 ^ (prefixWord ++ tailWord_6375618).sum := by decide
  have hdescent : baseEnd_6375618 < baseStart_6375618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375694 : List Nat := [4, 1, 1, 2, 1, 2, 2, 5, 5]
def baseStart_6375694 : Nat := 118140960795 + 6375694 * 2 ^ 59
def prefixEnd_6375694 : Nat := 4983230072969 + 3 ^ 40 * 6375694 * 2
def baseEnd_6375694 : Nat := 363755058665209255733747

theorem tailTrace_6375694 : CollatzResearch.WordTrace tailWord_6375694 prefixEnd_6375694 363755058665209255733747 := by
  unfold tailWord_6375694
  simp only [CollatzResearch.WordTrace]
  refine ⟨29067583020494624336249767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155027109442637996459998757 29067583020494624336249767)
  ·
    refine ⟨43601374530741936504374651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29067583020494624336249767 43601374530741936504374651)
    ·
      refine ⟨65402061796112904756561977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43601374530741936504374651 65402061796112904756561977)
      ·
        refine ⟨49051546347084678567421483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65402061796112904756561977 49051546347084678567421483)
        ·
          refine ⟨73577319520627017851132225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49051546347084678567421483 73577319520627017851132225)
          ·
            refine ⟨55182989640470263388349169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73577319520627017851132225 55182989640470263388349169)
            ·
              refine ⟨41387242230352697541261877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55182989640470263388349169 41387242230352697541261877)
              ·
                refine ⟨3880053959095565394493301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41387242230352697541261877 3880053959095565394493301)
                ·
                  refine ⟨363755058665209255733747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3880053959095565394493301 363755058665209255733747)
                  ·
                    rfl

theorem cell23_6375694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_6375694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375694 prefixEnd_6375694 := by exact prefixLift 6375694
  have htrace : WordTrace (prefixWord ++ tailWord_6375694) baseStart_6375694 baseEnd_6375694 := by
    simpa [prefixWord, tailWord_6375694, baseEnd_6375694] using wordTrace_append hprefix tailTrace_6375694
  have hstable : (prefixWord ++ tailWord_6375694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375694).length < 2 ^ (prefixWord ++ tailWord_6375694).sum := by decide
  have hdescent : baseEnd_6375694 < baseStart_6375694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375707 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 2, 5]
def baseStart_6375707 : Nat := 118140960795 + 6375707 * 2 ^ 59
def prefixEnd_6375707 : Nat := 4983230072969 + 3 ^ 40 * 6375707 * 2
def baseEnd_6375707 : Nat := 1091267401078463916913721

theorem tailTrace_6375707 : CollatzResearch.WordTrace tailWord_6375707 prefixEnd_6375707 1091267401078463916913721 := by
  unfold tailWord_6375707
  simp only [CollatzResearch.WordTrace]
  refine ⟨232541138312909897910221375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155027425541939931940147583 232541138312909897910221375)
  ·
    refine ⟨348811707469364846865332063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232541138312909897910221375 348811707469364846865332063)
    ·
      refine ⟨523217561204047270297998095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348811707469364846865332063 523217561204047270297998095)
      ·
        refine ⟨784826341806070905446997143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523217561204047270297998095 784826341806070905446997143)
        ·
          refine ⟨1177239512709106358170495715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784826341806070905446997143 1177239512709106358170495715)
          ·
            refine ⟨1765859269063659537255743573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177239512709106358170495715 1765859269063659537255743573)
            ·
              refine ⟨20693663309339760202215745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1765859269063659537255743573 20693663309339760202215745)
              ·
                refine ⟨15520247482004820151661809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20693663309339760202215745 15520247482004820151661809)
                ·
                  refine ⟨11640185611503615113746357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15520247482004820151661809 11640185611503615113746357)
                  ·
                    refine ⟨1091267401078463916913721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11640185611503615113746357 1091267401078463916913721)
                    ·
                      rfl

theorem cell23_6375707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 5].length) (baseStart_6375707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375707 prefixEnd_6375707 := by exact prefixLift 6375707
  have htrace : WordTrace (prefixWord ++ tailWord_6375707) baseStart_6375707 baseEnd_6375707 := by
    simpa [prefixWord, tailWord_6375707, baseEnd_6375707] using wordTrace_append hprefix tailTrace_6375707
  have hstable : (prefixWord ++ tailWord_6375707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375707).length < 2 ^ (prefixWord ++ tailWord_6375707).sum := by decide
  have hdescent : baseEnd_6375707 < baseStart_6375707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375711 : List Nat := [1, 1, 2, 4, 3, 1, 4, 2, 5]
def baseStart_6375711 : Nat := 118140960795 + 6375711 * 2 ^ 59
def prefixEnd_6375711 : Nat := 4983230072969 + 3 ^ 40 * 6375711 * 2
def baseEnd_6375711 : Nat := 363756028573112192787905

theorem tailTrace_6375711 : CollatzResearch.WordTrace tailWord_6375711 prefixEnd_6375711 363756028573112192787905 := by
  unfold tailWord_6375711
  simp only [CollatzResearch.WordTrace]
  refine ⟨232541284204895406593366987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155027522803263604395577991 232541284204895406593366987)
  ·
    refine ⟨348811926307343109890050481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232541284204895406593366987 348811926307343109890050481)
    ·
      refine ⟨261608944730507332417537861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348811926307343109890050481 261608944730507332417537861)
      ·
        refine ⟨49051677136970124828288349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261608944730507332417537861 49051677136970124828288349)
        ·
          refine ⟨18394378926363796810608131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49051677136970124828288349 18394378926363796810608131)
          ·
            refine ⟨27591568389545695215912197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18394378926363796810608131 27591568389545695215912197)
            ·
              refine ⟨5173419073039817852983537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27591568389545695215912197 5173419073039817852983537)
              ·
                refine ⟨3880064304779863389737653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5173419073039817852983537 3880064304779863389737653)
                ·
                  refine ⟨363756028573112192787905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3880064304779863389737653 363756028573112192787905)
                  ·
                    rfl

theorem cell23_6375711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 5].length) (baseStart_6375711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375711 prefixEnd_6375711 := by exact prefixLift 6375711
  have htrace : WordTrace (prefixWord ++ tailWord_6375711) baseStart_6375711 baseEnd_6375711 := by
    simpa [prefixWord, tailWord_6375711, baseEnd_6375711] using wordTrace_append hprefix tailTrace_6375711
  have hstable : (prefixWord ++ tailWord_6375711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375711).length < 2 ^ (prefixWord ++ tailWord_6375711).sum := by decide
  have hdescent : baseEnd_6375711 < baseStart_6375711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375727 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 4]
def baseStart_6375727 : Nat := 118140960795 + 6375727 * 2 ^ 59
def prefixEnd_6375727 : Nat := 4983230072969 + 3 ^ 40 * 6375727 * 2
def baseEnd_6375727 : Nat := 3273812472848481672491071

theorem tailTrace_6375727 : CollatzResearch.WordTrace tailWord_6375727 prefixEnd_6375727 3273812472848481672491071 := by
  unfold tailWord_6375727
  simp only [CollatzResearch.WordTrace]
  refine ⟨232541867772837441325949435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155027911848558294217299623 232541867772837441325949435)
  ·
    refine ⟨348812801659256161988924153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232541867772837441325949435 348812801659256161988924153)
    ·
      refine ⟨261609601244442121491693115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348812801659256161988924153 261609601244442121491693115)
      ·
        refine ⟨392414401866663182237539673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261609601244442121491693115 392414401866663182237539673)
        ·
          refine ⟨294310801399997386678154755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392414401866663182237539673 294310801399997386678154755)
          ·
            refine ⟨441466202099996080017232133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294310801399997386678154755 441466202099996080017232133)
            ·
              refine ⟨82774912893749265003231025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 441466202099996080017232133 82774912893749265003231025)
              ·
                refine ⟨62081184670311948752423269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82774912893749265003231025 62081184670311948752423269)
                ·
                  refine ⟨11640222125683490391079363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62081184670311948752423269 11640222125683490391079363)
                  ·
                    refine ⟨17460333188525235586619045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11640222125683490391079363 17460333188525235586619045)
                    ·
                      refine ⟨3273812472848481672491071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17460333188525235586619045 3273812472848481672491071)
                      ·
                        rfl

theorem cell23_6375727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_6375727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375727 prefixEnd_6375727 := by exact prefixLift 6375727
  have htrace : WordTrace (prefixWord ++ tailWord_6375727) baseStart_6375727 baseEnd_6375727 := by
    simpa [prefixWord, tailWord_6375727, baseEnd_6375727] using wordTrace_append hprefix tailTrace_6375727
  have hstable : (prefixWord ++ tailWord_6375727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375727).length < 2 ^ (prefixWord ++ tailWord_6375727).sum := by decide
  have hdescent : baseEnd_6375727 < baseStart_6375727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375767 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 8]
def baseStart_6375767 : Nat := 118140960795 + 6375767 * 2 ^ 59
def prefixEnd_6375767 : Nat := 4983230072969 + 3 ^ 40 * 6375767 * 2
def baseEnd_6375767 : Nat := 363759223563851279554543

theorem tailTrace_6375767 : CollatzResearch.WordTrace tailWord_6375767 prefixEnd_6375767 363759223563851279554543 := by
  unfold tailWord_6375767
  simp only [CollatzResearch.WordTrace]
  refine ⟨232543326692692528157405555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155028884461795018771603703 232543326692692528157405555)
  ·
    refine ⟨348814990039038792236108333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232543326692692528157405555 348814990039038792236108333)
    ·
      refine ⟨130805621264639547088540625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348814990039038792236108333 130805621264639547088540625)
      ·
        refine ⟨98104215948479660316405469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130805621264639547088540625 98104215948479660316405469)
        ·
          refine ⟨36789080980679872618652051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98104215948479660316405469 36789080980679872618652051)
          ·
            refine ⟨55183621471019808927978077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36789080980679872618652051 55183621471019808927978077)
            ·
              refine ⟨20693858051632428347991779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55183621471019808927978077 20693858051632428347991779)
              ·
                refine ⟨31040787077448642521987669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20693858051632428347991779 31040787077448642521987669)
                ·
                  refine ⟨363759223563851279554543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31040787077448642521987669 363759223563851279554543)
                  ·
                    rfl

theorem cell23_6375767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 8].length) (baseStart_6375767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375767 prefixEnd_6375767 := by exact prefixLift 6375767
  have htrace : WordTrace (prefixWord ++ tailWord_6375767) baseStart_6375767 baseEnd_6375767 := by
    simpa [prefixWord, tailWord_6375767, baseEnd_6375767] using wordTrace_append hprefix tailTrace_6375767
  have hstable : (prefixWord ++ tailWord_6375767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375767).length < 2 ^ (prefixWord ++ tailWord_6375767).sum := by decide
  have hdescent : baseEnd_6375767 < baseStart_6375767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375848 : List Nat := [2, 1, 6, 1, 1, 1, 3, 2, 1, 5]
def baseStart_6375848 : Nat := 118140960795 + 6375848 * 2 ^ 59
def prefixEnd_6375848 : Nat := 4983230072969 + 3 ^ 40 * 6375848 * 2
def baseEnd_6375848 : Nat := 1091291534669225233026005

theorem tailTrace_6375848 : CollatzResearch.WordTrace tailWord_6375848 prefixEnd_6375848 1091291534669225233026005 := by
  unfold tailWord_6375848
  simp only [CollatzResearch.WordTrace]
  refine ⟨116273140502699539495552099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155030854003599385994069465 116273140502699539495552099)
  ·
    refine ⟨174409710754049309243328149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116273140502699539495552099 174409710754049309243328149)
    ·
      refine ⟨8175455191596061370781007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174409710754049309243328149 8175455191596061370781007)
      ·
        refine ⟨12263182787394092056171511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8175455191596061370781007 12263182787394092056171511)
        ·
          refine ⟨18394774181091138084257267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12263182787394092056171511 18394774181091138084257267)
          ·
            refine ⟨27592161271636707126385901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18394774181091138084257267 27592161271636707126385901)
            ·
              refine ⟨10347060476863765172394713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27592161271636707126385901 10347060476863765172394713)
              ·
                refine ⟨7760295357647823879296035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10347060476863765172394713 7760295357647823879296035)
                ·
                  refine ⟨11640443036471735818944053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7760295357647823879296035 11640443036471735818944053)
                  ·
                    refine ⟨1091291534669225233026005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11640443036471735818944053 1091291534669225233026005)
                    ·
                      rfl

theorem cell23_6375848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_6375848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375848 prefixEnd_6375848 := by exact prefixLift 6375848
  have htrace : WordTrace (prefixWord ++ tailWord_6375848) baseStart_6375848 baseEnd_6375848 := by
    simpa [prefixWord, tailWord_6375848, baseEnd_6375848] using wordTrace_append hprefix tailTrace_6375848
  have hstable : (prefixWord ++ tailWord_6375848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375848).length < 2 ^ (prefixWord ++ tailWord_6375848).sum := by decide
  have hdescent : baseEnd_6375848 < baseStart_6375848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375861 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 1, 6]
def baseStart_6375861 : Nat := 118140960795 + 6375861 * 2 ^ 59
def prefixEnd_6375861 : Nat := 4983230072969 + 3 ^ 40 * 6375861 * 2
def baseEnd_6375861 : Nat := 1091293759752061382738485

theorem tailTrace_6375861 : CollatzResearch.WordTrace tailWord_6375861 prefixEnd_6375861 1091293759752061382738485 := by
  unfold tailWord_6375861
  simp only [CollatzResearch.WordTrace]
  refine ⟨232546755154351982211327437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155031170102901321474218291 232546755154351982211327437)
  ·
    refine ⟨87205033182881993329247789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232546755154351982211327437 87205033182881993329247789)
    ·
      refine ⟨32701887443580747498467921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87205033182881993329247789 32701887443580747498467921)
      ·
        refine ⟨24526415582685560623850941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32701887443580747498467921 24526415582685560623850941)
        ·
          refine ⟨9197405843507085233944103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24526415582685560623850941 9197405843507085233944103)
          ·
            refine ⟨13796108765260627850916155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9197405843507085233944103 13796108765260627850916155)
            ·
              refine ⟨20694163147890941776374233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13796108765260627850916155 20694163147890941776374233)
              ·
                refine ⟨15520622360918206332280675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20694163147890941776374233 15520622360918206332280675)
                ·
                  refine ⟨23280933541377309498421013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15520622360918206332280675 23280933541377309498421013)
                  ·
                    refine ⟨1091293759752061382738485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23280933541377309498421013 1091293759752061382738485)
                    ·
                      rfl

theorem cell23_6375861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_6375861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375861 prefixEnd_6375861 := by exact prefixLift 6375861
  have htrace : WordTrace (prefixWord ++ tailWord_6375861) baseStart_6375861 baseEnd_6375861 := by
    simpa [prefixWord, tailWord_6375861, baseEnd_6375861] using wordTrace_append hprefix tailTrace_6375861
  have hstable : (prefixWord ++ tailWord_6375861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375861).length < 2 ^ (prefixWord ++ tailWord_6375861).sum := by decide
  have hdescent : baseEnd_6375861 < baseStart_6375861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375877 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_6375877 : Nat := 118140960795 + 6375877 * 2 ^ 59
def prefixEnd_6375877 : Nat := 4983230072969 + 3 ^ 40 * 6375877 * 2
def baseEnd_6375877 : Nat := 3273889494946656085615381

theorem tailTrace_6375877 : CollatzResearch.WordTrace tailWord_6375877 prefixEnd_6375877 3273889494946656085615381 := by
  unfold tailWord_6375877
  simp only [CollatzResearch.WordTrace]
  refine ⟨232547338722294016943909885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155031559148196011295939923 232547338722294016943909885)
  ·
    refine ⟨87205252020860256353966207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232547338722294016943909885 87205252020860256353966207)
    ·
      refine ⟨130807878031290384530949311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87205252020860256353966207 130807878031290384530949311)
      ·
        refine ⟨196211817046935576796423967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130807878031290384530949311 196211817046935576796423967)
        ·
          refine ⟨294317725570403365194635951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196211817046935576796423967 294317725570403365194635951)
          ·
            refine ⟨441476588355605047791953927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294317725570403365194635951 441476588355605047791953927)
            ·
              refine ⟨662214882533407571687930891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441476588355605047791953927 662214882533407571687930891)
              ·
                refine ⟨993322323800111357531896337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662214882533407571687930891 993322323800111357531896337)
                ·
                  refine ⟨744991742850083518148922253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 993322323800111357531896337 744991742850083518148922253)
                  ·
                    refine ⟨279371903568781319305845845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 744991742850083518148922253 279371903568781319305845845)
                    ·
                      refine ⟨3273889494946656085615381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 279371903568781319305845845 3273889494946656085615381)
                      ·
                        rfl

theorem cell23_6375877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_6375877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375877 prefixEnd_6375877 := by exact prefixLift 6375877
  have htrace : WordTrace (prefixWord ++ tailWord_6375877) baseStart_6375877 baseEnd_6375877 := by
    simpa [prefixWord, tailWord_6375877, baseEnd_6375877] using wordTrace_append hprefix tailTrace_6375877
  have hstable : (prefixWord ++ tailWord_6375877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375877).length < 2 ^ (prefixWord ++ tailWord_6375877).sum := by decide
  have hdescent : baseEnd_6375877 < baseStart_6375877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375922 : List Nat := [3, 2, 1, 4, 2, 2, 2, 1, 1, 2, 3]
def baseStart_6375922 : Nat := 118140960795 + 6375922 * 2 ^ 59
def prefixEnd_6375922 : Nat := 4983230072969 + 3 ^ 40 * 6375922 * 2
def baseEnd_6375922 : Nat := 3273912601576108409552675

theorem tailTrace_6375922 : CollatzResearch.WordTrace tailWord_6375922 prefixEnd_6375922 3273912601576108409552675 := by
  unfold tailWord_6375922
  simp only [CollatzResearch.WordTrace]
  refine ⟨58137245001782747407324505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155032653338087326419532013 58137245001782747407324505)
  ·
    refine ⟨43602933751337060555493379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58137245001782747407324505 43602933751337060555493379)
    ·
      refine ⟨65404400627005590833240069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43602933751337060555493379 65404400627005590833240069)
      ·
        refine ⟨12263325117563548281232513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65404400627005590833240069 12263325117563548281232513)
        ·
          refine ⟨9197493838172661210924385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12263325117563548281232513 9197493838172661210924385)
          ·
            refine ⟨6898120378629495908193289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9197493838172661210924385 6898120378629495908193289)
            ·
              refine ⟨5173590283972121931144967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6898120378629495908193289 5173590283972121931144967)
              ·
                refine ⟨7760385425958182896717451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5173590283972121931144967 7760385425958182896717451)
                ·
                  refine ⟨11640578138937274345076177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7760385425958182896717451 11640578138937274345076177)
                  ·
                    refine ⟨8730433604202955758807133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11640578138937274345076177 8730433604202955758807133)
                    ·
                      refine ⟨3273912601576108409552675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8730433604202955758807133 3273912601576108409552675)
                      ·
                        rfl

theorem cell23_6375922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_6375922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375922 prefixEnd_6375922 := by exact prefixLift 6375922
  have htrace : WordTrace (prefixWord ++ tailWord_6375922) baseStart_6375922 baseEnd_6375922 := by
    simpa [prefixWord, tailWord_6375922, baseEnd_6375922] using wordTrace_append hprefix tailTrace_6375922
  have hstable : (prefixWord ++ tailWord_6375922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375922).length < 2 ^ (prefixWord ++ tailWord_6375922).sum := by decide
  have hdescent : baseEnd_6375922 < baseStart_6375922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375928 : List Nat := [2, 1, 2, 1, 1, 4, 3, 3, 1, 3, 2]
def baseStart_6375928 : Nat := 118140960795 + 6375928 * 2 ^ 59
def prefixEnd_6375928 : Nat := 4983230072969 + 3 ^ 40 * 6375928 * 2
def baseEnd_6375928 : Nat := 3273915682460035386077647

theorem tailTrace_6375928 : CollatzResearch.WordTrace tailWord_6375928 prefixEnd_6375928 3273915682460035386077647 := by
  unfold tailWord_6375928
  simp only [CollatzResearch.WordTrace]
  refine ⟨116274599422554626327008219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155032799230072835102677625 116274599422554626327008219)
  ·
    refine ⟨174411899133831939490512329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116274599422554626327008219 174411899133831939490512329)
    ·
      refine ⟨130808924350373954617884247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174411899133831939490512329 130808924350373954617884247)
      ·
        refine ⟨196213386525560931926826371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130808924350373954617884247 196213386525560931926826371)
        ·
          refine ⟨294320079788341397890239557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196213386525560931926826371 294320079788341397890239557)
          ·
            refine ⟨55185014960314012104419917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294320079788341397890239557 55185014960314012104419917)
            ·
              refine ⟨20694380610117754539157469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55185014960314012104419917 20694380610117754539157469)
              ·
                refine ⟨7760392728794157952184051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20694380610117754539157469 7760392728794157952184051)
                ·
                  refine ⟨11640589093191236928276077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7760392728794157952184051 11640589093191236928276077)
                  ·
                    refine ⟨4365220909946713848103529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11640589093191236928276077 4365220909946713848103529)
                    ·
                      refine ⟨3273915682460035386077647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4365220909946713848103529 3273915682460035386077647)
                      ·
                        rfl

theorem cell23_6375928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 1, 3, 2].length) (baseStart_6375928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375928 prefixEnd_6375928 := by exact prefixLift 6375928
  have htrace : WordTrace (prefixWord ++ tailWord_6375928) baseStart_6375928 baseEnd_6375928 := by
    simpa [prefixWord, tailWord_6375928, baseEnd_6375928] using wordTrace_append hprefix tailTrace_6375928
  have hstable : (prefixWord ++ tailWord_6375928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375928).length < 2 ^ (prefixWord ++ tailWord_6375928).sum := by decide
  have hdescent : baseEnd_6375928 < baseStart_6375928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375941 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 3, 4, 2]
def baseStart_6375941 : Nat := 118140960795 + 6375941 * 2 ^ 59
def prefixEnd_6375941 : Nat := 4983230072969 + 3 ^ 40 * 6375941 * 2
def baseEnd_6375941 : Nat := 3273922357708543835215087

theorem tailTrace_6375941 : CollatzResearch.WordTrace tailWord_6375941 prefixEnd_6375941 3273922357708543835215087 := by
  unfold tailWord_6375941
  simp only [CollatzResearch.WordTrace]
  refine ⟨232549672994062155874239677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155033115329374770582826451 232549672994062155874239677)
  ·
    refine ⟨87206127372773308452839879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232549672994062155874239677 87206127372773308452839879)
    ·
      refine ⟨130809191059159962679259819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87206127372773308452839879 130809191059159962679259819)
      ·
        refine ⟨196213786588739944018889729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130809191059159962679259819 196213786588739944018889729)
        ·
          refine ⟨147160339941554958014167297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196213786588739944018889729 147160339941554958014167297)
          ·
            refine ⟨110370254956166218510625473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147160339941554958014167297 110370254956166218510625473)
            ·
              refine ⟨82777691217124663882969105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110370254956166218510625473 82777691217124663882969105)
              ·
                refine ⟨62083268412843497912226829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82777691217124663882969105 62083268412843497912226829)
                ·
                  refine ⟨23281225654816311717085061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62083268412843497912226829 23281225654816311717085061)
                  ·
                    refine ⟨4365229810278058446953449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23281225654816311717085061 4365229810278058446953449)
                    ·
                      refine ⟨3273922357708543835215087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4365229810278058446953449 3273922357708543835215087)
                      ·
                        rfl

theorem cell23_6375941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 4, 2].length) (baseStart_6375941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375941 prefixEnd_6375941 := by exact prefixLift 6375941
  have htrace : WordTrace (prefixWord ++ tailWord_6375941) baseStart_6375941 baseEnd_6375941 := by
    simpa [prefixWord, tailWord_6375941, baseEnd_6375941] using wordTrace_append hprefix tailTrace_6375941
  have hstable : (prefixWord ++ tailWord_6375941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375941).length < 2 ^ (prefixWord ++ tailWord_6375941).sum := by decide
  have hdescent : baseEnd_6375941 < baseStart_6375941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6375944 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_6375944 : Nat := 118140960795 + 6375944 * 2 ^ 59
def prefixEnd_6375944 : Nat := 4983230072969 + 3 ^ 40 * 6375944 * 2
def baseEnd_6375944 : Nat := 3273923898150507323477573

theorem tailTrace_6375944 : CollatzResearch.WordTrace tailWord_6375944 prefixEnd_6375944 3273923898150507323477573 := by
  unfold tailWord_6375944
  simp only [CollatzResearch.WordTrace]
  refine ⟨116274891206525643693299443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155033188275367524924399257 116274891206525643693299443)
  ·
    refine ⟨174412336809788465539949165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116274891206525643693299443 174412336809788465539949165)
    ·
      refine ⟨65404626303670674577480937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174412336809788465539949165 65404626303670674577480937)
      ·
        refine ⟨49053469727753005933110703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65404626303670674577480937 49053469727753005933110703)
        ·
          refine ⟨73580204591629508899666055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49053469727753005933110703 73580204591629508899666055)
          ·
            refine ⟨110370306887444263349499083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73580204591629508899666055 110370306887444263349499083)
            ·
              refine ⟨165555460331166395024248625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110370306887444263349499083 165555460331166395024248625)
              ·
                refine ⟨124166595248374796268186469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165555460331166395024248625 124166595248374796268186469)
                ·
                  refine ⟨23281236609070274300284963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124166595248374796268186469 23281236609070274300284963)
                  ·
                    refine ⟨34921854913605411450427445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23281236609070274300284963 34921854913605411450427445)
                    ·
                      refine ⟨3273923898150507323477573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34921854913605411450427445 3273923898150507323477573)
                      ·
                        rfl

theorem cell23_6375944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_6375944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6375944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6375944 prefixEnd_6375944 := by exact prefixLift 6375944
  have htrace : WordTrace (prefixWord ++ tailWord_6375944) baseStart_6375944 baseEnd_6375944 := by
    simpa [prefixWord, tailWord_6375944, baseEnd_6375944] using wordTrace_append hprefix tailTrace_6375944
  have hstable : (prefixWord ++ tailWord_6375944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6375944).length < 2 ^ (prefixWord ++ tailWord_6375944).sum := by decide
  have hdescent : baseEnd_6375944 < baseStart_6375944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6375944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376024 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 2, 8]
def baseStart_6376024 : Nat := 118140960795 + 6376024 * 2 ^ 59
def prefixEnd_6376024 : Nat := 4983230072969 + 3 ^ 40 * 6376024 * 2
def baseEnd_6376024 : Nat := 1091321658867622336825735

theorem tailTrace_6376024 : CollatzResearch.WordTrace tailWord_6376024 prefixEnd_6376024 1091321658867622336825735 := by
  unfold tailWord_6376024
  simp only [CollatzResearch.WordTrace]
  refine ⟨116276350126380730524755563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155035133501840974033007417 116276350126380730524755563)
  ·
    refine ⟨174414525189571095787133345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116276350126380730524755563 174414525189571095787133345)
    ·
      refine ⟨130810893892178321840350009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174414525189571095787133345 130810893892178321840350009)
      ·
        refine ⟨98108170419133741380262507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130810893892178321840350009 98108170419133741380262507)
        ·
          refine ⟨147162255628700612070393761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98108170419133741380262507 147162255628700612070393761)
          ·
            refine ⟨110371691721525459052795321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147162255628700612070393761 110371691721525459052795321)
            ·
              refine ⟨82778768791144094289596491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110371691721525459052795321 82778768791144094289596491)
              ·
                refine ⟨124168153186716141434394737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82778768791144094289596491 124168153186716141434394737)
                ·
                  refine ⟨93126114890037106075796053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124168153186716141434394737 93126114890037106075796053)
                  ·
                    refine ⟨1091321658867622336825735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93126114890037106075796053 1091321658867622336825735)
                    ·
                      rfl

theorem cell23_6376024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_6376024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376024 prefixEnd_6376024 := by exact prefixLift 6376024
  have htrace : WordTrace (prefixWord ++ tailWord_6376024) baseStart_6376024 baseEnd_6376024 := by
    simpa [prefixWord, tailWord_6376024, baseEnd_6376024] using wordTrace_append hprefix tailTrace_6376024
  have hstable : (prefixWord ++ tailWord_6376024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376024).length < 2 ^ (prefixWord ++ tailWord_6376024).sum := by decide
  have hdescent : baseEnd_6376024 < baseStart_6376024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376051 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 3]
def baseStart_6376051 : Nat := 118140960795 + 6376051 * 2 ^ 59
def prefixEnd_6376051 : Nat := 4983230072969 + 3 ^ 40 * 6376051 * 2
def baseEnd_6376051 : Nat := 3273978840580538404839581

theorem tailTrace_6376051 : CollatzResearch.WordTrace tailWord_6376051 prefixEnd_6376051 3273978840580538404839581 := by
  unfold tailWord_6376051
  simp only [CollatzResearch.WordTrace]
  refine ⟨232553685023663644660744007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155035790015775763107162671 232553685023663644660744007)
  ·
    refine ⟨348830527535495466991116011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232553685023663644660744007 348830527535495466991116011)
    ·
      refine ⟨523245791303243200486674017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348830527535495466991116011 523245791303243200486674017)
      ·
        refine ⟨392434343477432400365005513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523245791303243200486674017 392434343477432400365005513)
        ·
          refine ⟨294325757608074300273754135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392434343477432400365005513 294325757608074300273754135)
          ·
            refine ⟨441488636412111450410631203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294325757608074300273754135 441488636412111450410631203)
            ·
              refine ⟨662232954618167175615946805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441488636412111450410631203 662232954618167175615946805)
              ·
                refine ⟨62084339495453172713995013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 662232954618167175615946805 62084339495453172713995013)
                ·
                  refine ⟨11640813655397469883874065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62084339495453172713995013 11640813655397469883874065)
                  ·
                    refine ⟨8730610241548102412905549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11640813655397469883874065 8730610241548102412905549)
                    ·
                      refine ⟨3273978840580538404839581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8730610241548102412905549 3273978840580538404839581)
                      ·
                        rfl

theorem cell23_6376051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 3].length) (baseStart_6376051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376051 prefixEnd_6376051 := by exact prefixLift 6376051
  have htrace : WordTrace (prefixWord ++ tailWord_6376051) baseStart_6376051 baseEnd_6376051 := by
    simpa [prefixWord, tailWord_6376051, baseEnd_6376051] using wordTrace_append hprefix tailTrace_6376051
  have hstable : (prefixWord ++ tailWord_6376051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376051).length < 2 ^ (prefixWord ++ tailWord_6376051).sum := by decide
  have hdescent : baseEnd_6376051 < baseStart_6376051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376071 : List Nat := [1, 1, 4, 2, 1, 2, 1, 5, 6]
def baseStart_6376071 : Nat := 118140960795 + 6376071 * 2 ^ 59
def prefixEnd_6376071 : Nat := 4983230072969 + 3 ^ 40 * 6376071 * 2
def baseEnd_6376071 : Nat := 363776567799292036287721

theorem tailTrace_6376071 : CollatzResearch.WordTrace tailWord_6376071 prefixEnd_6376071 363776567799292036287721 := by
  unfold tailWord_6376071
  simp only [CollatzResearch.WordTrace]
  refine ⟨232554414483591188076472067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155036276322394125384314711 232554414483591188076472067)
  ·
    refine ⟨348831621725386782114708101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232554414483591188076472067 348831621725386782114708101)
    ·
      refine ⟨65405929073510021646507769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348831621725386782114708101 65405929073510021646507769)
      ·
        refine ⟨49054446805132516234880827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65405929073510021646507769 49054446805132516234880827)
        ·
          refine ⟨73581670207698774352321241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49054446805132516234880827 73581670207698774352321241)
          ·
            refine ⟨55186252655774080764240931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73581670207698774352321241 55186252655774080764240931)
            ·
              refine ⟨82779378983661121146361397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55186252655774080764240931 82779378983661121146361397)
              ·
                refine ⟨7760566779718230107471381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82779378983661121146361397 7760566779718230107471381)
                ·
                  refine ⟨363776567799292036287721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7760566779718230107471381 363776567799292036287721)
                  ·
                    rfl

theorem cell23_6376071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 6].length) (baseStart_6376071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376071 prefixEnd_6376071 := by exact prefixLift 6376071
  have htrace : WordTrace (prefixWord ++ tailWord_6376071) baseStart_6376071 baseEnd_6376071 := by
    simpa [prefixWord, tailWord_6376071, baseEnd_6376071] using wordTrace_append hprefix tailTrace_6376071
  have hstable : (prefixWord ++ tailWord_6376071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376071).length < 2 ^ (prefixWord ++ tailWord_6376071).sum := by decide
  have hdescent : baseEnd_6376071 < baseStart_6376071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376092 : List Nat := [2, 2, 3, 2, 2, 2, 2, 3, 1, 4]
def baseStart_6376092 : Nat := 118140960795 + 6376092 * 2 ^ 59
def prefixEnd_6376092 : Nat := 4983230072969 + 3 ^ 40 * 6376092 * 2
def baseEnd_6376092 : Nat := 1091333297762457581475631

theorem tailTrace_6376092 : CollatzResearch.WordTrace tailWord_6376092 prefixEnd_6376092 1091333297762457581475631 := by
  unfold tailWord_6376092
  simp only [CollatzResearch.WordTrace]
  refine ⟨116277590208257554331493265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155036786944343405775324353 116277590208257554331493265)
  ·
    refine ⟨87208192656193165748619949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116277590208257554331493265 87208192656193165748619949)
    ·
      refine ⟨32703072246072437155732481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87208192656193165748619949 32703072246072437155732481)
      ·
        refine ⟨24527304184554327866799361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32703072246072437155732481 24527304184554327866799361)
        ·
          refine ⟨18395478138415745900099521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24527304184554327866799361 18395478138415745900099521)
          ·
            refine ⟨13796608603811809425074641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18395478138415745900099521 13796608603811809425074641)
            ·
              refine ⟨10347456452858857068805981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13796608603811809425074641 10347456452858857068805981)
              ·
                refine ⟨3880296169822071400802243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10347456452858857068805981 3880296169822071400802243)
                ·
                  refine ⟨5820444254733107101203365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3880296169822071400802243 5820444254733107101203365)
                  ·
                    refine ⟨1091333297762457581475631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5820444254733107101203365 1091333297762457581475631)
                    ·
                      rfl

theorem cell23_6376092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_6376092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376092 prefixEnd_6376092 := by exact prefixLift 6376092
  have htrace : WordTrace (prefixWord ++ tailWord_6376092) baseStart_6376092 baseEnd_6376092 := by
    simpa [prefixWord, tailWord_6376092, baseEnd_6376092] using wordTrace_append hprefix tailTrace_6376092
  have hstable : (prefixWord ++ tailWord_6376092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376092).length < 2 ^ (prefixWord ++ tailWord_6376092).sum := by decide
  have hdescent : baseEnd_6376092 < baseStart_6376092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376115 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 3, 1, 3]
def baseStart_6376115 : Nat := 118140960795 + 6376115 * 2 ^ 59
def prefixEnd_6376115 : Nat := 4983230072969 + 3 ^ 40 * 6376115 * 2
def baseEnd_6376115 : Nat := 3274011703342426154439287

theorem tailTrace_6376115 : CollatzResearch.WordTrace tailWord_6376115 prefixEnd_6376115 3274011703342426154439287 := by
  unfold tailWord_6376115
  simp only [CollatzResearch.WordTrace]
  refine ⟨232556019295431783591073799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155037346196954522394049199 232556019295431783591073799)
  ·
    refine ⟨348834028943147675386610699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232556019295431783591073799 348834028943147675386610699)
    ·
      refine ⟨523251043414721513079916049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348834028943147675386610699 523251043414721513079916049)
      ·
        refine ⟨392438282561041134809937037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523251043414721513079916049 392438282561041134809937037)
        ·
          refine ⟨147164355960390425553726389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392438282561041134809937037 147164355960390425553726389)
          ·
            refine ⟨13796658371286602395661849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147164355960390425553726389 13796658371286602395661849)
            ·
              refine ⟨10347493778464951796746387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13796658371286602395661849 10347493778464951796746387)
              ·
                refine ⟨15521240667697427695119581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10347493778464951796746387 15521240667697427695119581)
                ·
                  refine ⟨5820465250386535385669843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15521240667697427695119581 5820465250386535385669843)
                  ·
                    refine ⟨8730697875579803078504765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5820465250386535385669843 8730697875579803078504765)
                    ·
                      refine ⟨3274011703342426154439287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8730697875579803078504765 3274011703342426154439287)
                      ·
                        rfl

theorem cell23_6376115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 1, 3].length) (baseStart_6376115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376115 prefixEnd_6376115 := by exact prefixLift 6376115
  have htrace : WordTrace (prefixWord ++ tailWord_6376115) baseStart_6376115 baseEnd_6376115 := by
    simpa [prefixWord, tailWord_6376115, baseEnd_6376115] using wordTrace_append hprefix tailTrace_6376115
  have hstable : (prefixWord ++ tailWord_6376115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376115).length < 2 ^ (prefixWord ++ tailWord_6376115).sum := by decide
  have hdescent : baseEnd_6376115 < baseStart_6376115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376161 : List Nat := [1, 2, 3, 1, 4, 1, 11]
def baseStart_6376161 : Nat := 118140960795 + 6376161 * 2 ^ 59
def prefixEnd_6376161 : Nat := 4983230072969 + 3 ^ 40 * 6376161 * 2
def baseEnd_6376161 : Nat := 40420189178426333018075

theorem tailTrace_6376161 : CollatzResearch.WordTrace tailWord_6376161 prefixEnd_6376161 40420189178426333018075 := by
  unfold tailWord_6376161
  simp only [CollatzResearch.WordTrace]
  refine ⟨232557697053265133447248337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155038464702176755631498891 232557697053265133447248337)
  ·
    refine ⟨174418272789948850085436253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232557697053265133447248337 174418272789948850085436253)
    ·
      refine ⟨65406852296230818782038595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174418272789948850085436253 65406852296230818782038595)
      ·
        refine ⟨98110278444346228173057893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65406852296230818782038595 98110278444346228173057893)
        ·
          refine ⟨18395677208314917782448355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98110278444346228173057893 18395677208314917782448355)
          ·
            refine ⟨27593515812472376673672533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18395677208314917782448355 27593515812472376673672533)
            ·
              refine ⟨40420189178426333018075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27593515812472376673672533 40420189178426333018075)
              ·
                rfl

theorem cell23_6376161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 11].length) (baseStart_6376161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376161 prefixEnd_6376161 := by exact prefixLift 6376161
  have htrace : WordTrace (prefixWord ++ tailWord_6376161) baseStart_6376161 baseEnd_6376161 := by
    simpa [prefixWord, tailWord_6376161, baseEnd_6376161] using wordTrace_append hprefix tailTrace_6376161
  have hstable : (prefixWord ++ tailWord_6376161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376161).length < 2 ^ (prefixWord ++ tailWord_6376161).sum := by decide
  have hdescent : baseEnd_6376161 < baseStart_6376161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376178 : List Nat := [3, 2, 1, 3, 1, 3, 2, 8]
def baseStart_6376178 : Nat := 118140960795 + 6376178 * 2 ^ 59
def prefixEnd_6376178 : Nat := 4983230072969 + 3 ^ 40 * 6376178 * 2
def baseEnd_6376178 : Nat := 121260890837913311405611

theorem tailTrace_6376178 : CollatzResearch.WordTrace tailWord_6376178 prefixEnd_6376178 121260890837913311405611 := by
  unfold tailWord_6376178
  simp only [CollatzResearch.WordTrace]
  refine ⟨58139579273550886337654297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155038878062802363567078125 58139579273550886337654297)
  ·
    refine ⟨43604684455163164753240723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58139579273550886337654297 43604684455163164753240723)
    ·
      refine ⟨65407026682744747129861085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43604684455163164753240723 65407026682744747129861085)
      ·
        refine ⟨24527635006029280173697907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65407026682744747129861085 24527635006029280173697907)
        ·
          refine ⟨36791452509043920260546861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24527635006029280173697907 36791452509043920260546861)
          ·
            refine ⟨13796794690891470097705073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36791452509043920260546861 13796794690891470097705073)
            ·
              refine ⟨10347596018168602573278805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13796794690891470097705073 10347596018168602573278805)
              ·
                refine ⟨121260890837913311405611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10347596018168602573278805 121260890837913311405611)
                ·
                  rfl

theorem cell23_6376178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 8].length) (baseStart_6376178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376178 prefixEnd_6376178 := by exact prefixLift 6376178
  have htrace : WordTrace (prefixWord ++ tailWord_6376178) baseStart_6376178 baseEnd_6376178 := by
    simpa [prefixWord, tailWord_6376178, baseEnd_6376178] using wordTrace_append hprefix tailTrace_6376178
  have hstable : (prefixWord ++ tailWord_6376178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376178).length < 2 ^ (prefixWord ++ tailWord_6376178).sum := by decide
  have hdescent : baseEnd_6376178 < baseStart_6376178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376201 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 1, 4, 5]
def baseStart_6376201 : Nat := 118140960795 + 6376201 * 2 ^ 59
def prefixEnd_6376201 : Nat := 4983230072969 + 3 ^ 40 * 6376201 * 2
def baseEnd_6376201 : Nat := 3274055862678712817963891

theorem tailTrace_6376201 : CollatzResearch.WordTrace tailWord_6376201 prefixEnd_6376201 3274055862678712817963891 := by
  unfold tailWord_6376201
  simp only [CollatzResearch.WordTrace]
  refine ⟨232559155973120220278704457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155039437315413480185802971 232559155973120220278704457)
  ·
    refine ⟨174419366979840165209028343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232559155973120220278704457 174419366979840165209028343)
    ·
      refine ⟨261629050469760247813542515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174419366979840165209028343 261629050469760247813542515)
      ·
        refine ⟨392443575704640371720313773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261629050469760247813542515 392443575704640371720313773)
        ·
          refine ⟨147166340889240139395117665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392443575704640371720313773 147166340889240139395117665)
          ·
            refine ⟨110374755666930104546338249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147166340889240139395117665 110374755666930104546338249)
            ·
              refine ⟨82781066750197578409753687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110374755666930104546338249 82781066750197578409753687)
              ·
                refine ⟨124171600125296367614630531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82781066750197578409753687 124171600125296367614630531)
                ·
                  refine ⟨186257400187944551421945797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124171600125296367614630531 186257400187944551421945797)
                  ·
                    refine ⟨34923262535239603391614837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 186257400187944551421945797 34923262535239603391614837)
                    ·
                      refine ⟨3274055862678712817963891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34923262535239603391614837 3274055862678712817963891)
                      ·
                        rfl

theorem cell23_6376201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_6376201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376201 prefixEnd_6376201 := by exact prefixLift 6376201
  have htrace : WordTrace (prefixWord ++ tailWord_6376201) baseStart_6376201 baseEnd_6376201 := by
    simpa [prefixWord, tailWord_6376201, baseEnd_6376201] using wordTrace_append hprefix tailTrace_6376201
  have hstable : (prefixWord ++ tailWord_6376201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376201).length < 2 ^ (prefixWord ++ tailWord_6376201).sum := by decide
  have hdescent : baseEnd_6376201 < baseStart_6376201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376248 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 2, 4, 3]
def baseStart_6376248 : Nat := 118140960795 + 6376248 * 2 ^ 59
def prefixEnd_6376248 : Nat := 4983230072969 + 3 ^ 40 * 6376248 * 2
def baseEnd_6376248 : Nat := 3274079996269474134076175

theorem tailTrace_6376248 : CollatzResearch.WordTrace tailWord_6376248 prefixEnd_6376248 3274079996269474134076175 := by
  unfold tailWord_6376248
  simp only [CollatzResearch.WordTrace]
  refine ⟨116280435101974973652832699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155040580135966631537110265 116280435101974973652832699)
  ·
    refine ⟨174420652652962460479249049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116280435101974973652832699 174420652652962460479249049)
    ·
      refine ⟨130815489489721845359436787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174420652652962460479249049 130815489489721845359436787)
      ·
        refine ⟨196223234234582768039155181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130815489489721845359436787 196223234234582768039155181)
        ·
          refine ⟨73583712837968538014683193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196223234234582768039155181 73583712837968538014683193)
          ·
            refine ⟨55187784628476403511012395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73583712837968538014683193 55187784628476403511012395)
            ·
              refine ⟨82781676942714605266518593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55187784628476403511012395 82781676942714605266518593)
              ·
                refine ⟨62086257707035953949888945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82781676942714605266518593 62086257707035953949888945)
                ·
                  refine ⟨46564693280276965462416709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62086257707035953949888945 46564693280276965462416709)
                  ·
                    refine ⟨8730879990051931024203133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46564693280276965462416709 8730879990051931024203133)
                    ·
                      refine ⟨3274079996269474134076175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8730879990051931024203133 3274079996269474134076175)
                      ·
                        rfl

theorem cell23_6376248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_6376248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376248 prefixEnd_6376248 := by exact prefixLift 6376248
  have htrace : WordTrace (prefixWord ++ tailWord_6376248) baseStart_6376248 baseEnd_6376248 := by
    simpa [prefixWord, tailWord_6376248, baseEnd_6376248] using wordTrace_append hprefix tailTrace_6376248
  have hstable : (prefixWord ++ tailWord_6376248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376248).length < 2 ^ (prefixWord ++ tailWord_6376248).sum := by decide
  have hdescent : baseEnd_6376248 < baseStart_6376248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376279 : List Nat := [1, 1, 3, 2, 4, 1, 3, 2, 2, 2, 2]
def baseStart_6376279 : Nat := 118140960795 + 6376279 * 2 ^ 59
def prefixEnd_6376279 : Nat := 4983230072969 + 3 ^ 40 * 6376279 * 2
def baseEnd_6376279 : Nat := 3274095914169763512788533

theorem tailTrace_6376279 : CollatzResearch.WordTrace tailWord_6376279 prefixEnd_6376279 3274095914169763512788533 := by
  unfold tailWord_6376279
  simp only [CollatzResearch.WordTrace]
  refine ⟨232562000866837639600043891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155041333911225093066695927 232562000866837639600043891)
  ·
    refine ⟨348843001300256459400065837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232562000866837639600043891 348843001300256459400065837)
    ·
      refine ⟨130816125487596172275024689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348843001300256459400065837 130816125487596172275024689)
      ·
        refine ⟨98112094115697129206268517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130816125487596172275024689 98112094115697129206268517)
        ·
          refine ⟨18396017646693211726175347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98112094115697129206268517 18396017646693211726175347)
          ·
            refine ⟨27594026470039817589263021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18396017646693211726175347 27594026470039817589263021)
            ·
              refine ⟨10347759926264931595973633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27594026470039817589263021 10347759926264931595973633)
              ·
                refine ⟨7760819944698698696980225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10347759926264931595973633 7760819944698698696980225)
                ·
                  refine ⟨5820614958524024022735169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7760819944698698696980225 5820614958524024022735169)
                  ·
                    refine ⟨4365461218893018017051377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5820614958524024022735169 4365461218893018017051377)
                    ·
                      refine ⟨3274095914169763512788533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4365461218893018017051377 3274095914169763512788533)
                      ·
                        rfl

theorem cell23_6376279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_6376279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376279 prefixEnd_6376279 := by exact prefixLift 6376279
  have htrace : WordTrace (prefixWord ++ tailWord_6376279) baseStart_6376279 baseEnd_6376279 := by
    simpa [prefixWord, tailWord_6376279, baseEnd_6376279] using wordTrace_append hprefix tailTrace_6376279
  have hstable : (prefixWord ++ tailWord_6376279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376279).length < 2 ^ (prefixWord ++ tailWord_6376279).sum := by decide
  have hdescent : baseEnd_6376279 < baseStart_6376279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376295 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_6376295 : Nat := 118140960795 + 6376295 * 2 ^ 59
def prefixEnd_6376295 : Nat := 4983230072969 + 3 ^ 40 * 6376295 * 2
def baseEnd_6376295 : Nat := 3274104129860235450188459

theorem tailTrace_6376295 : CollatzResearch.WordTrace tailWord_6376295 prefixEnd_6376295 3274104129860235450188459 := by
  unfold tailWord_6376295
  simp only [CollatzResearch.WordTrace]
  refine ⟨232562584434779674332626339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155041722956519782888417559 232562584434779674332626339)
  ·
    refine ⟨348843876652169511498939509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232562584434779674332626339 348843876652169511498939509)
    ·
      refine ⟨32704113436140891703025579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 348843876652169511498939509 32704113436140891703025579)
      ·
        refine ⟨49056170154211337554538369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32704113436140891703025579 49056170154211337554538369)
        ·
          refine ⟨36792127615658503165903777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49056170154211337554538369 36792127615658503165903777)
          ·
            refine ⟨27594095711743877374427833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36792127615658503165903777 27594095711743877374427833)
            ·
              refine ⟨20695571783807908030820875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27594095711743877374427833 20695571783807908030820875)
              ·
                refine ⟨31043357675711862046231313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20695571783807908030820875 31043357675711862046231313)
                ·
                  refine ⟨23282518256783896534673485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31043357675711862046231313 23282518256783896534673485)
                  ·
                    refine ⟨8730944346293961200502557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23282518256783896534673485 8730944346293961200502557)
                    ·
                      refine ⟨3274104129860235450188459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8730944346293961200502557 3274104129860235450188459)
                      ·
                        rfl

theorem cell23_6376295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_6376295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376295 prefixEnd_6376295 := by exact prefixLift 6376295
  have htrace : WordTrace (prefixWord ++ tailWord_6376295) baseStart_6376295 baseEnd_6376295 := by
    simpa [prefixWord, tailWord_6376295, baseEnd_6376295] using wordTrace_append hprefix tailTrace_6376295
  have hstable : (prefixWord ++ tailWord_6376295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376295).length < 2 ^ (prefixWord ++ tailWord_6376295).sum := by decide
  have hdescent : baseEnd_6376295 < baseStart_6376295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376296 : List Nat := [2, 1, 4, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_6376296 : Nat := 118140960795 + 6376296 * 2 ^ 59
def prefixEnd_6376296 : Nat := 4983230072969 + 3 ^ 40 * 6376296 * 2
def baseEnd_6376296 : Nat := 3274104643340889946275955

theorem tailTrace_6376296 : CollatzResearch.WordTrace tailWord_6376296 prefixEnd_6376296 3274104643340889946275955 := by
  unfold tailWord_6376296
  simp only [CollatzResearch.WordTrace]
  refine ⟨116281310453888025751706371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155041747271850701002275161 116281310453888025751706371)
  ·
    refine ⟨174421965680832038627559557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116281310453888025751706371 174421965680832038627559557)
    ·
      refine ⟨32704118565156007242667417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174421965680832038627559557 32704118565156007242667417)
      ·
        refine ⟨24528088923867005432000563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32704118565156007242667417 24528088923867005432000563)
        ·
          refine ⟨36792133385800508148000845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24528088923867005432000563 36792133385800508148000845)
          ·
            refine ⟨13797050019675190555500317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36792133385800508148000845 13797050019675190555500317)
            ·
              refine ⟨5173893757378196458312619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13797050019675190555500317 5173893757378196458312619)
              ·
                refine ⟨7760840636067294687468929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5173893757378196458312619 7760840636067294687468929)
                ·
                  refine ⟨5820630477050471015601697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7760840636067294687468929 5820630477050471015601697)
                  ·
                    refine ⟨4365472857787853261701273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5820630477050471015601697 4365472857787853261701273)
                    ·
                      refine ⟨3274104643340889946275955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4365472857787853261701273 3274104643340889946275955)
                      ·
                        rfl

theorem cell23_6376296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_6376296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376296 prefixEnd_6376296 := by exact prefixLift 6376296
  have htrace : WordTrace (prefixWord ++ tailWord_6376296) baseStart_6376296 baseEnd_6376296 := by
    simpa [prefixWord, tailWord_6376296, baseEnd_6376296] using wordTrace_append hprefix tailTrace_6376296
  have hstable : (prefixWord ++ tailWord_6376296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376296).length < 2 ^ (prefixWord ++ tailWord_6376296).sum := by decide
  have hdescent : baseEnd_6376296 < baseStart_6376296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376392 : List Nat := [2, 1, 3, 1, 5, 1, 2, 2, 6]
def baseStart_6376392 : Nat := 118140960795 + 6376392 * 2 ^ 59
def prefixEnd_6376392 : Nat := 4983230072969 + 3 ^ 40 * 6376392 * 2
def baseEnd_6376392 : Nat := 363794881942635730075057

theorem tailTrace_6376392 : CollatzResearch.WordTrace tailWord_6376392 prefixEnd_6376392 363794881942635730075057 := by
  unfold tailWord_6376392
  simp only [CollatzResearch.WordTrace]
  refine ⟨116283061157714129949453715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155044081543618839932604953 116283061157714129949453715)
  ·
    refine ⟨174424591736571194924180573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116283061157714129949453715 174424591736571194924180573)
    ·
      refine ⟨65409221901214198096567715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174424591736571194924180573 65409221901214198096567715)
      ·
        refine ⟨98113832851821297144851573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65409221901214198096567715 98113832851821297144851573)
        ·
          refine ⟨9198171829858246607329835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98113832851821297144851573 9198171829858246607329835)
          ·
            refine ⟨13797257744787369910994753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9198171829858246607329835 13797257744787369910994753)
            ·
              refine ⟨10347943308590527433246065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13797257744787369910994753 10347943308590527433246065)
              ·
                refine ⟨7760957481442895574934549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10347943308590527433246065 7760957481442895574934549)
                ·
                  refine ⟨363794881942635730075057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7760957481442895574934549 363794881942635730075057)
                  ·
                    rfl

theorem cell23_6376392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 6].length) (baseStart_6376392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376392 prefixEnd_6376392 := by exact prefixLift 6376392
  have htrace : WordTrace (prefixWord ++ tailWord_6376392) baseStart_6376392 baseEnd_6376392 := by
    simpa [prefixWord, tailWord_6376392, baseEnd_6376392] using wordTrace_append hprefix tailTrace_6376392
  have hstable : (prefixWord ++ tailWord_6376392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376392).length < 2 ^ (prefixWord ++ tailWord_6376392).sum := by decide
  have hdescent : baseEnd_6376392 < baseStart_6376392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376445 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_6376445 : Nat := 118140960795 + 6376445 * 2 ^ 59
def prefixEnd_6376445 : Nat := 4983230072969 + 3 ^ 40 * 6376445 * 2
def baseEnd_6376445 : Nat := 3274181151958409863312769

theorem tailTrace_6376445 : CollatzResearch.WordTrace tailWord_6376445 prefixEnd_6376445 3274181151958409863312769 := by
  unfold tailWord_6376445
  simp only [CollatzResearch.WordTrace]
  refine ⟨232568055384236249950586789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155045370256157499967057859 232568055384236249950586789)
  ·
    refine ⟨43606510384544296865735023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232568055384236249950586789 43606510384544296865735023)
    ·
      refine ⟨65409765576816445298602535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43606510384544296865735023 65409765576816445298602535)
      ·
        refine ⟨98114648365224667947903803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65409765576816445298602535 98114648365224667947903803)
        ·
          refine ⟨147171972547837001921855705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98114648365224667947903803 147171972547837001921855705)
          ·
            refine ⟨110378979410877751441391779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147171972547837001921855705 110378979410877751441391779)
            ·
              refine ⟨165568469116316627162087669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110378979410877751441391779 165568469116316627162087669)
              ·
                refine ⟨15522043979654683796445719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165568469116316627162087669 15522043979654683796445719)
                ·
                  refine ⟨23283065969482025694668579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15522043979654683796445719 23283065969482025694668579)
                  ·
                    refine ⟨34924598954223038542002869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23283065969482025694668579 34924598954223038542002869)
                    ·
                      refine ⟨3274181151958409863312769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34924598954223038542002869 3274181151958409863312769)
                      ·
                        rfl

theorem cell23_6376445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_6376445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376445 prefixEnd_6376445 := by exact prefixLift 6376445
  have htrace : WordTrace (prefixWord ++ tailWord_6376445) baseStart_6376445 baseEnd_6376445 := by
    simpa [prefixWord, tailWord_6376445, baseEnd_6376445] using wordTrace_append hprefix tailTrace_6376445
  have hstable : (prefixWord ++ tailWord_6376445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376445).length < 2 ^ (prefixWord ++ tailWord_6376445).sum := by decide
  have hdescent : baseEnd_6376445 < baseStart_6376445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376455 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_6376455 : Nat := 118140960795 + 6376455 * 2 ^ 59
def prefixEnd_6376455 : Nat := 4983230072969 + 3 ^ 40 * 6376455 * 2
def baseEnd_6376455 : Nat := 3274186286764954824187723

theorem tailTrace_6376455 : CollatzResearch.WordTrace tailWord_6376455 prefixEnd_6376455 3274186286764954824187723 := by
  unfold tailWord_6376455
  simp only [CollatzResearch.WordTrace]
  refine ⟨232568420114200021658450819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155045613409466681105633879 232568420114200021658450819)
  ·
    refine ⟨348852630171300032487676229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232568420114200021658450819 348852630171300032487676229)
    ·
      refine ⟨65409868157118756091439293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348852630171300032487676229 65409868157118756091439293)
      ·
        refine ⟨24528700558919533534289735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65409868157118756091439293 24528700558919533534289735)
        ·
          refine ⟨36793050838379300301434603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24528700558919533534289735 36793050838379300301434603)
          ·
            refine ⟨55189576257568950452151905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36793050838379300301434603 55189576257568950452151905)
            ·
              refine ⟨41392182193176712839113929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55189576257568950452151905 41392182193176712839113929)
              ·
                refine ⟨31044136644882534629335447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41392182193176712839113929 31044136644882534629335447)
                ·
                  refine ⟨46566204967323801944003171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31044136644882534629335447 46566204967323801944003171)
                  ·
                    refine ⟨69849307450985702916004757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46566204967323801944003171 69849307450985702916004757)
                    ·
                      refine ⟨3274186286764954824187723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69849307450985702916004757 3274186286764954824187723)
                      ·
                        rfl

theorem cell23_6376455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_6376455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376455 prefixEnd_6376455 := by exact prefixLift 6376455
  have htrace : WordTrace (prefixWord ++ tailWord_6376455) baseStart_6376455 baseEnd_6376455 := by
    simpa [prefixWord, tailWord_6376455, baseEnd_6376455] using wordTrace_append hprefix tailTrace_6376455
  have hstable : (prefixWord ++ tailWord_6376455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376455).length < 2 ^ (prefixWord ++ tailWord_6376455).sum := by decide
  have hdescent : baseEnd_6376455 < baseStart_6376455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376459 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 3, 2, 2]
def baseStart_6376459 : Nat := 118140960795 + 6376459 * 2 ^ 59
def prefixEnd_6376459 : Nat := 4983230072969 + 3 ^ 40 * 6376459 * 2
def baseEnd_6376459 : Nat := 3274188340687572808537705

theorem tailTrace_6376459 : CollatzResearch.WordTrace tailWord_6376459 prefixEnd_6376459 3274188340687572808537705 := by
  unfold tailWord_6376459
  simp only [CollatzResearch.WordTrace]
  refine ⟨232568566006185530341596431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155045710670790353561064287 232568566006185530341596431)
  ·
    refine ⟨348852849009278295512394647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232568566006185530341596431 348852849009278295512394647)
    ·
      refine ⟨523279273513917443268591971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348852849009278295512394647 523279273513917443268591971)
      ·
        refine ⟨784918910270876164902887957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523279273513917443268591971 784918910270876164902887957)
        ·
          refine ⟨36793073918947320229822873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 784918910270876164902887957 36793073918947320229822873)
          ·
            refine ⟨27594805439210490172367155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36793073918947320229822873 27594805439210490172367155)
            ·
              refine ⟨41392208158815735258550733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27594805439210490172367155 41392208158815735258550733)
              ·
                refine ⟨15522078059555900721956525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41392208158815735258550733 15522078059555900721956525)
                ·
                  refine ⟨5820779272333462770733697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15522078059555900721956525 5820779272333462770733697)
                  ·
                    refine ⟨4365584454250097078050273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5820779272333462770733697 4365584454250097078050273)
                    ·
                      refine ⟨3274188340687572808537705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4365584454250097078050273 3274188340687572808537705)
                      ·
                        rfl

theorem cell23_6376459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 2, 2].length) (baseStart_6376459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376459 prefixEnd_6376459 := by exact prefixLift 6376459
  have htrace : WordTrace (prefixWord ++ tailWord_6376459) baseStart_6376459 baseEnd_6376459 := by
    simpa [prefixWord, tailWord_6376459, baseEnd_6376459] using wordTrace_append hprefix tailTrace_6376459
  have hstable : (prefixWord ++ tailWord_6376459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376459).length < 2 ^ (prefixWord ++ tailWord_6376459).sum := by decide
  have hdescent : baseEnd_6376459 < baseStart_6376459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376462 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_6376462 : Nat := 118140960795 + 6376462 * 2 ^ 59
def prefixEnd_6376462 : Nat := 4983230072969 + 3 ^ 40 * 6376462 * 2
def baseEnd_6376462 : Nat := 3274189881129536296800191

theorem tailTrace_6376462 : CollatzResearch.WordTrace tailWord_6376462 prefixEnd_6376462 3274189881129536296800191 := by
  unfold tailWord_6376462
  simp only [CollatzResearch.WordTrace]
  refine ⟨29071084428146832731744455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155045783616783107902637093 29071084428146832731744455)
  ·
    refine ⟨43606626642220249097616683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29071084428146832731744455 43606626642220249097616683)
    ·
      refine ⟨65409939963330373646425025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43606626642220249097616683 65409939963330373646425025)
      ·
        refine ⟨49057454972497780234818769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65409939963330373646425025 49057454972497780234818769)
        ·
          refine ⟨36793091229373335176114077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49057454972497780234818769 36793091229373335176114077)
          ·
            refine ⟨13797409211015000691042779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36793091229373335176114077 13797409211015000691042779)
            ·
              refine ⟨20696113816522501036564169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13797409211015000691042779 20696113816522501036564169)
              ·
                refine ⟨15522085362391875777423127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20696113816522501036564169 15522085362391875777423127)
                ·
                  refine ⟨23283128043587813666134691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15522085362391875777423127 23283128043587813666134691)
                  ·
                    refine ⟨34924692065381720499202037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23283128043587813666134691 34924692065381720499202037)
                    ·
                      refine ⟨3274189881129536296800191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34924692065381720499202037 3274189881129536296800191)
                      ·
                        rfl

theorem cell23_6376462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_6376462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376462 prefixEnd_6376462 := by exact prefixLift 6376462
  have htrace : WordTrace (prefixWord ++ tailWord_6376462) baseStart_6376462 baseEnd_6376462 := by
    simpa [prefixWord, tailWord_6376462, baseEnd_6376462] using wordTrace_append hprefix tailTrace_6376462
  have hstable : (prefixWord ++ tailWord_6376462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376462).length < 2 ^ (prefixWord ++ tailWord_6376462).sum := by decide
  have hdescent : baseEnd_6376462 < baseStart_6376462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376472 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 1, 2, 4]
def baseStart_6376472 : Nat := 118140960795 + 6376472 * 2 ^ 59
def prefixEnd_6376472 : Nat := 4983230072969 + 3 ^ 40 * 6376472 * 2
def baseEnd_6376472 : Nat := 3274195015936081257675145

theorem tailTrace_6376472 : CollatzResearch.WordTrace tailWord_6376472 prefixEnd_6376472 3274195015936081257675145 := by
  unfold tailWord_6376472
  simp only [CollatzResearch.WordTrace]
  refine ⟨116284520077569216780909835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155046026770092289041213113 116284520077569216780909835)
  ·
    refine ⟨174426780116353825171364753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116284520077569216780909835 174426780116353825171364753)
    ·
      refine ⟨130820085087265368878523565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174426780116353825171364753 130820085087265368878523565)
      ·
        refine ⟨49057531907724513329446337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130820085087265368878523565 49057531907724513329446337)
        ·
          refine ⟨36793148930793384997084753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49057531907724513329446337 36793148930793384997084753)
          ·
            refine ⟨27594861698095038747813565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36793148930793384997084753 27594861698095038747813565)
            ·
              refine ⟨10348073136785639530430087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27594861698095038747813565 10348073136785639530430087)
              ·
                refine ⟨15522109705178459295645131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10348073136785639530430087 15522109705178459295645131)
                ·
                  refine ⟨23283164557767688943467697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15522109705178459295645131 23283164557767688943467697)
                  ·
                    refine ⟨17462373418325766707600773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23283164557767688943467697 17462373418325766707600773)
                    ·
                      refine ⟨3274195015936081257675145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17462373418325766707600773 3274195015936081257675145)
                      ·
                        rfl

theorem cell23_6376472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_6376472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6376472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6376472 prefixEnd_6376472 := by exact prefixLift 6376472
  have htrace : WordTrace (prefixWord ++ tailWord_6376472) baseStart_6376472 baseEnd_6376472 := by
    simpa [prefixWord, tailWord_6376472, baseEnd_6376472] using wordTrace_append hprefix tailTrace_6376472
  have hstable : (prefixWord ++ tailWord_6376472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376472).length < 2 ^ (prefixWord ++ tailWord_6376472).sum := by decide
  have hdescent : baseEnd_6376472 < baseStart_6376472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
