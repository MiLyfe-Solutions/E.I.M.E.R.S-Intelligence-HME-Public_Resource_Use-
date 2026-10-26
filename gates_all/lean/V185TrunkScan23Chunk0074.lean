import V185TrunkScan23Chunk0073

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_439576 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 3, 2, 2]
def baseStart_439576 : Nat := 118140960795 + 439576 * 2 ^ 59
def prefixEnd_439576 : Nat := 4983230072969 + 3 ^ 40 * 439576 * 2
def baseEnd_439576 : Nat := 225713772180877390578433

theorem tailTrace_439576 : CollatzResearch.WordTrace tailWord_439576 prefixEnd_439576 225713772180877390578433 := by
  unfold tailWord_439576
  simp only [CollatzResearch.WordTrace]
  refine ⟨8016326927749350224497291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10688435903665800299329721 8016326927749350224497291)
  ·
    refine ⟨12024490391624025336745937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8016326927749350224497291 12024490391624025336745937)
    ·
      refine ⟨9018367793718019002559453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12024490391624025336745937 9018367793718019002559453)
      ·
        refine ⟨3381887922644257125959795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9018367793718019002559453 3381887922644257125959795)
        ·
          refine ⟨5072831883966385688939693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3381887922644257125959795 5072831883966385688939693)
          ·
            refine ⟨1902311956487394633352385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5072831883966385688939693 1902311956487394633352385)
            ·
              refine ⟨1426733967365545975014289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1902311956487394633352385 1426733967365545975014289)
              ·
                refine ⟨1070050475524159481260717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1426733967365545975014289 1070050475524159481260717)
                ·
                  refine ⟨401268928321559805472769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070050475524159481260717 401268928321559805472769)
                  ·
                    refine ⟨300951696241169854104577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 401268928321559805472769 300951696241169854104577)
                    ·
                      refine ⟨225713772180877390578433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 300951696241169854104577 225713772180877390578433)
                      ·
                        rfl

theorem cell23_439576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_439576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439576 prefixEnd_439576 := by exact prefixLift 439576
  have htrace : WordTrace (prefixWord ++ tailWord_439576) baseStart_439576 baseEnd_439576 := by
    simpa [prefixWord, tailWord_439576, baseEnd_439576] using wordTrace_append hprefix tailTrace_439576
  have hstable : (prefixWord ++ tailWord_439576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439576).length < 2 ^ (prefixWord ++ tailWord_439576).sum := by decide
  have hdescent : baseEnd_439576 < baseStart_439576 := by decide
  rcases family_descends (prefixWord ++ tailWord_439576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439595 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 6, 7]
def baseStart_439595 : Nat := 118140960795 + 439595 * 2 ^ 59
def prefixEnd_439595 : Nat := 4983230072969 + 3 ^ 40 * 439595 * 2
def baseEnd_439595 : Nat := 75241176104437605413615

theorem tailTrace_439595 : CollatzResearch.WordTrace tailWord_439595 prefixEnd_439595 75241176104437605413615 := by
  unfold tailWord_439595
  simp only [CollatzResearch.WordTrace]
  refine ⟨16033346842429866693936239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10688897894953244462624159 16033346842429866693936239)
  ·
    refine ⟨24050020263644800040904359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16033346842429866693936239 24050020263644800040904359)
    ·
      refine ⟨36075030395467200061356539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24050020263644800040904359 36075030395467200061356539)
      ·
        refine ⟨54112545593200800092034809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36075030395467200061356539 54112545593200800092034809)
        ·
          refine ⟨40584409194900600069026107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54112545593200800092034809 40584409194900600069026107)
          ·
            refine ⟨60876613792350900103539161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40584409194900600069026107 60876613792350900103539161)
            ·
              refine ⟨45657460344263175077654371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60876613792350900103539161 45657460344263175077654371)
              ·
                refine ⟨68486190516394762616481557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45657460344263175077654371 68486190516394762616481557)
                ·
                  refine ⟨3210290180456004497647573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68486190516394762616481557 3210290180456004497647573)
                  ·
                    refine ⟨75241176104437605413615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3210290180456004497647573 75241176104437605413615)
                    ·
                      rfl

theorem cell23_439595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 7].length) (baseStart_439595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439595 prefixEnd_439595 := by exact prefixLift 439595
  have htrace : WordTrace (prefixWord ++ tailWord_439595) baseStart_439595 baseEnd_439595 := by
    simpa [prefixWord, tailWord_439595, baseEnd_439595] using wordTrace_append hprefix tailTrace_439595
  have hstable : (prefixWord ++ tailWord_439595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439595).length < 2 ^ (prefixWord ++ tailWord_439595).sum := by decide
  have hdescent : baseEnd_439595 < baseStart_439595 := by decide
  rcases family_descends (prefixWord ++ tailWord_439595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439610 : List Nat := [3, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2]
def baseStart_439610 : Nat := 118140960795 + 439610 * 2 ^ 59
def prefixEnd_439610 : Nat := 4983230072969 + 3 ^ 40 * 439610 * 2
def baseEnd_439610 : Nat := 225731230523130257553277

theorem tailTrace_439610 : CollatzResearch.WordTrace tailWord_439610 prefixEnd_439610 225731230523130257553277 := by
  unfold tailWord_439610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4008473484343881063933071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10689262624917016170488189 4008473484343881063933071)
  ·
    refine ⟨6012710226515821595899607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4008473484343881063933071 6012710226515821595899607)
    ·
      refine ⟨9019065339773732393849411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6012710226515821595899607 9019065339773732393849411)
      ·
        refine ⟨13528598009660598590774117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9019065339773732393849411 13528598009660598590774117)
        ·
          refine ⟨2536612126811362235770147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13528598009660598590774117 2536612126811362235770147)
          ·
            refine ⟨3804918190217043353655221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2536612126811362235770147 3804918190217043353655221)
            ·
              refine ⟨356711080332847814405177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3804918190217043353655221 356711080332847814405177)
              ·
                refine ⟨267533310249635860803883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356711080332847814405177 267533310249635860803883)
                ·
                  refine ⟨401299965374453791205825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267533310249635860803883 401299965374453791205825)
                  ·
                    refine ⟨300974974030840343404369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 401299965374453791205825 300974974030840343404369)
                    ·
                      refine ⟨225731230523130257553277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 300974974030840343404369 225731230523130257553277)
                      ·
                        rfl

theorem cell23_439610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2].length) (baseStart_439610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439610 prefixEnd_439610 := by exact prefixLift 439610
  have htrace : WordTrace (prefixWord ++ tailWord_439610) baseStart_439610 baseEnd_439610 := by
    simpa [prefixWord, tailWord_439610, baseEnd_439610] using wordTrace_append hprefix tailTrace_439610
  have hstable : (prefixWord ++ tailWord_439610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439610).length < 2 ^ (prefixWord ++ tailWord_439610).sum := by decide
  have hdescent : baseEnd_439610 < baseStart_439610 := by decide
  rcases family_descends (prefixWord ++ tailWord_439610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439619 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 3, 3, 2]
def baseStart_439619 : Nat := 118140960795 + 439619 * 2 ^ 59
def prefixEnd_439619 : Nat := 4983230072969 + 3 ^ 40 * 439619 * 2
def baseEnd_439619 : Nat := 225735851849020722340735

theorem tailTrace_439619 : CollatzResearch.WordTrace tailWord_439619 prefixEnd_439619 225735851849020722340735 := by
  unfold tailWord_439619
  simp only [CollatzResearch.WordTrace]
  refine ⟨16034222194342918792809911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10689481462895279195206607 16034222194342918792809911)
  ·
    refine ⟨24051333291514378189214867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16034222194342918792809911 24051333291514378189214867)
    ·
      refine ⟨36076999937271567283822301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24051333291514378189214867 36076999937271567283822301)
      ·
        refine ⟨13528874976476837731433363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36076999937271567283822301 13528874976476837731433363)
        ·
          refine ⟨20293312464715256597150045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13528874976476837731433363 20293312464715256597150045)
          ·
            refine ⟨7609992174268221223931267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20293312464715256597150045 7609992174268221223931267)
            ·
              refine ⟨11414988261402331835896901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7609992174268221223931267 11414988261402331835896901)
              ·
                refine ⟨2140310299012937219230669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11414988261402331835896901 2140310299012937219230669)
                ·
                  refine ⟨802616362129851457211501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2140310299012937219230669 802616362129851457211501)
                  ·
                    refine ⟨300981135798694296454313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 802616362129851457211501 300981135798694296454313)
                    ·
                      refine ⟨225735851849020722340735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 300981135798694296454313 225735851849020722340735)
                      ·
                        rfl

theorem cell23_439619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 3, 2].length) (baseStart_439619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439619 prefixEnd_439619 := by exact prefixLift 439619
  have htrace : WordTrace (prefixWord ++ tailWord_439619) baseStart_439619 baseEnd_439619 := by
    simpa [prefixWord, tailWord_439619, baseEnd_439619] using wordTrace_append hprefix tailTrace_439619
  have hstable : (prefixWord ++ tailWord_439619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439619).length < 2 ^ (prefixWord ++ tailWord_439619).sum := by decide
  have hdescent : baseEnd_439619 < baseStart_439619 := by decide
  rcases family_descends (prefixWord ++ tailWord_439619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439620 : List Nat := [2, 3, 4, 1, 1, 3, 2, 1, 2, 4]
def baseStart_439620 : Nat := 118140960795 + 439620 * 2 ^ 59
def prefixEnd_439620 : Nat := 4983230072969 + 3 ^ 40 * 439620 * 2
def baseEnd_439620 : Nat := 75245455109891739476077

theorem tailTrace_439620 : CollatzResearch.WordTrace tailWord_439620 prefixEnd_439620 75245455109891739476077 := by
  unfold tailWord_439620
  simp only [CollatzResearch.WordTrace]
  refine ⟨8017129333669647981798157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10689505778226197309064209 8017129333669647981798157)
  ·
    refine ⟨3006423500126117993174309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8017129333669647981798157 3006423500126117993174309)
    ·
      refine ⟨563704406273647123720183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3006423500126117993174309 563704406273647123720183)
      ·
        refine ⟨845556609410470685580275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563704406273647123720183 845556609410470685580275)
        ·
          refine ⟨1268334914115706028370413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845556609410470685580275 1268334914115706028370413)
          ·
            refine ⟨475625592793389760638905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1268334914115706028370413 475625592793389760638905)
            ·
              refine ⟨356719194595042320479179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475625592793389760638905 356719194595042320479179)
              ·
                refine ⟨535078791892563480718769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356719194595042320479179 535078791892563480718769)
                ·
                  refine ⟨401309093919422610539077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535078791892563480718769 401309093919422610539077)
                  ·
                    refine ⟨75245455109891739476077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 401309093919422610539077 75245455109891739476077)
                    ·
                      rfl

theorem cell23_439620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_439620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439620 prefixEnd_439620 := by exact prefixLift 439620
  have htrace : WordTrace (prefixWord ++ tailWord_439620) baseStart_439620 baseEnd_439620 := by
    simpa [prefixWord, tailWord_439620, baseEnd_439620] using wordTrace_append hprefix tailTrace_439620
  have hstable : (prefixWord ++ tailWord_439620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439620).length < 2 ^ (prefixWord ++ tailWord_439620).sum := by decide
  have hdescent : baseEnd_439620 < baseStart_439620 := by decide
  rcases family_descends (prefixWord ++ tailWord_439620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439636 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_439636 : Nat := 118140960795 + 439636 * 2 ^ 59
def prefixEnd_439636 : Nat := 4983230072969 + 3 ^ 40 * 439636 * 2
def baseEnd_439636 : Nat := 225744581020147155828157

theorem tailTrace_439636 : CollatzResearch.WordTrace tailWord_439636 prefixEnd_439636 225744581020147155828157 := by
  unfold tailWord_439636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8017421117640665348089381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10689894823520887130785841 8017421117640665348089381)
  ·
    refine ⟨1503266459557624752766759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8017421117640665348089381 1503266459557624752766759)
    ·
      refine ⟨2254899689336437129150139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1503266459557624752766759 2254899689336437129150139)
      ·
        refine ⟨3382349534004655693725209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2254899689336437129150139 3382349534004655693725209)
        ·
          refine ⟨2536762150503491770293907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3382349534004655693725209 2536762150503491770293907)
          ·
            refine ⟨3805143225755237655440861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2536762150503491770293907 3805143225755237655440861)
            ·
              refine ⟨1426928709658214120790323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3805143225755237655440861 1426928709658214120790323)
              ·
                refine ⟨2140393064487321181185485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426928709658214120790323 2140393064487321181185485)
                ·
                  refine ⟨802647399182745442944557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2140393064487321181185485 802647399182745442944557)
                  ·
                    refine ⟨300992774693529541104209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 802647399182745442944557 300992774693529541104209)
                    ·
                      refine ⟨225744581020147155828157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 300992774693529541104209 225744581020147155828157)
                      ·
                        rfl

theorem cell23_439636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_439636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439636 prefixEnd_439636 := by exact prefixLift 439636
  have htrace : WordTrace (prefixWord ++ tailWord_439636) baseStart_439636 baseEnd_439636 := by
    simpa [prefixWord, tailWord_439636, baseEnd_439636] using wordTrace_append hprefix tailTrace_439636
  have hstable : (prefixWord ++ tailWord_439636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439636).length < 2 ^ (prefixWord ++ tailWord_439636).sum := by decide
  have hdescent : baseEnd_439636 < baseStart_439636 := by decide
  rcases family_descends (prefixWord ++ tailWord_439636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439653 : List Nat := [1, 3, 1, 3, 1, 2, 5, 1, 1, 3, 2]
def baseStart_439653 : Nat := 118140960795 + 439653 * 2 ^ 59
def prefixEnd_439653 : Nat := 4983230072969 + 3 ^ 40 * 439653 * 2
def baseEnd_439653 : Nat := 225753310191273589315579

theorem tailTrace_439653 : CollatzResearch.WordTrace tailWord_439653 prefixEnd_439653 225753310191273589315579 := by
  unfold tailWord_439653
  simp only [CollatzResearch.WordTrace]
  refine ⟨16035462276219742599547613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10690308184146495066365075 16035462276219742599547613)
  ·
    refine ⟨6013298353582403474830355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16035462276219742599547613 6013298353582403474830355)
    ·
      refine ⟨9019947530373605212245533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6013298353582403474830355 9019947530373605212245533)
      ·
        refine ⟨3382480323890101954592075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9019947530373605212245533 3382480323890101954592075)
        ·
          refine ⟨5073720485835152931888113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3382480323890101954592075 5073720485835152931888113)
          ·
            refine ⟨3805290364376364698916085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5073720485835152931888113 3805290364376364698916085)
            ·
              refine ⟨356745971660284190523383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3805290364376364698916085 356745971660284190523383)
              ·
                refine ⟨535118957490426285785075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356745971660284190523383 535118957490426285785075)
                ·
                  refine ⟨802678436235639428677613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535118957490426285785075 802678436235639428677613)
                  ·
                    refine ⟨301004413588364785754105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 802678436235639428677613 301004413588364785754105)
                    ·
                      refine ⟨225753310191273589315579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 301004413588364785754105 225753310191273589315579)
                      ·
                        rfl

theorem cell23_439653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_439653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439653 prefixEnd_439653 := by exact prefixLift 439653
  have htrace : WordTrace (prefixWord ++ tailWord_439653) baseStart_439653 baseEnd_439653 := by
    simpa [prefixWord, tailWord_439653, baseEnd_439653] using wordTrace_append hprefix tailTrace_439653
  have hstable : (prefixWord ++ tailWord_439653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439653).length < 2 ^ (prefixWord ++ tailWord_439653).sum := by decide
  have hdescent : baseEnd_439653 < baseStart_439653 := by decide
  rcases family_descends (prefixWord ++ tailWord_439653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439683 : List Nat := [1, 1, 1, 3, 5, 1, 2, 3, 2, 2, 2]
def baseStart_439683 : Nat := 118140960795 + 439683 * 2 ^ 59
def prefixEnd_439683 : Nat := 4983230072969 + 3 ^ 40 * 439683 * 2
def baseEnd_439683 : Nat := 225768714610908471940441

theorem tailTrace_439683 : CollatzResearch.WordTrace tailWord_439683 prefixEnd_439683 225768714610908471940441 := by
  unfold tailWord_439683
  simp only [CollatzResearch.WordTrace]
  refine ⟨16036556466111057723139703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10691037644074038482093135 16036556466111057723139703)
  ·
    refine ⟨24054834699166586584709555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16036556466111057723139703 24054834699166586584709555)
    ·
      refine ⟨36082252048749879877064333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24054834699166586584709555 36082252048749879877064333)
      ·
        refine ⟨13530844518281204953899125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36082252048749879877064333 13530844518281204953899125)
        ·
          refine ⟨1268516673588862964428043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13530844518281204953899125 1268516673588862964428043)
          ·
            refine ⟨1902775010383294446642065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268516673588862964428043 1902775010383294446642065)
            ·
              refine ⟨1427081257787470834981549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1902775010383294446642065 1427081257787470834981549)
              ·
                refine ⟨535155471670301563118081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1427081257787470834981549 535155471670301563118081)
                ·
                  refine ⟨401366603752726172338561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535155471670301563118081 401366603752726172338561)
                  ·
                    refine ⟨301024952814544629253921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 401366603752726172338561 301024952814544629253921)
                    ·
                      refine ⟨225768714610908471940441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 301024952814544629253921 225768714610908471940441)
                      ·
                        rfl

theorem cell23_439683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 2, 2].length) (baseStart_439683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439683 prefixEnd_439683 := by exact prefixLift 439683
  have htrace : WordTrace (prefixWord ++ tailWord_439683) baseStart_439683 baseEnd_439683 := by
    simpa [prefixWord, tailWord_439683, baseEnd_439683] using wordTrace_append hprefix tailTrace_439683
  have hstable : (prefixWord ++ tailWord_439683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439683).length < 2 ^ (prefixWord ++ tailWord_439683).sum := by decide
  have hdescent : baseEnd_439683 < baseStart_439683 := by decide
  rcases family_descends (prefixWord ++ tailWord_439683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439689 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 7]
def baseStart_439689 : Nat := 118140960795 + 439689 * 2 ^ 59
def prefixEnd_439689 : Nat := 4983230072969 + 3 ^ 40 * 439689 * 2
def baseEnd_439689 : Nat := 25085755054981716496157

theorem tailTrace_439689 : CollatzResearch.WordTrace tailWord_439689 prefixEnd_439689 25085755054981716496157 := by
  unfold tailWord_439689
  simp only [CollatzResearch.WordTrace]
  refine ⟨16036775304089320747858121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10691183536059547165238747 16036775304089320747858121)
  ·
    refine ⟨12027581478066990560893591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16036775304089320747858121 12027581478066990560893591)
    ·
      refine ⟨18041372217100485841340387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12027581478066990560893591 18041372217100485841340387)
      ·
        refine ⟨27062058325650728762010581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18041372217100485841340387 27062058325650728762010581)
        ·
          refine ⟨634266992007438955359623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27062058325650728762010581 634266992007438955359623)
          ·
            refine ⟨951400488011158433039435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634266992007438955359623 951400488011158433039435)
            ·
              refine ⟨1427100732016737649559153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951400488011158433039435 1427100732016737649559153)
              ·
                refine ⟨1070325549012553237169365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1427100732016737649559153 1070325549012553237169365)
                ·
                  refine ⟨25085755054981716496157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1070325549012553237169365 25085755054981716496157)
                  ·
                    rfl

theorem cell23_439689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 7].length) (baseStart_439689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439689 prefixEnd_439689 := by exact prefixLift 439689
  have htrace : WordTrace (prefixWord ++ tailWord_439689) baseStart_439689 baseEnd_439689 := by
    simpa [prefixWord, tailWord_439689, baseEnd_439689] using wordTrace_append hprefix tailTrace_439689
  have hstable : (prefixWord ++ tailWord_439689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439689).length < 2 ^ (prefixWord ++ tailWord_439689).sum := by decide
  have hdescent : baseEnd_439689 < baseStart_439689 := by decide
  rcases family_descends (prefixWord ++ tailWord_439689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439706 : List Nat := [3, 1, 1, 4, 1, 1, 4, 3, 5]
def baseStart_439706 : Nat := 118140960795 + 439706 * 2 ^ 59
def prefixEnd_439706 : Nat := 4983230072969 + 3 ^ 40 * 439706 * 2
def baseEnd_439706 : Nat := 25086724962884653550315

theorem tailTrace_439706 : CollatzResearch.WordTrace tailWord_439706 prefixEnd_439706 25086724962884653550315 := by
  unfold tailWord_439706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4009348836256933162806743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10691596896685155100817981 4009348836256933162806743)
  ·
    refine ⟨6014023254385399744210115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4009348836256933162806743 6014023254385399744210115)
    ·
      refine ⟨9021034881578099616315173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6014023254385399744210115 9021034881578099616315173)
      ·
        refine ⟨1691444040295893678059095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9021034881578099616315173 1691444040295893678059095)
        ·
          refine ⟨2537166060443840517088643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1691444040295893678059095 2537166060443840517088643)
          ·
            refine ⟨3805749090665760775632965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2537166060443840517088643 3805749090665760775632965)
            ·
              refine ⟨713577954499830145431181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3805749090665760775632965 713577954499830145431181)
              ·
                refine ⟨267591732937436304536693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 713577954499830145431181 267591732937436304536693)
                ·
                  refine ⟨25086724962884653550315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 267591732937436304536693 25086724962884653550315)
                  ·
                    rfl

theorem cell23_439706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 5].length) (baseStart_439706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439706 prefixEnd_439706 := by exact prefixLift 439706
  have htrace : WordTrace (prefixWord ++ tailWord_439706) baseStart_439706 baseEnd_439706 := by
    simpa [prefixWord, tailWord_439706, baseEnd_439706] using wordTrace_append hprefix tailTrace_439706
  have hstable : (prefixWord ++ tailWord_439706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439706).length < 2 ^ (prefixWord ++ tailWord_439706).sum := by decide
  have hdescent : baseEnd_439706 < baseStart_439706 := by decide
  rcases family_descends (prefixWord ++ tailWord_439706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439719 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 4, 5]
def baseStart_439719 : Nat := 118140960795 + 439719 * 2 ^ 59
def prefixEnd_439719 : Nat := 4983230072969 + 3 ^ 40 * 439719 * 2
def baseEnd_439719 : Nat := 75262399971490110363425

theorem tailTrace_439719 : CollatzResearch.WordTrace tailWord_439719 prefixEnd_439719 75262399971490110363425 := by
  unfold tailWord_439719
  simp only [CollatzResearch.WordTrace]
  refine ⟨16037869493980635871450211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10691912995987090580966807 16037869493980635871450211)
  ·
    refine ⟨24056804240970953807175317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16037869493980635871450211 24056804240970953807175317)
    ·
      refine ⟨1127662698795513459711343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24056804240970953807175317 1127662698795513459711343)
      ·
        refine ⟨1691494048193270189567015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1127662698795513459711343 1691494048193270189567015)
        ·
          refine ⟨2537241072289905284350523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1691494048193270189567015 2537241072289905284350523)
          ·
            refine ⟨3805861608434857926525785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2537241072289905284350523 3805861608434857926525785)
            ·
              refine ⟨2854396206326143444894339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3805861608434857926525785 2854396206326143444894339)
              ·
                refine ⟨4281594309489215167341509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2854396206326143444894339 4281594309489215167341509)
                ·
                  refine ⟨802798933029227843876533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4281594309489215167341509 802798933029227843876533)
                  ·
                    refine ⟨75262399971490110363425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 802798933029227843876533 75262399971490110363425)
                    ·
                      rfl

theorem cell23_439719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_439719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439719 prefixEnd_439719 := by exact prefixLift 439719
  have htrace : WordTrace (prefixWord ++ tailWord_439719) baseStart_439719 baseEnd_439719 := by
    simpa [prefixWord, tailWord_439719, baseEnd_439719] using wordTrace_append hprefix tailTrace_439719
  have hstable : (prefixWord ++ tailWord_439719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439719).length < 2 ^ (prefixWord ++ tailWord_439719).sum := by decide
  have hdescent : baseEnd_439719 < baseStart_439719 := by decide
  rcases family_descends (prefixWord ++ tailWord_439719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439759 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 3]
def baseStart_439759 : Nat := 118140960795 + 439759 * 2 ^ 59
def prefixEnd_439759 : Nat := 4983230072969 + 3 ^ 40 * 439759 * 2
def baseEnd_439759 : Nat := 225807739140650174590091

theorem tailTrace_439759 : CollatzResearch.WordTrace tailWord_439759 prefixEnd_439759 225807739140650174590091 := by
  unfold tailWord_439759
  simp only [CollatzResearch.WordTrace]
  refine ⟨16039328413835722702906331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10692885609223815135270887 16039328413835722702906331)
  ·
    refine ⟨24058992620753584054359497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16039328413835722702906331 24058992620753584054359497)
    ·
      refine ⟨18044244465565188040769623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24058992620753584054359497 18044244465565188040769623)
      ·
        refine ⟨27066366698347782061154435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18044244465565188040769623 27066366698347782061154435)
        ·
          refine ⟨40599550047521673091731653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27066366698347782061154435 40599550047521673091731653)
          ·
            refine ⟨7612415633910313704699685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40599550047521673091731653 7612415633910313704699685)
            ·
              refine ⟨1427327931358183819631191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7612415633910313704699685 1427327931358183819631191)
              ·
                refine ⟨2140991897037275729446787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427327931358183819631191 2140991897037275729446787)
                ·
                  refine ⟨3211487845555913594170181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140991897037275729446787 3211487845555913594170181)
                  ·
                    refine ⟨602153971041733798906909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3211487845555913594170181 602153971041733798906909)
                    ·
                      refine ⟨225807739140650174590091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 602153971041733798906909 225807739140650174590091)
                      ·
                        rfl

theorem cell23_439759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 3].length) (baseStart_439759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439759 prefixEnd_439759 := by exact prefixLift 439759
  have htrace : WordTrace (prefixWord ++ tailWord_439759) baseStart_439759 baseEnd_439759 := by
    simpa [prefixWord, tailWord_439759, baseEnd_439759] using wordTrace_append hprefix tailTrace_439759
  have hstable : (prefixWord ++ tailWord_439759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439759).length < 2 ^ (prefixWord ++ tailWord_439759).sum := by decide
  have hdescent : baseEnd_439759 < baseStart_439759 := by decide
  rcases family_descends (prefixWord ++ tailWord_439759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439779 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 8]
def baseStart_439779 : Nat := 118140960795 + 439779 * 2 ^ 59
def prefixEnd_439779 : Nat := 4983230072969 + 3 ^ 40 * 439779 * 2
def baseEnd_439779 : Nat := 25090889861526677371111

theorem tailTrace_439779 : CollatzResearch.WordTrace tailWord_439779 prefixEnd_439779 25090889861526677371111 := by
  unfold tailWord_439779
  simp only [CollatzResearch.WordTrace]
  refine ⟨16040057873763266118634391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10693371915842177412422927 16040057873763266118634391)
  ·
    refine ⟨24060086810644899177951587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16040057873763266118634391 24060086810644899177951587)
    ·
      refine ⟨36090130215967348766927381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24060086810644899177951587 36090130215967348766927381)
      ·
        refine ⟨1691724853873469473449721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36090130215967348766927381 1691724853873469473449721)
        ·
          refine ⟨1268793640405102105087291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1691724853873469473449721 1268793640405102105087291)
          ·
            refine ⟨1903190460607653157630937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268793640405102105087291 1903190460607653157630937)
            ·
              refine ⟨1427392845455739868223203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1903190460607653157630937 1427392845455739868223203)
              ·
                refine ⟨2141089268183609802334805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427392845455739868223203 2141089268183609802334805)
                ·
                  refine ⟨25090889861526677371111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2141089268183609802334805 25090889861526677371111)
                  ·
                    rfl

theorem cell23_439779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 8].length) (baseStart_439779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439779 prefixEnd_439779 := by exact prefixLift 439779
  have htrace : WordTrace (prefixWord ++ tailWord_439779) baseStart_439779 baseEnd_439779 := by
    simpa [prefixWord, tailWord_439779, baseEnd_439779] using wordTrace_append hprefix tailTrace_439779
  have hstable : (prefixWord ++ tailWord_439779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439779).length < 2 ^ (prefixWord ++ tailWord_439779).sum := by decide
  have hdescent : baseEnd_439779 < baseStart_439779 := by decide
  rcases family_descends (prefixWord ++ tailWord_439779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439783 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 3, 4]
def baseStart_439783 : Nat := 118140960795 + 439783 * 2 ^ 59
def prefixEnd_439783 : Nat := 4983230072969 + 3 ^ 40 * 439783 * 2
def baseEnd_439783 : Nat := 75273354225452693563327

theorem tailTrace_439783 : CollatzResearch.WordTrace tailWord_439783 prefixEnd_439783 75273354225452693563327 := by
  unfold tailWord_439783
  simp only [CollatzResearch.WordTrace]
  refine ⟨16040203765748774801780003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10693469177165849867853335 16040203765748774801780003)
  ·
    refine ⟨24060305648623162202670005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16040203765748774801780003 24060305648623162202670005)
    ·
      refine ⟨2255653654558421456500313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24060305648623162202670005 2255653654558421456500313)
      ·
        refine ⟨1691740240918816092375235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2255653654558421456500313 1691740240918816092375235)
        ·
          refine ⟨2537610361378224138562853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1691740240918816092375235 2537610361378224138562853)
          ·
            refine ⟨475801942758417025980535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2537610361378224138562853 475801942758417025980535)
            ·
              refine ⟨713702914137625538970803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475801942758417025980535 713702914137625538970803)
              ·
                refine ⟨1070554371206438308456205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713702914137625538970803 1070554371206438308456205)
                ·
                  refine ⟨401457889202414365671077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070554371206438308456205 401457889202414365671077)
                  ·
                    refine ⟨75273354225452693563327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 401457889202414365671077 75273354225452693563327)
                    ·
                      rfl

theorem cell23_439783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_439783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439783 prefixEnd_439783 := by exact prefixLift 439783
  have htrace : WordTrace (prefixWord ++ tailWord_439783) baseStart_439783 baseEnd_439783 := by
    simpa [prefixWord, tailWord_439783, baseEnd_439783] using wordTrace_append hprefix tailTrace_439783
  have hstable : (prefixWord ++ tailWord_439783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439783).length < 2 ^ (prefixWord ++ tailWord_439783).sum := by decide
  have hdescent : baseEnd_439783 < baseStart_439783 := by decide
  rcases family_descends (prefixWord ++ tailWord_439783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439810 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_439810 : Nat := 118140960795 + 439810 * 2 ^ 59
def prefixEnd_439810 : Nat := 4983230072969 + 3 ^ 40 * 439810 * 2
def baseEnd_439810 : Nat := 225833926654029475052357

theorem tailTrace_439810 : CollatzResearch.WordTrace tailWord_439810 prefixEnd_439810 225833926654029475052357 := by
  unfold tailWord_439810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4010297134162739603253221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10694125691100638942008589 4010297134162739603253221)
  ·
    refine ⟨751930712655513675609979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4010297134162739603253221 751930712655513675609979)
    ·
      refine ⟨1127896068983270513414969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 751930712655513675609979 1127896068983270513414969)
      ·
        refine ⟨845922051737452885061227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1127896068983270513414969 845922051737452885061227)
        ·
          refine ⟨1268883077606179327591841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845922051737452885061227 1268883077606179327591841)
          ·
            refine ⟨951662308204634495693881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1268883077606179327591841 951662308204634495693881)
            ·
              refine ⟨713746731153475871770411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951662308204634495693881 713746731153475871770411)
              ·
                refine ⟨1070620096730213807655617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713746731153475871770411 1070620096730213807655617)
                ·
                  refine ⟨802965072547660355741713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1070620096730213807655617 802965072547660355741713)
                  ·
                    refine ⟨602223804410745266806285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 802965072547660355741713 602223804410745266806285)
                    ·
                      refine ⟨225833926654029475052357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 602223804410745266806285 225833926654029475052357)
                      ·
                        rfl

theorem cell23_439810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_439810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439810 prefixEnd_439810 := by exact prefixLift 439810
  have htrace : WordTrace (prefixWord ++ tailWord_439810) baseStart_439810 baseEnd_439810 := by
    simpa [prefixWord, tailWord_439810, baseEnd_439810] using wordTrace_append hprefix tailTrace_439810
  have hstable : (prefixWord ++ tailWord_439810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439810).length < 2 ^ (prefixWord ++ tailWord_439810).sum := by decide
  have hdescent : baseEnd_439810 < baseStart_439810 := by decide
  rcases family_descends (prefixWord ++ tailWord_439810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439816 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 1, 5, 2]
def baseStart_439816 : Nat := 118140960795 + 439816 * 2 ^ 59
def prefixEnd_439816 : Nat := 4983230072969 + 3 ^ 40 * 439816 * 2
def baseEnd_439816 : Nat := 225837007537956451577329

theorem tailTrace_439816 : CollatzResearch.WordTrace tailWord_439816 prefixEnd_439816 225837007537956451577329 := by
  unfold tailWord_439816
  simp only [CollatzResearch.WordTrace]
  refine ⟨8020703687314610718865651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10694271583086147625154201 8020703687314610718865651)
  ·
    refine ⟨12031055530971916078298477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8020703687314610718865651 12031055530971916078298477)
    ·
      refine ⟨4511645824114468529361929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12031055530971916078298477 4511645824114468529361929)
      ·
        refine ⟨3383734368085851397021447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4511645824114468529361929 3383734368085851397021447)
        ·
          refine ⟨5075601552128777095532171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3383734368085851397021447 5075601552128777095532171)
          ·
            refine ⟨7613402328193165643298257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5075601552128777095532171 7613402328193165643298257)
            ·
              refine ⟨5710051746144874232473693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7613402328193165643298257 5710051746144874232473693)
              ·
                refine ⟨2141269404804327837177635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5710051746144874232473693 2141269404804327837177635)
                ·
                  refine ⟨3211904107206491755766453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141269404804327837177635 3211904107206491755766453)
                  ·
                    refine ⟨301116010050608602103105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3211904107206491755766453 301116010050608602103105)
                    ·
                      refine ⟨225837007537956451577329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 301116010050608602103105 225837007537956451577329)
                      ·
                        rfl

theorem cell23_439816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_439816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439816 prefixEnd_439816 := by exact prefixLift 439816
  have htrace : WordTrace (prefixWord ++ tailWord_439816) baseStart_439816 baseEnd_439816 := by
    simpa [prefixWord, tailWord_439816, baseEnd_439816] using wordTrace_append hprefix tailTrace_439816
  have hstable : (prefixWord ++ tailWord_439816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439816).length < 2 ^ (prefixWord ++ tailWord_439816).sum := by decide
  have hdescent : baseEnd_439816 < baseStart_439816 := by decide
  rcases family_descends (prefixWord ++ tailWord_439816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439863 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 5, 2, 2]
def baseStart_439863 : Nat := 118140960795 + 439863 * 2 ^ 59
def prefixEnd_439863 : Nat := 4983230072969 + 3 ^ 40 * 439863 * 2
def baseEnd_439863 : Nat := 225861141128717767689613

theorem tailTrace_439863 : CollatzResearch.WordTrace tailWord_439863 prefixEnd_439863 225861141128717767689613 := by
  unfold tailWord_439863
  simp only [CollatzResearch.WordTrace]
  refine ⟨16043121605458948464692243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10695414403639298976461495 16043121605458948464692243)
  ·
    refine ⟨24064682408188422697038365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16043121605458948464692243 24064682408188422697038365)
    ·
      refine ⟨9024255903070658511389387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24064682408188422697038365 9024255903070658511389387)
      ·
        refine ⟨13536383854605987767084081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9024255903070658511389387 13536383854605987767084081)
        ·
          refine ⟨10152287890954490825313061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13536383854605987767084081 10152287890954490825313061)
          ·
            refine ⟨1903553979553967029746199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10152287890954490825313061 1903553979553967029746199)
            ·
              refine ⟨2855330969330950544619299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903553979553967029746199 2855330969330950544619299)
              ·
                refine ⟨4282996453996425816928949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855330969330950544619299 4282996453996425816928949)
                ·
                  refine ⟨401530917562164920337089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4282996453996425816928949 401530917562164920337089)
                  ·
                    refine ⟨301148188171623690252817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 401530917562164920337089 301148188171623690252817)
                    ·
                      refine ⟨225861141128717767689613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 301148188171623690252817 225861141128717767689613)
                      ·
                        rfl

theorem cell23_439863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 2, 2].length) (baseStart_439863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439863 prefixEnd_439863 := by exact prefixLift 439863
  have htrace : WordTrace (prefixWord ++ tailWord_439863) baseStart_439863 baseEnd_439863 := by
    simpa [prefixWord, tailWord_439863, baseEnd_439863] using wordTrace_append hprefix tailTrace_439863
  have hstable : (prefixWord ++ tailWord_439863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439863).length < 2 ^ (prefixWord ++ tailWord_439863).sum := by decide
  have hdescent : baseEnd_439863 < baseStart_439863 := by decide
  rcases family_descends (prefixWord ++ tailWord_439863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439866 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3]
def baseStart_439866 : Nat := 118140960795 + 439866 * 2 ^ 59
def prefixEnd_439866 : Nat := 4983230072969 + 3 ^ 40 * 439866 * 2
def baseEnd_439866 : Nat := 225862681570681255952099

theorem tailTrace_439866 : CollatzResearch.WordTrace tailWord_439866 prefixEnd_439866 225862681570681255952099 := by
  unfold tailWord_439866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4010807756112019994262863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10695487349632053318034301 4010807756112019994262863)
  ·
    refine ⟨6016211634168029991394295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4010807756112019994262863 6016211634168029991394295)
    ·
      refine ⟨9024317451252044987091443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6016211634168029991394295 9024317451252044987091443)
      ·
        refine ⟨13536476176878067480637165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9024317451252044987091443 13536476176878067480637165)
        ·
          refine ⟨5076178566329275305238937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13536476176878067480637165 5076178566329275305238937)
          ·
            refine ⟨3807133924746956478929203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5076178566329275305238937 3807133924746956478929203)
            ·
              refine ⟨5710700887120434718393805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807133924746956478929203 5710700887120434718393805)
              ·
                refine ⟨2141512832670163019397677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5710700887120434718393805 2141512832670163019397677)
                ·
                  refine ⟨803067312251311132274129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2141512832670163019397677 803067312251311132274129)
                  ·
                    refine ⟨602300484188483349205597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 803067312251311132274129 602300484188483349205597)
                    ·
                      refine ⟨225862681570681255952099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 602300484188483349205597 225862681570681255952099)
                      ·
                        rfl

theorem cell23_439866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_439866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439866 prefixEnd_439866 := by exact prefixLift 439866
  have htrace : WordTrace (prefixWord ++ tailWord_439866) baseStart_439866 baseEnd_439866 := by
    simpa [prefixWord, tailWord_439866, baseEnd_439866] using wordTrace_append hprefix tailTrace_439866
  have hstable : (prefixWord ++ tailWord_439866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439866).length < 2 ^ (prefixWord ++ tailWord_439866).sum := by decide
  have hdescent : baseEnd_439866 < baseStart_439866 := by decide
  rcases family_descends (prefixWord ++ tailWord_439866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439890 : List Nat := [3, 2, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_439890 : Nat := 118140960795 + 439890 * 2 ^ 59
def prefixEnd_439890 : Nat := 4983230072969 + 3 ^ 40 * 439890 * 2
def baseEnd_439890 : Nat := 75291668368796387350663

theorem tailTrace_439890 : CollatzResearch.WordTrace tailWord_439890 prefixEnd_439890 75291668368796387350663 := by
  unfold tailWord_439890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4011026594090283018981281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10696070917574088050616749 4011026594090283018981281)
  ·
    refine ⟨3008269945567712264235961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4011026594090283018981281 3008269945567712264235961)
    ·
      refine ⟨2256202459175784198176971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3008269945567712264235961 2256202459175784198176971)
      ·
        refine ⟨3384303688763676297265457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2256202459175784198176971 3384303688763676297265457)
        ·
          refine ⟨2538227766572757222949093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3384303688763676297265457 2538227766572757222949093)
          ·
            refine ⟨475917706232391979302955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2538227766572757222949093 475917706232391979302955)
            ·
              refine ⟨713876559348587968954433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475917706232391979302955 713876559348587968954433)
              ·
                refine ⟨535407419511440976715825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713876559348587968954433 535407419511440976715825)
                ·
                  refine ⟨401555564633580732536869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535407419511440976715825 401555564633580732536869)
                  ·
                    refine ⟨75291668368796387350663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 401555564633580732536869 75291668368796387350663)
                    ·
                      rfl

theorem cell23_439890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_439890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439890 prefixEnd_439890 := by exact prefixLift 439890
  have htrace : WordTrace (prefixWord ++ tailWord_439890) baseStart_439890 baseEnd_439890 := by
    simpa [prefixWord, tailWord_439890, baseEnd_439890] using wordTrace_append hprefix tailTrace_439890
  have hstable : (prefixWord ++ tailWord_439890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439890).length < 2 ^ (prefixWord ++ tailWord_439890).sum := by decide
  have hdescent : baseEnd_439890 < baseStart_439890 := by decide
  rcases family_descends (prefixWord ++ tailWord_439890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439913 : List Nat := [1, 2, 1, 1, 1, 4, 2, 5, 2, 1, 3]
def baseStart_439913 : Nat := 118140960795 + 439913 * 2 ^ 59
def prefixEnd_439913 : Nat := 4983230072969 + 3 ^ 40 * 439913 * 2
def baseEnd_439913 : Nat := 225886815161442572064383

theorem tailTrace_439913 : CollatzResearch.WordTrace tailWord_439913 prefixEnd_439913 225886815161442572064383 := by
  unfold tailWord_439913
  simp only [CollatzResearch.WordTrace]
  refine ⟨16044945255277807004012393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10696630170185204669341595 16044945255277807004012393)
  ·
    refine ⟨12033708941458355253009295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16044945255277807004012393 12033708941458355253009295)
    ·
      refine ⟨18050563412187532879513943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12033708941458355253009295 18050563412187532879513943)
      ·
        refine ⟨27075845118281299319270915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18050563412187532879513943 27075845118281299319270915)
        ·
          refine ⟨40613767677421948978906373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27075845118281299319270915 40613767677421948978906373)
          ·
            refine ⟨7615081439516615433544945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40613767677421948978906373 7615081439516615433544945)
            ·
              refine ⟨5711311079637461575158709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7615081439516615433544945 5711311079637461575158709)
              ·
                refine ⟨535435413716012022671129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5711311079637461575158709 535435413716012022671129)
                ·
                  refine ⟨401576560287009017003347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535435413716012022671129 401576560287009017003347)
                  ·
                    refine ⟨602364840430513525505021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 401576560287009017003347 602364840430513525505021)
                    ·
                      refine ⟨225886815161442572064383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 602364840430513525505021 225886815161442572064383)
                      ·
                        rfl

theorem cell23_439913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 1, 3].length) (baseStart_439913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439913 prefixEnd_439913 := by exact prefixLift 439913
  have htrace : WordTrace (prefixWord ++ tailWord_439913) baseStart_439913 baseEnd_439913 := by
    simpa [prefixWord, tailWord_439913, baseEnd_439913] using wordTrace_append hprefix tailTrace_439913
  have hstable : (prefixWord ++ tailWord_439913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439913).length < 2 ^ (prefixWord ++ tailWord_439913).sum := by decide
  have hdescent : baseEnd_439913 < baseStart_439913 := by decide
  rcases family_descends (prefixWord ++ tailWord_439913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439964 : List Nat := [2, 2, 3, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_439964 : Nat := 118140960795 + 439964 * 2 ^ 59
def prefixEnd_439964 : Nat := 4983230072969 + 3 ^ 40 * 439964 * 2
def baseEnd_439964 : Nat := 225913002674821872526649

theorem tailTrace_439964 : CollatzResearch.WordTrace tailWord_439964 prefixEnd_439964 225913002674821872526649 := by
  unfold tailWord_439964
  simp only [CollatzResearch.WordTrace]
  refine ⟨8023402689046521357059473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10697870252062028476079297 8023402689046521357059473)
  ·
    refine ⟨6017552016784891017794605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8023402689046521357059473 6017552016784891017794605)
    ·
      refine ⟨2256582006294334131672977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6017552016784891017794605 2256582006294334131672977)
      ·
        refine ⟨1692436504720750598754733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2256582006294334131672977 1692436504720750598754733)
        ·
          refine ⟨634663689270281474533025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1692436504720750598754733 634663689270281474533025)
          ·
            refine ⟨475997766952711105899769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 634663689270281474533025 475997766952711105899769)
            ·
              refine ⟨356998325214533329424827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475997766952711105899769 356998325214533329424827)
              ·
                refine ⟨535497487821799994137241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356998325214533329424827 535497487821799994137241)
                ·
                  refine ⟨401623115866349995602931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535497487821799994137241 401623115866349995602931)
                  ·
                    refine ⟨602434673799524993404397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 401623115866349995602931 602434673799524993404397)
                    ·
                      refine ⟨225913002674821872526649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 602434673799524993404397 225913002674821872526649)
                      ·
                        rfl

theorem cell23_439964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_439964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439964 prefixEnd_439964 := by exact prefixLift 439964
  have htrace : WordTrace (prefixWord ++ tailWord_439964) baseStart_439964 baseEnd_439964 := by
    simpa [prefixWord, tailWord_439964, baseEnd_439964] using wordTrace_append hprefix tailTrace_439964
  have hstable : (prefixWord ++ tailWord_439964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439964).length < 2 ^ (prefixWord ++ tailWord_439964).sum := by decide
  have hdescent : baseEnd_439964 < baseStart_439964 := by decide
  rcases family_descends (prefixWord ++ tailWord_439964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439990 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_439990 : Nat := 118140960795 + 439990 * 2 ^ 59
def prefixEnd_439990 : Nat := 4983230072969 + 3 ^ 40 * 439990 * 2
def baseEnd_439990 : Nat := 225926353171838770801529

theorem tailTrace_439990 : CollatzResearch.WordTrace tailWord_439990 prefixEnd_439990 225926353171838770801529 := by
  unfold tailWord_439990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1002984604749928072160339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10698502450665899436376949 1002984604749928072160339)
  ·
    refine ⟨1504476907124892108240509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1002984604749928072160339 1504476907124892108240509)
    ·
      refine ⟨564178840171834540590191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1504476907124892108240509 564178840171834540590191)
      ·
        refine ⟨846268260257751810885287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564178840171834540590191 846268260257751810885287)
        ·
          refine ⟨1269402390386627716327931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846268260257751810885287 1269402390386627716327931)
          ·
            refine ⟨1904103585579941574491897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269402390386627716327931 1904103585579941574491897)
            ·
              refine ⟨1428077689184956180868923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1904103585579941574491897 1428077689184956180868923)
              ·
                refine ⟨2142116533777434271303385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428077689184956180868923 2142116533777434271303385)
                ·
                  refine ⟨1606587400333075703477539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2142116533777434271303385 1606587400333075703477539)
                  ·
                    refine ⟨2409881100499613555216309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1606587400333075703477539 2409881100499613555216309)
                    ·
                      refine ⟨225926353171838770801529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2409881100499613555216309 225926353171838770801529)
                      ·
                        rfl

theorem cell23_439990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_439990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439990 prefixEnd_439990 := by exact prefixLift 439990
  have htrace : WordTrace (prefixWord ++ tailWord_439990) baseStart_439990 baseEnd_439990 := by
    simpa [prefixWord, tailWord_439990, baseEnd_439990] using wordTrace_append hprefix tailTrace_439990
  have hstable : (prefixWord ++ tailWord_439990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439990).length < 2 ^ (prefixWord ++ tailWord_439990).sum := by decide
  have hdescent : baseEnd_439990 < baseStart_439990 := by decide
  rcases family_descends (prefixWord ++ tailWord_439990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440010 : List Nat := [3, 1, 2, 1, 5, 1, 1, 4, 5]
def baseStart_440010 : Nat := 118140960795 + 440010 * 2 ^ 59
def prefixEnd_440010 : Nat := 4983230072969 + 3 ^ 40 * 440010 * 2
def baseEnd_440010 : Nat := 25104069198325410283493

theorem tailTrace_440010 : CollatzResearch.WordTrace tailWord_440010 prefixEnd_440010 25104069198325410283493 := by
  unfold tailWord_440010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4012120783981598142573371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10698988757284261713528989 4012120783981598142573371)
  ·
    refine ⟨6018181175972397213860057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4012120783981598142573371 6018181175972397213860057)
    ·
      refine ⟨4513635881979297910395043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6018181175972397213860057 4513635881979297910395043)
      ·
        refine ⟨6770453822968946865592565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4513635881979297910395043 6770453822968946865592565)
        ·
          refine ⟨634730045903338768649303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6770453822968946865592565 634730045903338768649303)
          ·
            refine ⟨952095068855008152973955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634730045903338768649303 952095068855008152973955)
            ·
              refine ⟨1428142603282512229460933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952095068855008152973955 1428142603282512229460933)
              ·
                refine ⟨267776738115471043023925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1428142603282512229460933 267776738115471043023925)
                ·
                  refine ⟨25104069198325410283493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 267776738115471043023925 25104069198325410283493)
                  ·
                    rfl

theorem cell23_440010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 5].length) (baseStart_440010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440010 prefixEnd_440010 := by exact prefixLift 440010
  have htrace : WordTrace (prefixWord ++ tailWord_440010) baseStart_440010 baseEnd_440010 := by
    simpa [prefixWord, tailWord_440010, baseEnd_440010] using wordTrace_append hprefix tailTrace_440010
  have hstable : (prefixWord ++ tailWord_440010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440010).length < 2 ^ (prefixWord ++ tailWord_440010).sum := by decide
  have hdescent : baseEnd_440010 < baseStart_440010 := by decide
  rcases family_descends (prefixWord ++ tailWord_440010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440020 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_440020 : Nat := 118140960795 + 440020 * 2 ^ 59
def prefixEnd_440020 : Nat := 4983230072969 + 3 ^ 40 * 440020 * 2
def baseEnd_440020 : Nat := 225941757591473653426391

theorem tailTrace_440020 : CollatzResearch.WordTrace tailWord_440020 prefixEnd_440020 225941757591473653426391 := by
  unfold tailWord_440020
  simp only [CollatzResearch.WordTrace]
  refine ⟨8024423932945082139078757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10699231910593442852105009 8024423932945082139078757)
  ·
    refine ⟨1504579487427202901077267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8024423932945082139078757 1504579487427202901077267)
    ·
      refine ⟨2256869231140804351615901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1504579487427202901077267 2256869231140804351615901)
      ·
        refine ⟨846325961677801631855963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2256869231140804351615901 846325961677801631855963)
        ·
          refine ⟨1269488942516702447783945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846325961677801631855963 1269488942516702447783945)
          ·
            refine ⟨952116706887526835837959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1269488942516702447783945 952116706887526835837959)
            ·
              refine ⟨1428175060331290253756939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952116706887526835837959 1428175060331290253756939)
              ·
                refine ⟨2142262590496935380635409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428175060331290253756939 2142262590496935380635409)
                ·
                  refine ⟨1606696942872701535476557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2142262590496935380635409 1606696942872701535476557)
                  ·
                    refine ⟨602511353577263075803709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1606696942872701535476557 602511353577263075803709)
                    ·
                      refine ⟨225941757591473653426391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 602511353577263075803709 225941757591473653426391)
                      ·
                        rfl

theorem cell23_440020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_440020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440020 prefixEnd_440020 := by exact prefixLift 440020
  have htrace : WordTrace (prefixWord ++ tailWord_440020) baseStart_440020 baseEnd_440020 := by
    simpa [prefixWord, tailWord_440020, baseEnd_440020] using wordTrace_append hprefix tailTrace_440020
  have hstable : (prefixWord ++ tailWord_440020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440020).length < 2 ^ (prefixWord ++ tailWord_440020).sum := by decide
  have hdescent : baseEnd_440020 < baseStart_440020 := by decide
  rcases family_descends (prefixWord ++ tailWord_440020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440040 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 2, 5]
def baseStart_440040 : Nat := 118140960795 + 440040 * 2 ^ 59
def prefixEnd_440040 : Nat := 4983230072969 + 3 ^ 40 * 440040 * 2
def baseEnd_440040 : Nat := 75317342401521191725433

theorem tailTrace_440040 : CollatzResearch.WordTrace tailWord_440040 prefixEnd_440040 75317342401521191725433 := by
  unfold tailWord_440040
  simp only [CollatzResearch.WordTrace]
  refine ⟨8024788662908853846942787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10699718217211805129257049 8024788662908853846942787)
  ·
    refine ⟨12037182994363280770414181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8024788662908853846942787 12037182994363280770414181)
    ·
      refine ⟨2256971811443115144452659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12037182994363280770414181 2256971811443115144452659)
      ·
        refine ⟨3385457717164672716678989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2256971811443115144452659 3385457717164672716678989)
        ·
          refine ⟨1269546643936752268754621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3385457717164672716678989 1269546643936752268754621)
          ·
            refine ⟨476079991476282100782983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1269546643936752268754621 476079991476282100782983)
            ·
              refine ⟨714119987214423151174475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476079991476282100782983 714119987214423151174475)
              ·
                refine ⟨1071179980821634726761713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714119987214423151174475 1071179980821634726761713)
                ·
                  refine ⟨803384985616226045071285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1071179980821634726761713 803384985616226045071285)
                  ·
                    refine ⟨75317342401521191725433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 803384985616226045071285 75317342401521191725433)
                    ·
                      rfl

theorem cell23_440040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_440040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440040 prefixEnd_440040 := by exact prefixLift 440040
  have htrace : WordTrace (prefixWord ++ tailWord_440040) baseStart_440040 baseEnd_440040 := by
    simpa [prefixWord, tailWord_440040, baseEnd_440040] using wordTrace_append hprefix tailTrace_440040
  have hstable : (prefixWord ++ tailWord_440040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440040).length < 2 ^ (prefixWord ++ tailWord_440040).sum := by decide
  have hdescent : baseEnd_440040 < baseStart_440040 := by decide
  rcases family_descends (prefixWord ++ tailWord_440040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440043 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 4]
def baseStart_440043 : Nat := 118140960795 + 440043 * 2 ^ 59
def prefixEnd_440043 : Nat := 4983230072969 + 3 ^ 40 * 440043 * 2
def baseEnd_440043 : Nat := 225953567646527063438785

theorem tailTrace_440043 : CollatzResearch.WordTrace tailWord_440043 prefixEnd_440043 225953567646527063438785 := by
  unfold tailWord_440043
  simp only [CollatzResearch.WordTrace]
  refine ⟨16049686744806839206244783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10699791163204559470829855 16049686744806839206244783)
  ·
    refine ⟨24074530117210258809367175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16049686744806839206244783 24074530117210258809367175)
    ·
      refine ⟨36111795175815388214050763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24074530117210258809367175 36111795175815388214050763)
      ·
        refine ⟨54167692763723082321076145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36111795175815388214050763 54167692763723082321076145)
        ·
          refine ⟨40625769572792311740807109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54167692763723082321076145 40625769572792311740807109)
          ·
            refine ⟨7617331794898558451401333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40625769572792311740807109 7617331794898558451401333)
            ·
              refine ⟨714124855771739854818875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7617331794898558451401333 714124855771739854818875)
              ·
                refine ⟨1071187283657609782228313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714124855771739854818875 1071187283657609782228313)
                ·
                  refine ⟨803390462743207336671235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1071187283657609782228313 803390462743207336671235)
                  ·
                    refine ⟨1205085694114811005006853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 803390462743207336671235 1205085694114811005006853)
                    ·
                      refine ⟨225953567646527063438785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1205085694114811005006853 225953567646527063438785)
                      ·
                        rfl

theorem cell23_440043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 4].length) (baseStart_440043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440043 prefixEnd_440043 := by exact prefixLift 440043
  have htrace : WordTrace (prefixWord ++ tailWord_440043) baseStart_440043 baseEnd_440043 := by
    simpa [prefixWord, tailWord_440043, baseEnd_440043] using wordTrace_append hprefix tailTrace_440043
  have hstable : (prefixWord ++ tailWord_440043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440043).length < 2 ^ (prefixWord ++ tailWord_440043).sum := by decide
  have hdescent : baseEnd_440043 < baseStart_440043 := by decide
  rcases family_descends (prefixWord ++ tailWord_440043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440063 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 3]
def baseStart_440063 : Nat := 118140960795 + 440063 * 2 ^ 59
def prefixEnd_440063 : Nat := 4983230072969 + 3 ^ 40 * 440063 * 2
def baseEnd_440063 : Nat := 225963837259616985188693

theorem tailTrace_440063 : CollatzResearch.WordTrace tailWord_440063 prefixEnd_440063 225963837259616985188693 := by
  unfold tailWord_440063
  simp only [CollatzResearch.WordTrace]
  refine ⟨16050416204734382621972843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10700277469822921747981895 16050416204734382621972843)
  ·
    refine ⟨24075624307101573932959265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16050416204734382621972843 24075624307101573932959265)
    ·
      refine ⟨18056718230326180449719449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24075624307101573932959265 18056718230326180449719449)
      ·
        refine ⟨13542538672744635337289587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18056718230326180449719449 13542538672744635337289587)
        ·
          refine ⟨20313808009116953005934381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13542538672744635337289587 20313808009116953005934381)
          ·
            refine ⟨7617678003418857377225393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20313808009116953005934381 7617678003418857377225393)
            ·
              refine ⟨5713258502564143032919045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7617678003418857377225393 5713258502564143032919045)
              ·
                refine ⟨1071235969230776818672321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5713258502564143032919045 1071235969230776818672321)
                ·
                  refine ⟨803426976923082614004241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1071235969230776818672321 803426976923082614004241)
                  ·
                    refine ⟨602570232692311960503181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 803426976923082614004241 602570232692311960503181)
                    ·
                      refine ⟨225963837259616985188693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 602570232692311960503181 225963837259616985188693)
                      ·
                        rfl

theorem cell23_440063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_440063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440063 prefixEnd_440063 := by exact prefixLift 440063
  have htrace : WordTrace (prefixWord ++ tailWord_440063) baseStart_440063 baseEnd_440063 := by
    simpa [prefixWord, tailWord_440063, baseEnd_440063] using wordTrace_append hprefix tailTrace_440063
  have hstable : (prefixWord ++ tailWord_440063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440063).length < 2 ^ (prefixWord ++ tailWord_440063).sum := by decide
  have hdescent : baseEnd_440063 < baseStart_440063 := by decide
  rcases family_descends (prefixWord ++ tailWord_440063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440104 : List Nat := [2, 1, 5, 1, 1, 4, 1, 3, 1, 4]
def baseStart_440104 : Nat := 118140960795 + 440104 * 2 ^ 59
def prefixEnd_440104 : Nat := 4983230072969 + 3 ^ 40 * 440104 * 2
def baseEnd_440104 : Nat := 75328296655483774925335

theorem tailTrace_440104 : CollatzResearch.WordTrace tailWord_440104 prefixEnd_440104 75328296655483774925335 := by
  unfold tailWord_440104
  simp only [CollatzResearch.WordTrace]
  refine ⟨8025955798792923312107683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10701274398390564416143577 8025955798792923312107683)
  ·
    refine ⟨12038933698189384968161525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8025955798792923312107683 12038933698189384968161525)
    ·
      refine ⟨1128650034205254840765143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12038933698189384968161525 1128650034205254840765143)
      ·
        refine ⟨1692975051307882261147715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1128650034205254840765143 1692975051307882261147715)
        ·
          refine ⟨2539462576961823391721573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692975051307882261147715 2539462576961823391721573)
          ·
            refine ⟨476149233180341885947795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2539462576961823391721573 476149233180341885947795)
            ·
              refine ⟨714223849770512828921693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476149233180341885947795 714223849770512828921693)
              ·
                refine ⟨267833943663942310845635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 714223849770512828921693 267833943663942310845635)
                ·
                  refine ⟨401750915495913466268453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267833943663942310845635 401750915495913466268453)
                  ·
                    refine ⟨75328296655483774925335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 401750915495913466268453 75328296655483774925335)
                    ·
                      rfl

theorem cell23_440104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_440104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440104 prefixEnd_440104 := by exact prefixLift 440104
  have htrace : WordTrace (prefixWord ++ tailWord_440104) baseStart_440104 baseEnd_440104 := by
    simpa [prefixWord, tailWord_440104, baseEnd_440104] using wordTrace_append hprefix tailTrace_440104
  have hstable : (prefixWord ++ tailWord_440104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440104).length < 2 ^ (prefixWord ++ tailWord_440104).sum := by decide
  have hdescent : baseEnd_440104 < baseStart_440104 := by decide
  rcases family_descends (prefixWord ++ tailWord_440104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440120 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 4, 3, 2]
def baseStart_440120 : Nat := 118140960795 + 440120 * 2 ^ 59
def prefixEnd_440120 : Nat := 4983230072969 + 3 ^ 40 * 440120 * 2
def baseEnd_440120 : Nat := 225993105656923262175931

theorem tailTrace_440120 : CollatzResearch.WordTrace tailWord_440120 prefixEnd_440120 225993105656923262175931 := by
  unfold tailWord_440120
  simp only [CollatzResearch.WordTrace]
  refine ⟨8026247582763940678398907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10701663443685254237865209 8026247582763940678398907)
  ·
    refine ⟨12039371374145911017598361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8026247582763940678398907 12039371374145911017598361)
    ·
      refine ⟨9029528530609433263198771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12039371374145911017598361 9029528530609433263198771)
      ·
        refine ⟨13544292795914149894798157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9029528530609433263198771 13544292795914149894798157)
        ·
          refine ⟨5079109798467806210549309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13544292795914149894798157 5079109798467806210549309)
          ·
            refine ⟨1904666174425427328955991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5079109798467806210549309 1904666174425427328955991)
            ·
              refine ⟨2856999261638140993433987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904666174425427328955991 2856999261638140993433987)
              ·
                refine ⟨4285498892457211490150981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2856999261638140993433987 4285498892457211490150981)
                ·
                  refine ⟨803531042335727154403309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4285498892457211490150981 803531042335727154403309)
                  ·
                    refine ⟨301324140875897682901241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 803531042335727154403309 301324140875897682901241)
                    ·
                      refine ⟨225993105656923262175931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 301324140875897682901241 225993105656923262175931)
                      ·
                        rfl

theorem cell23_440120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 4, 3, 2].length) (baseStart_440120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440120 prefixEnd_440120 := by exact prefixLift 440120
  have htrace : WordTrace (prefixWord ++ tailWord_440120) baseStart_440120 baseEnd_440120 := by
    simpa [prefixWord, tailWord_440120, baseEnd_440120] using wordTrace_append hprefix tailTrace_440120
  have hstable : (prefixWord ++ tailWord_440120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440120).length < 2 ^ (prefixWord ++ tailWord_440120).sum := by decide
  have hdescent : baseEnd_440120 < baseStart_440120 := by decide
  rcases family_descends (prefixWord ++ tailWord_440120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440121 : List Nat := [1, 2, 1, 7, 1, 1, 3, 2, 1, 4]
def baseStart_440121 : Nat := 118140960795 + 440121 * 2 ^ 59
def prefixEnd_440121 : Nat := 4983230072969 + 3 ^ 40 * 440121 * 2
def baseEnd_440121 : Nat := 75331206379192586087809

theorem tailTrace_440121 : CollatzResearch.WordTrace tailWord_440121 prefixEnd_440121 75331206379192586087809 := by
  unfold tailWord_440121
  simp only [CollatzResearch.WordTrace]
  refine ⟨16052531638524258527584217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10701687759016172351722811 16052531638524258527584217)
  ·
    refine ⟨12039398728893193895688163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16052531638524258527584217 12039398728893193895688163)
    ·
      refine ⟨18059098093339790843532245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12039398728893193895688163 18059098093339790843532245)
      ·
        refine ⟨423260111562651347895287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 18059098093339790843532245 423260111562651347895287)
        ·
          refine ⟨634890167343977021842931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423260111562651347895287 634890167343977021842931)
          ·
            refine ⟨952335251015965532764397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634890167343977021842931 952335251015965532764397)
            ·
              refine ⟨357125719130987074786649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 952335251015965532764397 357125719130987074786649)
              ·
                refine ⟨267844289348240306089987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357125719130987074786649 267844289348240306089987)
                ·
                  refine ⟨401766434022360459134981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267844289348240306089987 401766434022360459134981)
                  ·
                    refine ⟨75331206379192586087809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 401766434022360459134981 75331206379192586087809)
                    ·
                      rfl

theorem cell23_440121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 1, 4].length) (baseStart_440121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440121 prefixEnd_440121 := by exact prefixLift 440121
  have htrace : WordTrace (prefixWord ++ tailWord_440121) baseStart_440121 baseEnd_440121 := by
    simpa [prefixWord, tailWord_440121, baseEnd_440121] using wordTrace_append hprefix tailTrace_440121
  have hstable : (prefixWord ++ tailWord_440121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440121).length < 2 ^ (prefixWord ++ tailWord_440121).sum := by decide
  have hdescent : baseEnd_440121 < baseStart_440121 := by decide
  rcases family_descends (prefixWord ++ tailWord_440121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440133 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 3, 1, 4]
def baseStart_440133 : Nat := 118140960795 + 440133 * 2 ^ 59
def prefixEnd_440133 : Nat := 4983230072969 + 3 ^ 40 * 440133 * 2
def baseEnd_440133 : Nat := 225999780905431711313371

theorem tailTrace_440133 : CollatzResearch.WordTrace tailWord_440133 prefixEnd_440133 225999780905431711313371 := by
  unfold tailWord_440133
  simp only [CollatzResearch.WordTrace]
  refine ⟨16052969314480784577021053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10701979542987189718014035 16052969314480784577021053)
  ·
    refine ⟨6019863492930294216382895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16052969314480784577021053 6019863492930294216382895)
    ·
      refine ⟨9029795239395441324574343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6019863492930294216382895 9029795239395441324574343)
      ·
        refine ⟨13544692859093161986861515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9029795239395441324574343 13544692859093161986861515)
        ·
          refine ⟨20317039288639742980292273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13544692859093161986861515 20317039288639742980292273)
          ·
            refine ⟨15237779466479807235219205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20317039288639742980292273 15237779466479807235219205)
            ·
              refine ⟨2857083649964963856603601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15237779466479807235219205 2857083649964963856603601)
              ·
                refine ⟨2142812737473722892452701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2857083649964963856603601 2142812737473722892452701)
                ·
                  refine ⟨803554776552646084669763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2142812737473722892452701 803554776552646084669763)
                  ·
                    refine ⟨1205332164828969127004645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 803554776552646084669763 1205332164828969127004645)
                    ·
                      refine ⟨225999780905431711313371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1205332164828969127004645 225999780905431711313371)
                      ·
                        rfl

theorem cell23_440133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_440133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440133 prefixEnd_440133 := by exact prefixLift 440133
  have htrace : WordTrace (prefixWord ++ tailWord_440133) baseStart_440133 baseEnd_440133 := by
    simpa [prefixWord, tailWord_440133, baseEnd_440133] using wordTrace_append hprefix tailTrace_440133
  have hstable : (prefixWord ++ tailWord_440133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440133).length < 2 ^ (prefixWord ++ tailWord_440133).sum := by decide
  have hdescent : baseEnd_440133 < baseStart_440133 := by decide
  rcases family_descends (prefixWord ++ tailWord_440133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440134 : List Nat := [6, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_440134 : Nat := 118140960795 + 440134 * 2 ^ 59
def prefixEnd_440134 : Nat := 4983230072969 + 3 ^ 40 * 440134 * 2
def baseEnd_440134 : Nat := 25111143820676245266763

theorem tailTrace_440134 : CollatzResearch.WordTrace tailWord_440134 prefixEnd_440134 25111143820676245266763 := by
  unfold tailWord_440134
  simp only [CollatzResearch.WordTrace]
  refine ⟨501656430858661304618983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10702003858318107831871637 501656430858661304618983)
  ·
    refine ⟨752484646287991956928475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 501656430858661304618983 752484646287991956928475)
    ·
      refine ⟨1128726969431987935392713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 752484646287991956928475 1128726969431987935392713)
      ·
        refine ⟨846545227073990951544535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1128726969431987935392713 846545227073990951544535)
        ·
          refine ⟨1269817840610986427316803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846545227073990951544535 1269817840610986427316803)
          ·
            refine ⟨1904726760916479640975205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269817840610986427316803 1904726760916479640975205)
            ·
              refine ⟨357136267671839932682851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1904726760916479640975205 357136267671839932682851)
              ·
                refine ⟨535704401507759899024277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357136267671839932682851 535704401507759899024277)
                ·
                  refine ⟨25111143820676245266763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 535704401507759899024277 25111143820676245266763)
                  ·
                    rfl

theorem cell23_440134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_440134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440134 prefixEnd_440134 := by exact prefixLift 440134
  have htrace : WordTrace (prefixWord ++ tailWord_440134) baseStart_440134 baseEnd_440134 := by
    simpa [prefixWord, tailWord_440134, baseEnd_440134] using wordTrace_append hprefix tailTrace_440134
  have hstable : (prefixWord ++ tailWord_440134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440134).length < 2 ^ (prefixWord ++ tailWord_440134).sum := by decide
  have hdescent : baseEnd_440134 < baseStart_440134 := by decide
  rcases family_descends (prefixWord ++ tailWord_440134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440167 : List Nat := [1, 1, 5, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_440167 : Nat := 118140960795 + 440167 * 2 ^ 59
def prefixEnd_440167 : Nat := 4983230072969 + 3 ^ 40 * 440167 * 2
def baseEnd_440167 : Nat := 226017239247684578288215

theorem tailTrace_440167 : CollatzResearch.WordTrace tailWord_440167 prefixEnd_440167 226017239247684578288215 := by
  unfold tailWord_440167
  simp only [CollatzResearch.WordTrace]
  refine ⟨16054209396357608383758755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10702806264238405589172503 16054209396357608383758755)
  ·
    refine ⟨24081314094536412575638133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16054209396357608383758755 24081314094536412575638133)
    ·
      refine ⟨2257623196362788678966075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24081314094536412575638133 2257623196362788678966075)
      ·
        refine ⟨3386434794544183018449113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2257623196362788678966075 3386434794544183018449113)
        ·
          refine ⟨2539826095908137263836835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3386434794544183018449113 2539826095908137263836835)
          ·
            refine ⟨3809739143862205895755253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539826095908137263836835 3809739143862205895755253)
            ·
              refine ⟨357163044737081802727055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3809739143862205895755253 357163044737081802727055)
              ·
                refine ⟨535744567105622704090583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357163044737081802727055 535744567105622704090583)
                ·
                  refine ⟨803616850658434056135875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535744567105622704090583 803616850658434056135875)
                  ·
                    refine ⟨1205425275987651084203813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 803616850658434056135875 1205425275987651084203813)
                    ·
                      refine ⟨226017239247684578288215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1205425275987651084203813 226017239247684578288215)
                      ·
                        rfl

theorem cell23_440167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_440167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440167 prefixEnd_440167 := by exact prefixLift 440167
  have htrace : WordTrace (prefixWord ++ tailWord_440167) baseStart_440167 baseEnd_440167 := by
    simpa [prefixWord, tailWord_440167, baseEnd_440167] using wordTrace_append hprefix tailTrace_440167
  have hstable : (prefixWord ++ tailWord_440167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440167).length < 2 ^ (prefixWord ++ tailWord_440167).sum := by decide
  have hdescent : baseEnd_440167 < baseStart_440167 := by decide
  rcases family_descends (prefixWord ++ tailWord_440167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440213 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_440213 : Nat := 118140960795 + 440213 * 2 ^ 59
def prefixEnd_440213 : Nat := 4983230072969 + 3 ^ 40 * 440213 * 2
def baseEnd_440213 : Nat := 226040859357791398313003

theorem tailTrace_440213 : CollatzResearch.WordTrace tailWord_440213 prefixEnd_440213 226040859357791398313003 := by
  unfold tailWord_440213
  simp only [CollatzResearch.WordTrace]
  refine ⟨16055887154190958239933293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10703924769460638826622195 16055887154190958239933293)
  ·
    refine ⟨6020957682821609339974985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16055887154190958239933293 6020957682821609339974985)
    ·
      refine ⟨4515718262116207004981239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6020957682821609339974985 4515718262116207004981239)
      ·
        refine ⟨6773577393174310507471859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4515718262116207004981239 6773577393174310507471859)
        ·
          refine ⟨10160366089761465761207789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773577393174310507471859 10160366089761465761207789)
          ·
            refine ⟨3810137283660549660452921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10160366089761465761207789 3810137283660549660452921)
            ·
              refine ⟨2857602962745412245339691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3810137283660549660452921 2857602962745412245339691)
              ·
                refine ⟨4286404444118118368009537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857602962745412245339691 4286404444118118368009537)
                ·
                  refine ⟨3214803333088588776007153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4286404444118118368009537 3214803333088588776007153)
                  ·
                    refine ⟨2411102499816441582005365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3214803333088588776007153 2411102499816441582005365)
                    ·
                      refine ⟨226040859357791398313003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2411102499816441582005365 226040859357791398313003)
                      ·
                        rfl

theorem cell23_440213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_440213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440213 prefixEnd_440213 := by exact prefixLift 440213
  have htrace : WordTrace (prefixWord ++ tailWord_440213) baseStart_440213 baseEnd_440213 := by
    simpa [prefixWord, tailWord_440213, baseEnd_440213] using wordTrace_append hprefix tailTrace_440213
  have hstable : (prefixWord ++ tailWord_440213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440213).length < 2 ^ (prefixWord ++ tailWord_440213).sum := by decide
  have hdescent : baseEnd_440213 < baseStart_440213 := by decide
  rcases family_descends (prefixWord ++ tailWord_440213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440323 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 2, 8]
def baseStart_440323 : Nat := 118140960795 + 440323 * 2 ^ 59
def prefixEnd_440323 : Nat := 4983230072969 + 3 ^ 40 * 440323 * 2
def baseEnd_440323 : Nat := 75365780743261989312499

theorem tailTrace_440323 : CollatzResearch.WordTrace tailWord_440323 prefixEnd_440323 75365780743261989312499 := by
  unfold tailWord_440323
  simp only [CollatzResearch.WordTrace]
  refine ⟨16059899183792447026437623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10706599455861631350958415 16059899183792447026437623)
  ·
    refine ⟨24089848775688670539656435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16059899183792447026437623 24089848775688670539656435)
    ·
      refine ⟨36134773163533005809484653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24089848775688670539656435 36134773163533005809484653)
      ·
        refine ⟨13550539936324877178556745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36134773163533005809484653 13550539936324877178556745)
        ·
          refine ⟨10162904952243657883917559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13550539936324877178556745 10162904952243657883917559)
          ·
            refine ⟨15244357428365486825876339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10162904952243657883917559 15244357428365486825876339)
            ·
              refine ⟨22866536142548230238814509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15244357428365486825876339 22866536142548230238814509)
              ·
                refine ⟨8574951053455586339555441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22866536142548230238814509 8574951053455586339555441)
                ·
                  refine ⟨6431213290091689754666581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8574951053455586339555441 6431213290091689754666581)
                  ·
                    refine ⟨75365780743261989312499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6431213290091689754666581 75365780743261989312499)
                    ·
                      rfl

theorem cell23_440323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 8].length) (baseStart_440323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440323 prefixEnd_440323 := by exact prefixLift 440323
  have htrace : WordTrace (prefixWord ++ tailWord_440323) baseStart_440323 baseEnd_440323 := by
    simpa [prefixWord, tailWord_440323, baseEnd_440323] using wordTrace_append hprefix tailTrace_440323
  have hstable : (prefixWord ++ tailWord_440323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440323).length < 2 ^ (prefixWord ++ tailWord_440323).sum := by decide
  have hdescent : baseEnd_440323 < baseStart_440323 := by decide
  rcases family_descends (prefixWord ++ tailWord_440323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440327 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 2, 5]
def baseStart_440327 : Nat := 118140960795 + 440327 * 2 ^ 59
def prefixEnd_440327 : Nat := 4983230072969 + 3 ^ 40 * 440327 * 2
def baseEnd_440327 : Nat := 75366465384134650762493

theorem tailTrace_440327 : CollatzResearch.WordTrace tailWord_440327 prefixEnd_440327 75366465384134650762493 := by
  unfold tailWord_440327
  simp only [CollatzResearch.WordTrace]
  refine ⟨16060045075777955709583235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10706696717185303806388823 16060045075777955709583235)
  ·
    refine ⟨24090067613666933564374853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16060045075777955709583235 24090067613666933564374853)
    ·
      refine ⟨4516887677562550043320285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24090067613666933564374853 4516887677562550043320285)
      ·
        refine ⟨1693832879085956266245107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4516887677562550043320285 1693832879085956266245107)
        ·
          refine ⟨2540749318628934399367661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1693832879085956266245107 2540749318628934399367661)
          ·
            refine ⟨952780994485850399762873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2540749318628934399367661 952780994485850399762873)
            ·
              refine ⟨714585745864387799822155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 952780994485850399762873 714585745864387799822155)
              ·
                refine ⟨1071878618796581699733233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714585745864387799822155 1071878618796581699733233)
                ·
                  refine ⟨803908964097436274799925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1071878618796581699733233 803908964097436274799925)
                  ·
                    refine ⟨75366465384134650762493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 803908964097436274799925 75366465384134650762493)
                    ·
                      rfl

theorem cell23_440327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_440327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440327 prefixEnd_440327 := by exact prefixLift 440327
  have htrace : WordTrace (prefixWord ++ tailWord_440327) baseStart_440327 baseEnd_440327 := by
    simpa [prefixWord, tailWord_440327, baseEnd_440327] using wordTrace_append hprefix tailTrace_440327
  have hstable : (prefixWord ++ tailWord_440327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440327).length < 2 ^ (prefixWord ++ tailWord_440327).sum := by decide
  have hdescent : baseEnd_440327 < baseStart_440327 := by decide
  rcases family_descends (prefixWord ++ tailWord_440327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440374 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_440374 : Nat := 118140960795 + 440374 * 2 ^ 59
def prefixEnd_440374 : Nat := 4983230072969 + 3 ^ 40 * 440374 * 2
def baseEnd_440374 : Nat := 75374509914388422799921

theorem tailTrace_440374 : CollatzResearch.WordTrace tailWord_440374 prefixEnd_440374 75374509914388422799921 := by
  unfold tailWord_440374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1003859956662980171034011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10707839537738455157696117 1003859956662980171034011)
  ·
    refine ⟨1505789934994470256551017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1003859956662980171034011 1505789934994470256551017)
    ·
      refine ⟨1129342451245852692413263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1505789934994470256551017 1129342451245852692413263)
      ·
        refine ⟨1694013676868779038619895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129342451245852692413263 1694013676868779038619895)
        ·
          refine ⟨2541020515303168557929843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694013676868779038619895 2541020515303168557929843)
          ·
            refine ⟨3811530772954752836894765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2541020515303168557929843 3811530772954752836894765)
            ·
              refine ⟨1429324039858032313835537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3811530772954752836894765 1429324039858032313835537)
              ·
                refine ⟨1071993029893524235376653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1429324039858032313835537 1071993029893524235376653)
                ·
                  refine ⟨401997386210071588266245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1071993029893524235376653 401997386210071588266245)
                  ·
                    refine ⟨75374509914388422799921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 401997386210071588266245 75374509914388422799921)
                    ·
                      rfl

theorem cell23_440374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_440374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440374 prefixEnd_440374 := by exact prefixLift 440374
  have htrace : WordTrace (prefixWord ++ tailWord_440374) baseStart_440374 baseEnd_440374 := by
    simpa [prefixWord, tailWord_440374, baseEnd_440374] using wordTrace_append hprefix tailTrace_440374
  have hstable : (prefixWord ++ tailWord_440374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440374).length < 2 ^ (prefixWord ++ tailWord_440374).sum := by decide
  have hdescent : baseEnd_440374 < baseStart_440374 := by decide
  rcases family_descends (prefixWord ++ tailWord_440374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440384 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 3]
def baseStart_440384 : Nat := 118140960795 + 440384 * 2 ^ 59
def prefixEnd_440384 : Nat := 4983230072969 + 3 ^ 40 * 440384 * 2
def baseEnd_440384 : Nat := 226128664549710229274717

theorem tailTrace_440384 : CollatzResearch.WordTrace tailWord_440384 prefixEnd_440384 226128664549710229274717 := by
  unfold tailWord_440384
  simp only [CollatzResearch.WordTrace]
  refine ⟨8031062018285727222204103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10708082691047636296272137 8031062018285727222204103)
  ·
    refine ⟨12046593027428590833306155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8031062018285727222204103 12046593027428590833306155)
    ·
      refine ⟨18069889541142886249959233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12046593027428590833306155 18069889541142886249959233)
      ·
        refine ⟨13552417155857164687469425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18069889541142886249959233 13552417155857164687469425)
        ·
          refine ⟨10164312866892873515602069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13552417155857164687469425 10164312866892873515602069)
          ·
            refine ⟨476452165635603446043847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10164312866892873515602069 476452165635603446043847)
            ·
              refine ⟨714678248453405169065771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476452165635603446043847 714678248453405169065771)
              ·
                refine ⟨1072017372680107753598657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714678248453405169065771 1072017372680107753598657)
                ·
                  refine ⟨804013029510080815198993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1072017372680107753598657 804013029510080815198993)
                  ·
                    refine ⟨603009772132560611399245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 804013029510080815198993 603009772132560611399245)
                    ·
                      refine ⟨226128664549710229274717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 603009772132560611399245 226128664549710229274717)
                      ·
                        rfl

theorem cell23_440384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_440384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440384 prefixEnd_440384 := by exact prefixLift 440384
  have htrace : WordTrace (prefixWord ++ tailWord_440384) baseStart_440384 baseEnd_440384 := by
    simpa [prefixWord, tailWord_440384, baseEnd_440384] using wordTrace_append hprefix tailTrace_440384
  have hstable : (prefixWord ++ tailWord_440384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440384).length < 2 ^ (prefixWord ++ tailWord_440384).sum := by decide
  have hdescent : baseEnd_440384 < baseStart_440384 := by decide
  rcases family_descends (prefixWord ++ tailWord_440384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440434 : List Nat := [3, 2, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_440434 : Nat := 118140960795 + 440434 * 2 ^ 59
def prefixEnd_440434 : Nat := 4983230072969 + 3 ^ 40 * 440434 * 2
def baseEnd_440434 : Nat := 75384779527478344549829

theorem tailTrace_440434 : CollatzResearch.WordTrace tailWord_440434 prefixEnd_440434 75384779527478344549829 := by
  unfold tailWord_440434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015986921597578245932089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10709298457593541989152237 4015986921597578245932089)
  ·
    refine ⟨3011990191198183684449067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4015986921597578245932089 3011990191198183684449067)
    ·
      refine ⟨4517985286797275526673601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3011990191198183684449067 4517985286797275526673601)
      ·
        refine ⟨3388488965097956645005201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4517985286797275526673601 3388488965097956645005201)
        ·
          refine ⟨2541366723823467483753901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3388488965097956645005201 2541366723823467483753901)
          ·
            refine ⟨953012521433800306407713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2541366723823467483753901 953012521433800306407713)
            ·
              refine ⟨714759391075350229805785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953012521433800306407713 714759391075350229805785)
              ·
                refine ⟨536069543306512672354339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714759391075350229805785 536069543306512672354339)
                ·
                  refine ⟨804104314959769008531509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536069543306512672354339 804104314959769008531509)
                  ·
                    refine ⟨75384779527478344549829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 804104314959769008531509 75384779527478344549829)
                    ·
                      rfl

theorem cell23_440434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_440434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440434 prefixEnd_440434 := by exact prefixLift 440434
  have htrace : WordTrace (prefixWord ++ tailWord_440434) baseStart_440434 baseEnd_440434 := by
    simpa [prefixWord, tailWord_440434, baseEnd_440434] using wordTrace_append hprefix tailTrace_440434
  have hstable : (prefixWord ++ tailWord_440434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440434).length < 2 ^ (prefixWord ++ tailWord_440434).sum := by decide
  have hdescent : baseEnd_440434 < baseStart_440434 := by decide
  rcases family_descends (prefixWord ++ tailWord_440434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440440 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_440440 : Nat := 118140960795 + 440440 * 2 ^ 59
def prefixEnd_440440 : Nat := 4983230072969 + 3 ^ 40 * 440440 * 2
def baseEnd_440440 : Nat := 226157419466362010174459

theorem tailTrace_440440 : CollatzResearch.WordTrace tailWord_440440 prefixEnd_440440 226157419466362010174459 := by
  unfold tailWord_440440
  simp only [CollatzResearch.WordTrace]
  refine ⟨8032083262184288004223387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10709444349579050672297849 8032083262184288004223387)
  ·
    refine ⟨12048124893276432006335081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8032083262184288004223387 12048124893276432006335081)
    ·
      refine ⟨9036093669957324004751311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12048124893276432006335081 9036093669957324004751311)
      ·
        refine ⟨13554140504935986007126967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9036093669957324004751311 13554140504935986007126967)
        ·
          refine ⟨20331210757403979010690451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13554140504935986007126967 20331210757403979010690451)
          ·
            refine ⟨30496816136105968516035677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20331210757403979010690451 30496816136105968516035677)
            ·
              refine ⟨11436306051039738193513379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30496816136105968516035677 11436306051039738193513379)
              ·
                refine ⟨17154459076559607290270069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11436306051039738193513379 17154459076559607290270069)
                ·
                  refine ⟨1608230538427463183462819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17154459076559607290270069 1608230538427463183462819)
                  ·
                    refine ⟨2412345807641194775194229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1608230538427463183462819 2412345807641194775194229)
                    ·
                      refine ⟨226157419466362010174459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2412345807641194775194229 226157419466362010174459)
                      ·
                        rfl

theorem cell23_440440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_440440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440440 prefixEnd_440440 := by exact prefixLift 440440
  have htrace : WordTrace (prefixWord ++ tailWord_440440) baseStart_440440 baseEnd_440440 := by
    simpa [prefixWord, tailWord_440440, baseEnd_440440] using wordTrace_append hprefix tailTrace_440440
  have hstable : (prefixWord ++ tailWord_440440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440440).length < 2 ^ (prefixWord ++ tailWord_440440).sum := by decide
  have hdescent : baseEnd_440440 < baseStart_440440 := by decide
  rcases family_descends (prefixWord ++ tailWord_440440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440457 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 1, 1, 5]
def baseStart_440457 : Nat := 118140960795 + 440457 * 2 ^ 59
def prefixEnd_440457 : Nat := 4983230072969 + 3 ^ 40 * 440457 * 2
def baseEnd_440457 : Nat := 226166148637488443661881

theorem tailTrace_440457 : CollatzResearch.WordTrace tailWord_440457 prefixEnd_440457 226166148637488443661881 := by
  unfold tailWord_440457
  simp only [CollatzResearch.WordTrace]
  refine ⟨16064786565306987911815625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10709857710204658607877083 16064786565306987911815625)
  ·
    refine ⟨12048589923980240933861719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16064786565306987911815625 12048589923980240933861719)
    ·
      refine ⟨18072884885970361400792579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12048589923980240933861719 18072884885970361400792579)
      ·
        refine ⟨27109327328955542101188869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18072884885970361400792579 27109327328955542101188869)
        ·
          refine ⟨5082998874179164143972913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27109327328955542101188869 5082998874179164143972913)
          ·
            refine ⟨3812249155634373107979685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5082998874179164143972913 3812249155634373107979685)
            ·
              refine ⟨714796716681444957746191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3812249155634373107979685 714796716681444957746191)
              ·
                refine ⟨1072195075022167436619287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714796716681444957746191 1072195075022167436619287)
                ·
                  refine ⟨1608292612533251154928931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072195075022167436619287 1608292612533251154928931)
                  ·
                    refine ⟨2412438918799876732393397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1608292612533251154928931 2412438918799876732393397)
                    ·
                      refine ⟨226166148637488443661881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2412438918799876732393397 226166148637488443661881)
                      ·
                        rfl

theorem cell23_440457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 1, 5].length) (baseStart_440457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440457 prefixEnd_440457 := by exact prefixLift 440457
  have htrace : WordTrace (prefixWord ++ tailWord_440457) baseStart_440457 baseEnd_440457 := by
    simpa [prefixWord, tailWord_440457, baseEnd_440457] using wordTrace_append hprefix tailTrace_440457
  have hstable : (prefixWord ++ tailWord_440457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440457).length < 2 ^ (prefixWord ++ tailWord_440457).sum := by decide
  have hdescent : baseEnd_440457 < baseStart_440457 := by decide
  rcases family_descends (prefixWord ++ tailWord_440457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440477 : List Nat := [1, 4, 2, 1, 1, 4, 2, 8]
def baseStart_440477 : Nat := 118140960795 + 440477 * 2 ^ 59
def prefixEnd_440477 : Nat := 4983230072969 + 3 ^ 40 * 440477 * 2
def baseEnd_440477 : Nat := 8376904379651050570807

theorem tailTrace_440477 : CollatzResearch.WordTrace tailWord_440477 prefixEnd_440477 8376904379651050570807 := by
  unfold tailWord_440477
  simp only [CollatzResearch.WordTrace]
  refine ⟨16065516025234531327543685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10710344016823020885029123 16065516025234531327543685)
  ·
    refine ⟨3012284254731474623914441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16065516025234531327543685 3012284254731474623914441)
    ·
      refine ⟨2259213191048605967935831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3012284254731474623914441 2259213191048605967935831)
      ·
        refine ⟨3388819786572908951903747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2259213191048605967935831 3388819786572908951903747)
        ·
          refine ⟨5083229679859363427855621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3388819786572908951903747 5083229679859363427855621)
          ·
            refine ⟨953105564973630642722929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5083229679859363427855621 953105564973630642722929)
            ·
              refine ⟨714829173730222982042197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953105564973630642722929 714829173730222982042197)
              ·
                refine ⟨8376904379651050570807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 714829173730222982042197 8376904379651050570807)
                ·
                  rfl

theorem cell23_440477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 8].length) (baseStart_440477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440477 prefixEnd_440477 := by exact prefixLift 440477
  have htrace : WordTrace (prefixWord ++ tailWord_440477) baseStart_440477 baseEnd_440477 := by
    simpa [prefixWord, tailWord_440477, baseEnd_440477] using wordTrace_append hprefix tailTrace_440477
  have hstable : (prefixWord ++ tailWord_440477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440477).length < 2 ^ (prefixWord ++ tailWord_440477).sum := by decide
  have hdescent : baseEnd_440477 < baseStart_440477 := by decide
  rcases family_descends (prefixWord ++ tailWord_440477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440481 : List Nat := [1, 2, 3, 3, 1, 2, 4, 1, 2, 4]
def baseStart_440481 : Nat := 118140960795 + 440481 * 2 ^ 59
def prefixEnd_440481 : Nat := 4983230072969 + 3 ^ 40 * 440481 * 2
def baseEnd_440481 : Nat := 75392824057732116587257

theorem tailTrace_440481 : CollatzResearch.WordTrace tailWord_440481 prefixEnd_440481 75392824057732116587257 := by
  unfold tailWord_440481
  simp only [CollatzResearch.WordTrace]
  refine ⟨16065661917220040010689297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10710441278146693340459531 16065661917220040010689297)
  ·
    refine ⟨12049246437915030008016973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16065661917220040010689297 12049246437915030008016973)
    ·
      refine ⟨4518467414218136253006365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12049246437915030008016973 4518467414218136253006365)
      ·
        refine ⟨1694425280331801094877387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4518467414218136253006365 1694425280331801094877387)
        ·
          refine ⟨2541637920497701642316081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694425280331801094877387 2541637920497701642316081)
          ·
            refine ⟨1906228440373276231737061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2541637920497701642316081 1906228440373276231737061)
            ·
              refine ⟨357417832569989293450699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1906228440373276231737061 357417832569989293450699)
              ·
                refine ⟨536126748854983940176049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357417832569989293450699 536126748854983940176049)
                ·
                  refine ⟨402095061641237955132037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536126748854983940176049 402095061641237955132037)
                  ·
                    refine ⟨75392824057732116587257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 402095061641237955132037 75392824057732116587257)
                    ·
                      rfl

theorem cell23_440481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_440481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440481 prefixEnd_440481 := by exact prefixLift 440481
  have htrace : WordTrace (prefixWord ++ tailWord_440481) baseStart_440481 baseEnd_440481 := by
    simpa [prefixWord, tailWord_440481, baseEnd_440481] using wordTrace_append hprefix tailTrace_440481
  have hstable : (prefixWord ++ tailWord_440481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440481).length < 2 ^ (prefixWord ++ tailWord_440481).sum := by decide
  have hdescent : baseEnd_440481 < baseStart_440481 := by decide
  rcases family_descends (prefixWord ++ tailWord_440481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440501 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_440501 : Nat := 118140960795 + 440501 * 2 ^ 59
def prefixEnd_440501 : Nat := 4983230072969 + 3 ^ 40 * 440501 * 2
def baseEnd_440501 : Nat := 226188741786286271511679

theorem tailTrace_440501 : CollatzResearch.WordTrace tailWord_440501 prefixEnd_440501 226188741786286271511679 := by
  unfold tailWord_440501
  simp only [CollatzResearch.WordTrace]
  refine ⟨16066391377147583426417357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10710927584765055617611571 16066391377147583426417357)
  ·
    refine ⟨6024896766430343784906509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16066391377147583426417357 6024896766430343784906509)
    ·
      refine ⟨2259336287411378919339941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6024896766430343784906509 2259336287411378919339941)
      ·
        refine ⟨423625553889633547376239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2259336287411378919339941 423625553889633547376239)
        ·
          refine ⟨635438330834450321064359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423625553889633547376239 635438330834450321064359)
          ·
            refine ⟨953157496251675481596539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635438330834450321064359 953157496251675481596539)
            ·
              refine ⟨1429736244377513222394809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953157496251675481596539 1429736244377513222394809)
              ·
                refine ⟨1072302183283134916796107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1429736244377513222394809 1072302183283134916796107)
                ·
                  refine ⟨1608453274924702375194161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072302183283134916796107 1608453274924702375194161)
                  ·
                    refine ⟨1206339956193526781395621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1608453274924702375194161 1206339956193526781395621)
                    ·
                      refine ⟨226188741786286271511679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1206339956193526781395621 226188741786286271511679)
                      ·
                        rfl

theorem cell23_440501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_440501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440501 prefixEnd_440501 := by exact prefixLift 440501
  have htrace : WordTrace (prefixWord ++ tailWord_440501) baseStart_440501 baseEnd_440501 := by
    simpa [prefixWord, tailWord_440501, baseEnd_440501] using wordTrace_append hprefix tailTrace_440501
  have hstable : (prefixWord ++ tailWord_440501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440501).length < 2 ^ (prefixWord ++ tailWord_440501).sum := by decide
  have hdescent : baseEnd_440501 < baseStart_440501 := by decide
  rcases family_descends (prefixWord ++ tailWord_440501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440508 : List Nat := [2, 2, 2, 3, 3, 1, 3, 1, 1, 2, 3]
def baseStart_440508 : Nat := 118140960795 + 440508 * 2 ^ 59
def prefixEnd_440508 : Nat := 4983230072969 + 3 ^ 40 * 440508 * 2
def baseEnd_440508 : Nat := 226192336150867744124147

theorem tailTrace_440508 : CollatzResearch.WordTrace tailWord_440508 prefixEnd_440508 226192336150867744124147 := by
  unfold tailWord_440508
  simp only [CollatzResearch.WordTrace]
  refine ⟨8033323344061111810961089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10711097792081482414614785 8033323344061111810961089)
  ·
    refine ⟨6024992508045833858220817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8033323344061111810961089 6024992508045833858220817)
    ·
      refine ⟨4518744381034375393665613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6024992508045833858220817 4518744381034375393665613)
      ·
        refine ⟨1694529142887890772624605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4518744381034375393665613 1694529142887890772624605)
        ·
          refine ⟨635448428582959039734227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1694529142887890772624605 635448428582959039734227)
          ·
            refine ⟨953172642874438559601341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635448428582959039734227 953172642874438559601341)
            ·
              refine ⟨357439741077914459850503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 953172642874438559601341 357439741077914459850503)
              ·
                refine ⟨536159611616871689775755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357439741077914459850503 536159611616871689775755)
                ·
                  refine ⟨804239417425307534663633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536159611616871689775755 804239417425307534663633)
                  ·
                    refine ⟨603179563068980650997725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 804239417425307534663633 603179563068980650997725)
                    ·
                      refine ⟨226192336150867744124147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 603179563068980650997725 226192336150867744124147)
                      ·
                        rfl

theorem cell23_440508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_440508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440508 prefixEnd_440508 := by exact prefixLift 440508
  have htrace : WordTrace (prefixWord ++ tailWord_440508) baseStart_440508 baseEnd_440508 := by
    simpa [prefixWord, tailWord_440508, baseEnd_440508] using wordTrace_append hprefix tailTrace_440508
  have hstable : (prefixWord ++ tailWord_440508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440508).length < 2 ^ (prefixWord ++ tailWord_440508).sum := by decide
  have hdescent : baseEnd_440508 < baseStart_440508 := by decide
  rcases family_descends (prefixWord ++ tailWord_440508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440574 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_440574 : Nat := 118140960795 + 440574 * 2 ^ 59
def prefixEnd_440574 : Nat := 4983230072969 + 3 ^ 40 * 440574 * 2
def baseEnd_440574 : Nat := 226226225874064485898843

theorem tailTrace_440574 : CollatzResearch.WordTrace tailWord_440574 prefixEnd_440574 226226225874064485898843 := by
  unfold tailWord_440574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2008631738235389611728097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10712702603922077929216517 2008631738235389611728097)
  ·
    refine ⟨1506473803676542208796073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2008631738235389611728097 1506473803676542208796073)
    ·
      refine ⟨1129855352757406656597055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1506473803676542208796073 1129855352757406656597055)
      ·
        refine ⟨1694783029136109984895583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129855352757406656597055 1694783029136109984895583)
        ·
          refine ⟨2542174543704164977343375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694783029136109984895583 2542174543704164977343375)
          ·
            refine ⟨3813261815556247466015063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542174543704164977343375 3813261815556247466015063)
            ·
              refine ⟨5719892723334371199022595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3813261815556247466015063 5719892723334371199022595)
              ·
                refine ⟨8579839085001556798533893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5719892723334371199022595 8579839085001556798533893)
                ·
                  refine ⟨1608719828437791899725105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8579839085001556798533893 1608719828437791899725105)
                  ·
                    refine ⟨1206539871328343924793829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1608719828437791899725105 1206539871328343924793829)
                    ·
                      refine ⟨226226225874064485898843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1206539871328343924793829 226226225874064485898843)
                      ·
                        rfl

theorem cell23_440574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_440574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440574 prefixEnd_440574 := by exact prefixLift 440574
  have htrace : WordTrace (prefixWord ++ tailWord_440574) baseStart_440574 baseEnd_440574 := by
    simpa [prefixWord, tailWord_440574, baseEnd_440574] using wordTrace_append hprefix tailTrace_440574
  have hstable : (prefixWord ++ tailWord_440574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440574).length < 2 ^ (prefixWord ++ tailWord_440574).sum := by decide
  have hdescent : baseEnd_440574 < baseStart_440574 := by decide
  rcases family_descends (prefixWord ++ tailWord_440574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440584 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 7]
def baseStart_440584 : Nat := 118140960795 + 440584 * 2 ^ 59
def prefixEnd_440584 : Nat := 4983230072969 + 3 ^ 40 * 440584 * 2
def baseEnd_440584 : Nat := 25136817853401049641533

theorem tailTrace_440584 : CollatzResearch.WordTrace tailWord_440584 prefixEnd_440584 25136817853401049641533 := by
  unfold tailWord_440584
  simp only [CollatzResearch.WordTrace]
  refine ⟨8034709317923444300844403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10712945757231259067792537 8034709317923444300844403)
  ·
    refine ⟨12052063976885166451266605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8034709317923444300844403 12052063976885166451266605)
    ·
      refine ⟨4519523991331937419224977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12052063976885166451266605 4519523991331937419224977)
      ·
        refine ⟨3389642993498953064418733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4519523991331937419224977 3389642993498953064418733)
        ·
          refine ⟨1271116122562107399157025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3389642993498953064418733 1271116122562107399157025)
          ·
            refine ⟨953337091921580549367769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1271116122562107399157025 953337091921580549367769)
            ·
              refine ⟨715002818941185412025827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953337091921580549367769 715002818941185412025827)
              ·
                refine ⟨1072504228411778118038741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715002818941185412025827 1072504228411778118038741)
                ·
                  refine ⟨25136817853401049641533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1072504228411778118038741 25136817853401049641533)
                  ·
                    rfl

theorem cell23_440584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 7].length) (baseStart_440584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440584 prefixEnd_440584 := by exact prefixLift 440584
  have htrace : WordTrace (prefixWord ++ tailWord_440584) baseStart_440584 baseEnd_440584 := by
    simpa [prefixWord, tailWord_440584, baseEnd_440584] using wordTrace_append hprefix tailTrace_440584
  have hstable : (prefixWord ++ tailWord_440584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440584).length < 2 ^ (prefixWord ++ tailWord_440584).sum := by decide
  have hdescent : baseEnd_440584 < baseStart_440584 := by decide
  rcases family_descends (prefixWord ++ tailWord_440584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440597 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 1, 7]
def baseStart_440597 : Nat := 118140960795 + 440597 * 2 ^ 59
def prefixEnd_440597 : Nat := 4983230072969 + 3 ^ 40 * 440597 * 2
def baseEnd_440597 : Nat := 75412678643039298637079

theorem tailTrace_440597 : CollatzResearch.WordTrace tailWord_440597 prefixEnd_440597 75412678643039298637079 := by
  unfold tailWord_440597
  simp only [CollatzResearch.WordTrace]
  refine ⟨16069892784799791821912045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10713261856533194547941363 16069892784799791821912045)
  ·
    refine ⟨6026209794299921933217017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16069892784799791821912045 6026209794299921933217017)
    ·
      refine ⟨4519657345724941449912763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6026209794299921933217017 4519657345724941449912763)
      ·
        refine ⟨6779486018587412174869145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4519657345724941449912763 6779486018587412174869145)
        ·
          refine ⟨5084614513940559131151859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6779486018587412174869145 5084614513940559131151859)
          ·
            refine ⟨7626921770910838696727789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084614513940559131151859 7626921770910838696727789)
            ·
              refine ⟨2860095664091564511272921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7626921770910838696727789 2860095664091564511272921)
              ·
                refine ⟨2145071748068673383454691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2860095664091564511272921 2145071748068673383454691)
                ·
                  refine ⟨3217607622103010075182037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145071748068673383454691 3217607622103010075182037)
                  ·
                    refine ⟨75412678643039298637079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3217607622103010075182037 75412678643039298637079)
                    ·
                      rfl

theorem cell23_440597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_440597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440597 prefixEnd_440597 := by exact prefixLift 440597
  have htrace : WordTrace (prefixWord ++ tailWord_440597) baseStart_440597 baseEnd_440597 := by
    simpa [prefixWord, tailWord_440597, baseEnd_440597] using wordTrace_append hprefix tailTrace_440597
  have hstable : (prefixWord ++ tailWord_440597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440597).length < 2 ^ (prefixWord ++ tailWord_440597).sum := by decide
  have hdescent : baseEnd_440597 < baseStart_440597 := by decide
  rcases family_descends (prefixWord ++ tailWord_440597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440634 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4]
def baseStart_440634 : Nat := 118140960795 + 440634 * 2 ^ 59
def prefixEnd_440634 : Nat := 4983230072969 + 3 ^ 40 * 440634 * 2
def baseEnd_440634 : Nat := 226257034713334251148567

theorem tailTrace_440634 : CollatzResearch.WordTrace tailWord_440634 prefixEnd_440634 226257034713334251148567 := by
  unfold tailWord_440634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4017810571416436785252239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10714161523777164760672637 4017810571416436785252239)
  ·
    refine ⟨6026715857124655177878359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4017810571416436785252239 6026715857124655177878359)
    ·
      refine ⟨9040073785686982766817539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6026715857124655177878359 9040073785686982766817539)
      ·
        refine ⟨13560110678530474150226309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9040073785686982766817539 13560110678530474150226309)
        ·
          refine ⟨2542520752224463903167433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13560110678530474150226309 2542520752224463903167433)
          ·
            refine ⟨1906890564168347927375575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2542520752224463903167433 1906890564168347927375575)
            ·
              refine ⟨2860335846252521891063363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906890564168347927375575 2860335846252521891063363)
              ·
                refine ⟨4290503769378782836595045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860335846252521891063363 4290503769378782836595045)
                ·
                  refine ⟨804469456758521781861571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4290503769378782836595045 804469456758521781861571)
                  ·
                    refine ⟨1206704185137782672792357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 804469456758521781861571 1206704185137782672792357)
                    ·
                      refine ⟨226257034713334251148567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1206704185137782672792357 226257034713334251148567)
                      ·
                        rfl

theorem cell23_440634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_440634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440634 prefixEnd_440634 := by exact prefixLift 440634
  have htrace : WordTrace (prefixWord ++ tailWord_440634) baseStart_440634 baseEnd_440634 := by
    simpa [prefixWord, tailWord_440634, baseEnd_440634] using wordTrace_append hprefix tailTrace_440634
  have hstable : (prefixWord ++ tailWord_440634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440634).length < 2 ^ (prefixWord ++ tailWord_440634).sum := by decide
  have hdescent : baseEnd_440634 < baseStart_440634 := by decide
  rcases family_descends (prefixWord ++ tailWord_440634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440641 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_440641 : Nat := 118140960795 + 440641 * 2 ^ 59
def prefixEnd_440641 : Nat := 4983230072969 + 3 ^ 40 * 440641 * 2
def baseEnd_440641 : Nat := 226260629077915723761035

theorem tailTrace_440641 : CollatzResearch.WordTrace tailWord_440641 prefixEnd_440641 226260629077915723761035 := by
  unfold tailWord_440641
  simp only [CollatzResearch.WordTrace]
  refine ⟨16071497596640387336513777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10714331731093591557675851 16071497596640387336513777)
  ·
    refine ⟨12053623197480290502385333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16071497596640387336513777 12053623197480290502385333)
    ·
      refine ⟨1130027174763777234598625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12053623197480290502385333 1130027174763777234598625)
      ·
        refine ⟨847520381072832925948969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1130027174763777234598625 847520381072832925948969)
        ·
          refine ⟨635640285804624694461727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 847520381072832925948969 635640285804624694461727)
          ·
            refine ⟨953460428706937041692591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635640285804624694461727 953460428706937041692591)
            ·
              refine ⟨1430190643060405562538887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953460428706937041692591 1430190643060405562538887)
              ·
                refine ⟨2145285964590608343808331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430190643060405562538887 2145285964590608343808331)
                ·
                  refine ⟨3217928946885912515712497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145285964590608343808331 3217928946885912515712497)
                  ·
                    refine ⟨2413446710164434386784373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3217928946885912515712497 2413446710164434386784373)
                    ·
                      refine ⟨226260629077915723761035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2413446710164434386784373 226260629077915723761035)
                      ·
                        rfl

theorem cell23_440641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_440641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440641 prefixEnd_440641 := by exact prefixLift 440641
  have htrace : WordTrace (prefixWord ++ tailWord_440641) baseStart_440641 baseEnd_440641 := by
    simpa [prefixWord, tailWord_440641, baseEnd_440641] using wordTrace_append hprefix tailTrace_440641
  have hstable : (prefixWord ++ tailWord_440641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440641).length < 2 ^ (prefixWord ++ tailWord_440641).sum := by decide
  have hdescent : baseEnd_440641 < baseStart_440641 := by decide
  rcases family_descends (prefixWord ++ tailWord_440641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440654 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_440654 : Nat := 118140960795 + 440654 * 2 ^ 59
def prefixEnd_440654 : Nat := 4983230072969 + 3 ^ 40 * 440654 * 2
def baseEnd_440654 : Nat := 226267304326424172898475

theorem tailTrace_440654 : CollatzResearch.WordTrace tailWord_440654 prefixEnd_440654 226267304326424172898475 := by
  unfold tailWord_440654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2008996468199161319592127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10714647830395527037824677 2008996468199161319592127)
  ·
    refine ⟨3013494702298741979388191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2008996468199161319592127 3013494702298741979388191)
    ·
      refine ⟨4520242053448112969082287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3013494702298741979388191 4520242053448112969082287)
      ·
        refine ⟨6780363080172169453623431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4520242053448112969082287 6780363080172169453623431)
        ·
          refine ⟨10170544620258254180435147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6780363080172169453623431 10170544620258254180435147)
          ·
            refine ⟨15255816930387381270652721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10170544620258254180435147 15255816930387381270652721)
            ·
              refine ⟨11441862697790535952989541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15255816930387381270652721 11441862697790535952989541)
              ·
                refine ⟨2145349255835725491185539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11441862697790535952989541 2145349255835725491185539)
                ·
                  refine ⟨3218023883753588236778309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145349255835725491185539 3218023883753588236778309)
                  ·
                    refine ⟨603379478203797794395933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3218023883753588236778309 603379478203797794395933)
                    ·
                      refine ⟨226267304326424172898475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 603379478203797794395933 226267304326424172898475)
                      ·
                        rfl

theorem cell23_440654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_440654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440654 prefixEnd_440654 := by exact prefixLift 440654
  have htrace : WordTrace (prefixWord ++ tailWord_440654) baseStart_440654 baseEnd_440654 := by
    simpa [prefixWord, tailWord_440654, baseEnd_440654] using wordTrace_append hprefix tailTrace_440654
  have hstable : (prefixWord ++ tailWord_440654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440654).length < 2 ^ (prefixWord ++ tailWord_440654).sum := by decide
  have hdescent : baseEnd_440654 < baseStart_440654 := by decide
  rcases family_descends (prefixWord ++ tailWord_440654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440711 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 1, 5, 2]
def baseStart_440711 : Nat := 118140960795 + 440711 * 2 ^ 59
def prefixEnd_440711 : Nat := 4983230072969 + 3 ^ 40 * 440711 * 2
def baseEnd_440711 : Nat := 226296572723730449885713

theorem tailTrace_440711 : CollatzResearch.WordTrace tailWord_440711 prefixEnd_440711 226296572723730449885713 := by
  unfold tailWord_440711
  simp only [CollatzResearch.WordTrace]
  refine ⟨16074050706386789291561987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10716033804257859527707991 16074050706386789291561987)
  ·
    refine ⟨24111076059580183937342981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16074050706386789291561987 24111076059580183937342981)
    ·
      refine ⟨4520826761171284488251809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24111076059580183937342981 4520826761171284488251809)
      ·
        refine ⟨3390620070878463366188857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4520826761171284488251809 3390620070878463366188857)
        ·
          refine ⟨2542965053158847524641643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3390620070878463366188857 2542965053158847524641643)
          ·
            refine ⟨3814447579738271286962465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542965053158847524641643 3814447579738271286962465)
            ·
              refine ⟨2860835684803703465221849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3814447579738271286962465 2860835684803703465221849)
              ·
                refine ⟨2145626763602777598916387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2860835684803703465221849 2145626763602777598916387)
                ·
                  refine ⟨3218440145404166398374581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145626763602777598916387 3218440145404166398374581)
                  ·
                    refine ⟨301728763631640599847617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3218440145404166398374581 301728763631640599847617)
                    ·
                      refine ⟨226296572723730449885713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 301728763631640599847617 226296572723730449885713)
                      ·
                        rfl

theorem cell23_440711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_440711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440711 prefixEnd_440711 := by exact prefixLift 440711
  have htrace : WordTrace (prefixWord ++ tailWord_440711) baseStart_440711 baseEnd_440711 := by
    simpa [prefixWord, tailWord_440711, baseEnd_440711] using wordTrace_append hprefix tailTrace_440711
  have hstable : (prefixWord ++ tailWord_440711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440711).length < 2 ^ (prefixWord ++ tailWord_440711).sum := by decide
  have hdescent : baseEnd_440711 < baseStart_440711 := by decide
  rcases family_descends (prefixWord ++ tailWord_440711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440718 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3]
def baseStart_440718 : Nat := 118140960795 + 440718 * 2 ^ 59
def prefixEnd_440718 : Nat := 4983230072969 + 3 ^ 40 * 440718 * 2
def baseEnd_440718 : Nat := 226300167088311922498181

theorem tailTrace_440718 : CollatzResearch.WordTrace tailWord_440718 prefixEnd_440718 226300167088311922498181 := by
  unfold tailWord_440718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2009288252170178685883351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10716204011574286324711205 2009288252170178685883351)
  ·
    refine ⟨3013932378255268028825027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2009288252170178685883351 3013932378255268028825027)
    ·
      refine ⟨4520898567382902043237541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3013932378255268028825027 4520898567382902043237541)
      ·
        refine ⟨847668481384294133107039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4520898567382902043237541 847668481384294133107039)
        ·
          refine ⟨1271502722076441199660559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847668481384294133107039 1271502722076441199660559)
          ·
            refine ⟨1907254083114661799490839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271502722076441199660559 1907254083114661799490839)
            ·
              refine ⟨2860881124671992699236259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1907254083114661799490839 2860881124671992699236259)
              ·
                refine ⟨4291321687007989048854389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860881124671992699236259 4291321687007989048854389)
                ·
                  refine ⟨402311408156998973330099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4291321687007989048854389 402311408156998973330099)
                  ·
                    refine ⟨603467112235498459995149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 402311408156998973330099 603467112235498459995149)
                    ·
                      refine ⟨226300167088311922498181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 603467112235498459995149 226300167088311922498181)
                      ·
                        rfl

theorem cell23_440718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_440718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440718 prefixEnd_440718 := by exact prefixLift 440718
  have htrace : WordTrace (prefixWord ++ tailWord_440718) baseStart_440718 baseEnd_440718 := by
    simpa [prefixWord, tailWord_440718, baseEnd_440718] using wordTrace_append hprefix tailTrace_440718
  have hstable : (prefixWord ++ tailWord_440718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440718).length < 2 ^ (prefixWord ++ tailWord_440718).sum := by decide
  have hdescent : baseEnd_440718 < baseStart_440718 := by decide
  rcases family_descends (prefixWord ++ tailWord_440718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440728 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 1, 5, 2]
def baseStart_440728 : Nat := 118140960795 + 440728 * 2 ^ 59
def prefixEnd_440728 : Nat := 4983230072969 + 3 ^ 40 * 440728 * 2
def baseEnd_440728 : Nat := 226305301894856883373135

theorem tailTrace_440728 : CollatzResearch.WordTrace tailWord_440728 prefixEnd_440728 226305301894856883373135 := by
  unfold tailWord_440728
  simp only [CollatzResearch.WordTrace]
  refine ⟨8037335373662600597465419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10716447164883467463287225 8037335373662600597465419)
  ·
    refine ⟨12056003060493900896198129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8037335373662600597465419 12056003060493900896198129)
    ·
      refine ⟨9042002295370425672148597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12056003060493900896198129 9042002295370425672148597)
      ·
        refine ⟨847687715190977406763931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9042002295370425672148597 847687715190977406763931)
        ·
          refine ⟨1271531572786466110145897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847687715190977406763931 1271531572786466110145897)
          ·
            refine ⟨953648679589849582609423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1271531572786466110145897 953648679589849582609423)
            ·
              refine ⟨1430473019384774373914135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953648679589849582609423 1430473019384774373914135)
              ·
                refine ⟨2145709529077161560871203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430473019384774373914135 2145709529077161560871203)
                ·
                  refine ⟨3218564293615742341306805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145709529077161560871203 3218564293615742341306805)
                  ·
                    refine ⟨301740402526475844497513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3218564293615742341306805 301740402526475844497513)
                    ·
                      refine ⟨226305301894856883373135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 301740402526475844497513 226305301894856883373135)
                      ·
                        rfl

theorem cell23_440728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_440728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440728 prefixEnd_440728 := by exact prefixLift 440728
  have htrace : WordTrace (prefixWord ++ tailWord_440728) baseStart_440728 baseEnd_440728 := by
    simpa [prefixWord, tailWord_440728, baseEnd_440728] using wordTrace_append hprefix tailTrace_440728
  have hstable : (prefixWord ++ tailWord_440728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440728).length < 2 ^ (prefixWord ++ tailWord_440728).sum := by decide
  have hdescent : baseEnd_440728 < baseStart_440728 := by decide
  rcases family_descends (prefixWord ++ tailWord_440728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440735 : List Nat := [1, 1, 2, 5, 1, 1, 4, 3, 1, 1, 3]
def baseStart_440735 : Nat := 118140960795 + 440735 * 2 ^ 59
def prefixEnd_440735 : Nat := 4983230072969 + 3 ^ 40 * 440735 * 2
def baseEnd_440735 : Nat := 226308896259438355985603

theorem tailTrace_440735 : CollatzResearch.WordTrace tailWord_440735 prefixEnd_440735 226308896259438355985603 := by
  unfold tailWord_440735
  simp only [CollatzResearch.WordTrace]
  refine ⟨16074926058299841390435659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10716617372199894260290439 16074926058299841390435659)
  ·
    refine ⟨24112389087449762085653489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16074926058299841390435659 24112389087449762085653489)
    ·
      refine ⟨18084291815587321564240117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24112389087449762085653489 18084291815587321564240117)
      ·
        refine ⟨1695402357711311396647511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18084291815587321564240117 1695402357711311396647511)
        ·
          refine ⟨2543103536566967094971267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695402357711311396647511 2543103536566967094971267)
          ·
            refine ⟨3814655304850450642456901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543103536566967094971267 3814655304850450642456901)
            ·
              refine ⟨715247869659459495460669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3814655304850450642456901 715247869659459495460669)
              ·
                refine ⟨268217951122297310797751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 715247869659459495460669 268217951122297310797751)
                ·
                  refine ⟨402326926683445966196627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268217951122297310797751 402326926683445966196627)
                  ·
                    refine ⟨603490390025168949294941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 402326926683445966196627 603490390025168949294941)
                    ·
                      refine ⟨226308896259438355985603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 603490390025168949294941 226308896259438355985603)
                      ·
                        rfl

theorem cell23_440735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_440735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440735 prefixEnd_440735 := by exact prefixLift 440735
  have htrace : WordTrace (prefixWord ++ tailWord_440735) baseStart_440735 baseEnd_440735 := by
    simpa [prefixWord, tailWord_440735, baseEnd_440735] using wordTrace_append hprefix tailTrace_440735
  have hstable : (prefixWord ++ tailWord_440735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440735).length < 2 ^ (prefixWord ++ tailWord_440735).sum := by decide
  have hdescent : baseEnd_440735 < baseStart_440735 := by decide
  rcases family_descends (prefixWord ++ tailWord_440735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440741 : List Nat := [1, 3, 1, 2, 1, 1, 5, 3, 1, 1, 4]
def baseStart_440741 : Nat := 118140960795 + 440741 * 2 ^ 59
def prefixEnd_440741 : Nat := 4983230072969 + 3 ^ 40 * 440741 * 2
def baseEnd_440741 : Nat := 226311977143365332510575

theorem tailTrace_440741 : CollatzResearch.WordTrace tailWord_440741 prefixEnd_440741 226311977143365332510575 := by
  unfold tailWord_440741
  simp only [CollatzResearch.WordTrace]
  refine ⟨16075144896278104415154077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10716763264185402943436051 16075144896278104415154077)
  ·
    refine ⟨6028179336104289155682779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16075144896278104415154077 6028179336104289155682779)
    ·
      refine ⟨9042269004156433733524169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6028179336104289155682779 9042269004156433733524169)
      ·
        refine ⟨6781701753117325300143127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9042269004156433733524169 6781701753117325300143127)
        ·
          refine ⟨10172552629675987950214691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6781701753117325300143127 10172552629675987950214691)
          ·
            refine ⟨15258828944513981925322037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10172552629675987950214691 15258828944513981925322037)
            ·
              refine ⟨1430515213548185805498941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15258828944513981925322037 1430515213548185805498941)
              ·
                refine ⟨536443205080569677062103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1430515213548185805498941 536443205080569677062103)
                ·
                  refine ⟨804664807620854515593155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536443205080569677062103 804664807620854515593155)
                  ·
                    refine ⟨1206997211431281773389733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 804664807620854515593155 1206997211431281773389733)
                    ·
                      refine ⟨226311977143365332510575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1206997211431281773389733 226311977143365332510575)
                      ·
                        rfl

theorem cell23_440741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_440741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440741 prefixEnd_440741 := by exact prefixLift 440741
  have htrace : WordTrace (prefixWord ++ tailWord_440741) baseStart_440741 baseEnd_440741 := by
    simpa [prefixWord, tailWord_440741, baseEnd_440741] using wordTrace_append hprefix tailTrace_440741
  have hstable : (prefixWord ++ tailWord_440741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440741).length < 2 ^ (prefixWord ++ tailWord_440741).sum := by decide
  have hdescent : baseEnd_440741 < baseStart_440741 := by decide
  rcases family_descends (prefixWord ++ tailWord_440741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440754 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_440754 : Nat := 118140960795 + 440754 * 2 ^ 59
def prefixEnd_440754 : Nat := 4983230072969 + 3 ^ 40 * 440754 * 2
def baseEnd_440754 : Nat := 226318652391873781648015

theorem tailTrace_440754 : CollatzResearch.WordTrace tailWord_440754 prefixEnd_440754 226318652391873781648015 := by
  unfold tailWord_440754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4018904761307751908844329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10717079363487338423584877 4018904761307751908844329)
  ·
    refine ⟨3014178570980813931633247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4018904761307751908844329 3014178570980813931633247)
    ·
      refine ⟨4521267856471220897449871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3014178570980813931633247 4521267856471220897449871)
      ·
        refine ⟨6781901784706831346174807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521267856471220897449871 6781901784706831346174807)
        ·
          refine ⟨10172852677060247019262211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6781901784706831346174807 10172852677060247019262211)
          ·
            refine ⟨15259279015590370528893317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10172852677060247019262211 15259279015590370528893317)
            ·
              refine ⟨2861114815423194474167497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15259279015590370528893317 2861114815423194474167497)
              ·
                refine ⟨2145836111567395855625623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2861114815423194474167497 2145836111567395855625623)
                ·
                  refine ⟨3218754167351093783438435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145836111567395855625623 3218754167351093783438435)
                  ·
                    refine ⟨4828131251026640675157653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3218754167351093783438435 4828131251026640675157653)
                    ·
                      refine ⟨226318652391873781648015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4828131251026640675157653 226318652391873781648015)
                      ·
                        rfl

theorem cell23_440754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_440754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440754 prefixEnd_440754 := by exact prefixLift 440754
  have htrace : WordTrace (prefixWord ++ tailWord_440754) baseStart_440754 baseEnd_440754 := by
    simpa [prefixWord, tailWord_440754, baseEnd_440754] using wordTrace_append hprefix tailTrace_440754
  have hstable : (prefixWord ++ tailWord_440754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440754).length < 2 ^ (prefixWord ++ tailWord_440754).sum := by decide
  have hdescent : baseEnd_440754 < baseStart_440754 := by decide
  rcases family_descends (prefixWord ++ tailWord_440754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440761 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 1, 1, 5]
def baseStart_440761 : Nat := 118140960795 + 440761 * 2 ^ 59
def prefixEnd_440761 : Nat := 4983230072969 + 3 ^ 40 * 440761 * 2
def baseEnd_440761 : Nat := 226322246756455254260483

theorem tailTrace_440761 : CollatzResearch.WordTrace tailWord_440761 prefixEnd_440761 226322246756455254260483 := by
  unfold tailWord_440761
  simp only [CollatzResearch.WordTrace]
  refine ⟨16075874356205647830882137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10717249570803765220588091 16075874356205647830882137)
  ·
    refine ⟨12056905767154235873161603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16075874356205647830882137 12056905767154235873161603)
    ·
      refine ⟨18085358650731353809742405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12056905767154235873161603 18085358650731353809742405)
      ·
        refine ⟨3391004747012128839326701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18085358650731353809742405 3391004747012128839326701)
        ·
          refine ⟨1271626780129548314747513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3391004747012128839326701 1271626780129548314747513)
          ·
            refine ⟨953720085097161236060635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1271626780129548314747513 953720085097161236060635)
            ·
              refine ⟨1430580127645741854090953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953720085097161236060635 1430580127645741854090953)
              ·
                refine ⟨1072935095734306390568215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430580127645741854090953 1072935095734306390568215)
                ·
                  refine ⟨1609402643601459585852323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072935095734306390568215 1609402643601459585852323)
                  ·
                    refine ⟨2414103965402189378778485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1609402643601459585852323 2414103965402189378778485)
                    ·
                      refine ⟨226322246756455254260483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2414103965402189378778485 226322246756455254260483)
                      ·
                        rfl

theorem cell23_440761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_440761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440761 prefixEnd_440761 := by exact prefixLift 440761
  have htrace : WordTrace (prefixWord ++ tailWord_440761) baseStart_440761 baseEnd_440761 := by
    simpa [prefixWord, tailWord_440761, baseEnd_440761] using wordTrace_append hprefix tailTrace_440761
  have hstable : (prefixWord ++ tailWord_440761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440761).length < 2 ^ (prefixWord ++ tailWord_440761).sum := by decide
  have hdescent : baseEnd_440761 < baseStart_440761 := by decide
  rcases family_descends (prefixWord ++ tailWord_440761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440778 : List Nat := [3, 1, 2, 1, 2, 2, 4, 2, 1, 2, 3]
def baseStart_440778 : Nat := 118140960795 + 440778 * 2 ^ 59
def prefixEnd_440778 : Nat := 4983230072969 + 3 ^ 40 * 440778 * 2
def baseEnd_440778 : Nat := 226330975927581687747905

theorem tailTrace_440778 : CollatzResearch.WordTrace tailWord_440778 prefixEnd_440778 226330975927581687747905 := by
  unfold tailWord_440778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019123599286014933562747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10717662931429373156167325 4019123599286014933562747)
  ·
    refine ⟨6028685398929022400344121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4019123599286014933562747 6028685398929022400344121)
    ·
      refine ⟨4521514049196766800258091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6028685398929022400344121 4521514049196766800258091)
      ·
        refine ⟨6782271073795150200387137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521514049196766800258091 6782271073795150200387137)
        ·
          refine ⟨5086703305346362650290353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6782271073795150200387137 5086703305346362650290353)
          ·
            refine ⟨3815027479009771987717765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5086703305346362650290353 3815027479009771987717765)
            ·
              refine ⟨715317652314332247697081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3815027479009771987717765 715317652314332247697081)
              ·
                refine ⟨536488239235749185772811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 715317652314332247697081 536488239235749185772811)
                ·
                  refine ⟨804732358853623778659217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536488239235749185772811 804732358853623778659217)
                  ·
                    refine ⟨603549269140217833994413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 804732358853623778659217 603549269140217833994413)
                    ·
                      refine ⟨226330975927581687747905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 603549269140217833994413 226330975927581687747905)
                      ·
                        rfl

theorem cell23_440778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_440778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440778 prefixEnd_440778 := by exact prefixLift 440778
  have htrace : WordTrace (prefixWord ++ tailWord_440778) baseStart_440778 baseEnd_440778 := by
    simpa [prefixWord, tailWord_440778, baseEnd_440778] using wordTrace_append hprefix tailTrace_440778
  have hstable : (prefixWord ++ tailWord_440778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440778).length < 2 ^ (prefixWord ++ tailWord_440778).sum := by decide
  have hdescent : baseEnd_440778 < baseStart_440778 := by decide
  rcases family_descends (prefixWord ++ tailWord_440778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440786 : List Nat := [3, 2, 2, 4, 2, 1, 1, 3, 1, 1, 3]
def baseStart_440786 : Nat := 118140960795 + 440786 * 2 ^ 59
def prefixEnd_440786 : Nat := 4983230072969 + 3 ^ 40 * 440786 * 2
def baseEnd_440786 : Nat := 226335083772817656447869

theorem tailTrace_440786 : CollatzResearch.WordTrace tailWord_440786 prefixEnd_440786 226335083772817656447869 := by
  unfold tailWord_440786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019196545278769275135553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10717857454076718067028141 4019196545278769275135553)
  ·
    refine ⟨3014397408959076956351665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4019196545278769275135553 3014397408959076956351665)
    ·
      refine ⟨2260798056719307717263749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3014397408959076956351665 2260798056719307717263749)
      ·
        refine ⟨423899635634870196986953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2260798056719307717263749 423899635634870196986953)
        ·
          refine ⟨317924726726152647740215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423899635634870196986953 317924726726152647740215)
          ·
            refine ⟨476887090089228971610323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317924726726152647740215 476887090089228971610323)
            ·
              refine ⟨715330635133843457415485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476887090089228971610323 715330635133843457415485)
              ·
                refine ⟨268248988175191296530807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 715330635133843457415485 268248988175191296530807)
                ·
                  refine ⟨402373482262786944796211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268248988175191296530807 402373482262786944796211)
                  ·
                    refine ⟨603560223394180417194317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 402373482262786944796211 603560223394180417194317)
                    ·
                      refine ⟨226335083772817656447869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 603560223394180417194317 226335083772817656447869)
                      ·
                        rfl

theorem cell23_440786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_440786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440786 prefixEnd_440786 := by exact prefixLift 440786
  have htrace : WordTrace (prefixWord ++ tailWord_440786) baseStart_440786 baseEnd_440786 := by
    simpa [prefixWord, tailWord_440786, baseEnd_440786] using wordTrace_append hprefix tailTrace_440786
  have hstable : (prefixWord ++ tailWord_440786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440786).length < 2 ^ (prefixWord ++ tailWord_440786).sum := by decide
  have hdescent : baseEnd_440786 < baseStart_440786 := by decide
  rcases family_descends (prefixWord ++ tailWord_440786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440808 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_440808 : Nat := 118140960795 + 440808 * 2 ^ 59
def prefixEnd_440808 : Nat := 4983230072969 + 3 ^ 40 * 440808 * 2
def baseEnd_440808 : Nat := 226346380347216570372767

theorem tailTrace_440808 : CollatzResearch.WordTrace tailWord_440808 prefixEnd_440808 226346380347216570372767 := by
  unfold tailWord_440808
  simp only [CollatzResearch.WordTrace]
  refine ⟨8038794293517687428921539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10718392391356916571895385 8038794293517687428921539)
  ·
    refine ⟨12058191440276531143382309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8038794293517687428921539 12058191440276531143382309)
    ·
      refine ⟨2260910895051849589384183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12058191440276531143382309 2260910895051849589384183)
      ·
        refine ⟨3391366342577774384076275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2260910895051849589384183 3391366342577774384076275)
        ·
          refine ⟨5087049513866661576114413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3391366342577774384076275 5087049513866661576114413)
          ·
            refine ⟨1907643567699998091042905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5087049513866661576114413 1907643567699998091042905)
            ·
              refine ⟨1430732675774998568282179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1907643567699998091042905 1430732675774998568282179)
              ·
                refine ⟨2146099013662497852423269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430732675774998568282179 2146099013662497852423269)
                ·
                  refine ⟨402393565061718347329363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2146099013662497852423269 402393565061718347329363)
                  ·
                    refine ⟨603590347592577520994045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 402393565061718347329363 603590347592577520994045)
                    ·
                      refine ⟨226346380347216570372767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 603590347592577520994045 226346380347216570372767)
                      ·
                        rfl

theorem cell23_440808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_440808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440808 prefixEnd_440808 := by exact prefixLift 440808
  have htrace : WordTrace (prefixWord ++ tailWord_440808) baseStart_440808 baseEnd_440808 := by
    simpa [prefixWord, tailWord_440808, baseEnd_440808] using wordTrace_append hprefix tailTrace_440808
  have hstable : (prefixWord ++ tailWord_440808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440808).length < 2 ^ (prefixWord ++ tailWord_440808).sum := by decide
  have hdescent : baseEnd_440808 < baseStart_440808 := by decide
  rcases family_descends (prefixWord ++ tailWord_440808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440824 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 1, 8]
def baseStart_440824 : Nat := 118140960795 + 440824 * 2 ^ 59
def prefixEnd_440824 : Nat := 4983230072969 + 3 ^ 40 * 440824 * 2
def baseEnd_440824 : Nat := 75451532012562835924231

theorem tailTrace_440824 : CollatzResearch.WordTrace tailWord_440824 prefixEnd_440824 75451532012562835924231 := by
  unfold tailWord_440824
  simp only [CollatzResearch.WordTrace]
  refine ⟨8039086077488704795212763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10718781436651606393617017 8039086077488704795212763)
  ·
    refine ⟨12058629116233057192819145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8039086077488704795212763 12058629116233057192819145)
    ·
      refine ⟨9043971837174792894614359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12058629116233057192819145 9043971837174792894614359)
      ·
        refine ⟨13565957755762189341921539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9043971837174792894614359 13565957755762189341921539)
        ·
          refine ⟨20348936633643284012882309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13565957755762189341921539 20348936633643284012882309)
          ·
            refine ⟨3815425618808115752415433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20348936633643284012882309 3815425618808115752415433)
            ·
              refine ⟨2861569214106086814311575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3815425618808115752415433 2861569214106086814311575)
              ·
                refine ⟨4292353821159130221467363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2861569214106086814311575 4292353821159130221467363)
                ·
                  refine ⟨6438530731738695332201045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292353821159130221467363 6438530731738695332201045)
                  ·
                    refine ⟨75451532012562835924231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6438530731738695332201045 75451532012562835924231)
                    ·
                      rfl

theorem cell23_440824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_440824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440824 prefixEnd_440824 := by exact prefixLift 440824
  have htrace : WordTrace (prefixWord ++ tailWord_440824) baseStart_440824 baseEnd_440824 := by
    simpa [prefixWord, tailWord_440824, baseEnd_440824] using wordTrace_append hprefix tailTrace_440824
  have hstable : (prefixWord ++ tailWord_440824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440824).length < 2 ^ (prefixWord ++ tailWord_440824).sum := by decide
  have hdescent : baseEnd_440824 < baseStart_440824 := by decide
  rcases family_descends (prefixWord ++ tailWord_440824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440825 : List Nat := [1, 2, 1, 3, 1, 2, 6, 1, 2, 1, 3]
def baseStart_440825 : Nat := 118140960795 + 440825 * 2 ^ 59
def prefixEnd_440825 : Nat := 4983230072969 + 3 ^ 40 * 440825 * 2
def baseEnd_440825 : Nat := 226355109518343003860189

theorem tailTrace_440825 : CollatzResearch.WordTrace tailWord_440825 prefixEnd_440825 226355109518343003860189 := by
  unfold tailWord_440825
  simp only [CollatzResearch.WordTrace]
  refine ⟨16078208627973786761211929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10718805751982524507474619 16078208627973786761211929)
  ·
    refine ⟨12058656470980340070908947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16078208627973786761211929 12058656470980340070908947)
    ·
      refine ⟨18087984706470510106363421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12058656470980340070908947 18087984706470510106363421)
      ·
        refine ⟨6782994264926441289886283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18087984706470510106363421 6782994264926441289886283)
        ·
          refine ⟨10174491397389661934829425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6782994264926441289886283 10174491397389661934829425)
          ·
            refine ⟨7630868548042246451122069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10174491397389661934829425 7630868548042246451122069)
            ·
              refine ⟨357696963189480302396347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7630868548042246451122069 357696963189480302396347)
              ·
                refine ⟨536545444784220453594521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357696963189480302396347 536545444784220453594521)
                ·
                  refine ⟨402409083588165340195891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536545444784220453594521 402409083588165340195891)
                  ·
                    refine ⟨603613625382248010293837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 402409083588165340195891 603613625382248010293837)
                    ·
                      refine ⟨226355109518343003860189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 603613625382248010293837 226355109518343003860189)
                      ·
                        rfl

theorem cell23_440825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_440825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440825 prefixEnd_440825 := by exact prefixLift 440825
  have htrace : WordTrace (prefixWord ++ tailWord_440825) baseStart_440825 baseEnd_440825 := by
    simpa [prefixWord, tailWord_440825, baseEnd_440825] using wordTrace_append hprefix tailTrace_440825
  have hstable : (prefixWord ++ tailWord_440825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440825).length < 2 ^ (prefixWord ++ tailWord_440825).sum := by decide
  have hdescent : baseEnd_440825 < baseStart_440825 := by decide
  rcases family_descends (prefixWord ++ tailWord_440825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440881 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 1, 5, 3]
def baseStart_440881 : Nat := 118140960795 + 440881 * 2 ^ 59
def prefixEnd_440881 : Nat := 4983230072969 + 3 ^ 40 * 440881 * 2
def baseEnd_440881 : Nat := 226383864434994784759931

theorem tailTrace_440881 : CollatzResearch.WordTrace tailWord_440881 prefixEnd_440881 226383864434994784759931 := by
  unfold tailWord_440881
  simp only [CollatzResearch.WordTrace]
  refine ⟨16080251115770908325250497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10720167410513938883500331 16080251115770908325250497)
  ·
    refine ⟨12060188336828181243937873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16080251115770908325250497 12060188336828181243937873)
    ·
      refine ⟨9045141252621135932953405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12060188336828181243937873 9045141252621135932953405)
      ·
        refine ⟨3391927969732925974857527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9045141252621135932953405 3391927969732925974857527)
        ·
          refine ⟨5087891954599388962286291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3391927969732925974857527 5087891954599388962286291)
          ·
            refine ⟨7631837931899083443429437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5087891954599388962286291 7631837931899083443429437)
            ·
              refine ⟨2861939224462156291286039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7631837931899083443429437 2861939224462156291286039)
              ·
                refine ⟨4292908836693234436929059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2861939224462156291286039 4292908836693234436929059)
                ·
                  refine ⟨6439363255039851655393589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292908836693234436929059 6439363255039851655393589)
                  ·
                    refine ⟨603690305159986092693149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6439363255039851655393589 603690305159986092693149)
                    ·
                      refine ⟨226383864434994784759931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 603690305159986092693149 226383864434994784759931)
                      ·
                        rfl

theorem cell23_440881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_440881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440881 prefixEnd_440881 := by exact prefixLift 440881
  have htrace : WordTrace (prefixWord ++ tailWord_440881) baseStart_440881 baseEnd_440881 := by
    simpa [prefixWord, tailWord_440881, baseEnd_440881] using wordTrace_append hprefix tailTrace_440881
  have hstable : (prefixWord ++ tailWord_440881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440881).length < 2 ^ (prefixWord ++ tailWord_440881).sum := by decide
  have hdescent : baseEnd_440881 < baseStart_440881 := by decide
  rcases family_descends (prefixWord ++ tailWord_440881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440901 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 1, 7]
def baseStart_440901 : Nat := 118140960795 + 440901 * 2 ^ 59
def prefixEnd_440901 : Nat := 4983230072969 + 3 ^ 40 * 440901 * 2
def baseEnd_440901 : Nat := 75464711349361568836613

theorem tailTrace_440901 : CollatzResearch.WordTrace tailWord_440901 prefixEnd_440901 75464711349361568836613 := by
  unfold tailWord_440901
  simp only [CollatzResearch.WordTrace]
  refine ⟨16080980575698451740978557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10720653717132301160652371 16080980575698451740978557)
  ·
    refine ⟨6030367715886919402866959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16080980575698451740978557 6030367715886919402866959)
    ·
      refine ⟨9045551573830379104300439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6030367715886919402866959 9045551573830379104300439)
      ·
        refine ⟨13568327360745568656450659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9045551573830379104300439 13568327360745568656450659)
        ·
          refine ⟨20352491041118352984675989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13568327360745568656450659 20352491041118352984675989)
          ·
            refine ⟨954023017552422796156687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20352491041118352984675989 954023017552422796156687)
            ·
              refine ⟨1431034526328634194235031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954023017552422796156687 1431034526328634194235031)
              ·
                refine ⟨2146551789492951291352547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431034526328634194235031 2146551789492951291352547)
                ·
                  refine ⟨3219827684239426937028821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146551789492951291352547 3219827684239426937028821)
                  ·
                    refine ⟨75464711349361568836613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3219827684239426937028821 75464711349361568836613)
                    ·
                      rfl

theorem cell23_440901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_440901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440901 prefixEnd_440901 := by exact prefixLift 440901
  have htrace : WordTrace (prefixWord ++ tailWord_440901) baseStart_440901 baseEnd_440901 := by
    simpa [prefixWord, tailWord_440901, baseEnd_440901] using wordTrace_append hprefix tailTrace_440901
  have hstable : (prefixWord ++ tailWord_440901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440901).length < 2 ^ (prefixWord ++ tailWord_440901).sum := by decide
  have hdescent : baseEnd_440901 < baseStart_440901 := by decide
  rcases family_descends (prefixWord ++ tailWord_440901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440961 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 10]
def baseStart_440961 : Nat := 118140960795 + 440961 * 2 ^ 59
def prefixEnd_440961 : Nat := 4983230072969 + 3 ^ 40 * 440961 * 2
def baseEnd_440961 : Nat := 25158326987483830195507

theorem tailTrace_440961 : CollatzResearch.WordTrace tailWord_440961 prefixEnd_440961 25158326987483830195507 := by
  unfold tailWord_440961
  simp only [CollatzResearch.WordTrace]
  refine ⟨16083168955481081988162737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10722112636987387992108491 16083168955481081988162737)
  ·
    refine ⟨12062376716610811491122053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16083168955481081988162737 12062376716610811491122053)
    ·
      refine ⟨2261695634364527154585385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12062376716610811491122053 2261695634364527154585385)
      ·
        refine ⟨1696271725773395365939039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2261695634364527154585385 1696271725773395365939039)
        ·
          refine ⟨2544407588660093048908559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1696271725773395365939039 2544407588660093048908559)
          ·
            refine ⟨3816611382990139573362839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2544407588660093048908559 3816611382990139573362839)
            ·
              refine ⟨5724917074485209360044259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3816611382990139573362839 5724917074485209360044259)
              ·
                refine ⟨8587375611727814040066389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5724917074485209360044259 8587375611727814040066389)
                ·
                  refine ⟨25158326987483830195507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 8587375611727814040066389 25158326987483830195507)
                  ·
                    rfl

theorem cell23_440961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 10].length) (baseStart_440961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440961 prefixEnd_440961 := by exact prefixLift 440961
  have htrace : WordTrace (prefixWord ++ tailWord_440961) baseStart_440961 baseEnd_440961 := by
    simpa [prefixWord, tailWord_440961, baseEnd_440961] using wordTrace_append hprefix tailTrace_440961
  have hstable : (prefixWord ++ tailWord_440961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440961).length < 2 ^ (prefixWord ++ tailWord_440961).sum := by decide
  have hdescent : baseEnd_440961 < baseStart_440961 := by decide
  rcases family_descends (prefixWord ++ tailWord_440961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440978 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 8]
def baseStart_440978 : Nat := 118140960795 + 440978 * 2 ^ 59
def prefixEnd_440978 : Nat := 4983230072969 + 3 ^ 40 * 440978 * 2
def baseEnd_440978 : Nat := 25159296895386767249665

theorem tailTrace_440978 : CollatzResearch.WordTrace tailWord_440978 prefixEnd_440978 25159296895386767249665 := by
  unfold tailWord_440978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4020947249104873472882897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10722525997612995927687725 4020947249104873472882897)
  ·
    refine ⟨3015710436828655104662173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4020947249104873472882897 3015710436828655104662173)
    ·
      refine ⟨1130891413810745664248315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3015710436828655104662173 1130891413810745664248315)
      ·
        refine ⟨1696337120716118496372473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1130891413810745664248315 1696337120716118496372473)
        ·
          refine ⟨1272252840537088872279355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1696337120716118496372473 1272252840537088872279355)
          ·
            refine ⟨1908379260805633308419033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272252840537088872279355 1908379260805633308419033)
            ·
              refine ⟨1431284445604224981314275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1908379260805633308419033 1431284445604224981314275)
              ·
                refine ⟨2146926668406337471971413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431284445604224981314275 2146926668406337471971413)
                ·
                  refine ⟨25159296895386767249665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2146926668406337471971413 25159296895386767249665)
                  ·
                    rfl

theorem cell23_440978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_440978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_440978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_440978 prefixEnd_440978 := by exact prefixLift 440978
  have htrace : WordTrace (prefixWord ++ tailWord_440978) baseStart_440978 baseEnd_440978 := by
    simpa [prefixWord, tailWord_440978, baseEnd_440978] using wordTrace_append hprefix tailTrace_440978
  have hstable : (prefixWord ++ tailWord_440978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440978).length < 2 ^ (prefixWord ++ tailWord_440978).sum := by decide
  have hdescent : baseEnd_440978 < baseStart_440978 := by decide
  rcases family_descends (prefixWord ++ tailWord_440978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441055 : List Nat := [1, 1, 2, 3, 2, 3, 2, 3, 2, 4]
def baseStart_441055 : Nat := 118140960795 + 441055 * 2 ^ 59
def prefixEnd_441055 : Nat := 4983230072969 + 3 ^ 40 * 441055 * 2
def baseEnd_441055 : Nat := 75491070022959034661377

theorem tailTrace_441055 : CollatzResearch.WordTrace tailWord_441055 prefixEnd_441055 75491070022959034661377 := by
  unfold tailWord_441055
  simp only [CollatzResearch.WordTrace]
  refine ⟨16086597417140536042084619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10724398278093690694723079 16086597417140536042084619)
  ·
    refine ⟨24129896125710804063126929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16086597417140536042084619 24129896125710804063126929)
    ·
      refine ⟨18097422094283103047345197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24129896125710804063126929 18097422094283103047345197)
      ·
        refine ⟨6786533285356163642754449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18097422094283103047345197 6786533285356163642754449)
        ·
          refine ⟨5089899964017122732065837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6786533285356163642754449 5089899964017122732065837)
          ·
            refine ⟨1908712486506421024524689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5089899964017122732065837 1908712486506421024524689)
            ·
              refine ⟨1431534364879815768393517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1908712486506421024524689 1431534364879815768393517)
              ·
                refine ⟨536825386829930913147569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1431534364879815768393517 536825386829930913147569)
                ·
                  refine ⟨402619040122448184860677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536825386829930913147569 402619040122448184860677)
                  ·
                    refine ⟨75491070022959034661377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 402619040122448184860677 75491070022959034661377)
                    ·
                      rfl

theorem cell23_441055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 4].length) (baseStart_441055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441055 prefixEnd_441055 := by exact prefixLift 441055
  have htrace : WordTrace (prefixWord ++ tailWord_441055) baseStart_441055 baseEnd_441055 := by
    simpa [prefixWord, tailWord_441055, baseEnd_441055] using wordTrace_append hprefix tailTrace_441055
  have hstable : (prefixWord ++ tailWord_441055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441055).length < 2 ^ (prefixWord ++ tailWord_441055).sum := by decide
  have hdescent : baseEnd_441055 < baseStart_441055 := by decide
  rcases family_descends (prefixWord ++ tailWord_441055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441082 : List Nat := [3, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3]
def baseStart_441082 : Nat := 118140960795 + 441082 * 2 ^ 59
def prefixEnd_441082 : Nat := 4983230072969 + 3 ^ 40 * 441082 * 2
def baseEnd_441082 : Nat := 226487074046548498346507

theorem tailTrace_441082 : CollatzResearch.WordTrace tailWord_441082 prefixEnd_441082 226487074046548498346507 := by
  unfold tailWord_441082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4021895547010679913329375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10725054792028479768878333 4021895547010679913329375)
  ·
    refine ⟨6032843320516019869994063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4021895547010679913329375 6032843320516019869994063)
    ·
      refine ⟨9049264980774029804991095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6032843320516019869994063 9049264980774029804991095)
      ·
        refine ⟨13573897471161044707486643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9049264980774029804991095 13573897471161044707486643)
        ·
          refine ⟨20360846206741567061229965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13573897471161044707486643 20360846206741567061229965)
          ·
            refine ⟨7635317327528087647961237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20360846206741567061229965 7635317327528087647961237)
            ·
              refine ⟨357905499727879108498183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7635317327528087647961237 357905499727879108498183)
              ·
                refine ⟨536858249591818662747275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357905499727879108498183 536858249591818662747275)
                ·
                  refine ⟨805287374387727994120913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536858249591818662747275 805287374387727994120913)
                  ·
                    refine ⟨603965530790795995590685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 805287374387727994120913 603965530790795995590685)
                    ·
                      refine ⟨226487074046548498346507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 603965530790795995590685 226487074046548498346507)
                      ·
                        rfl

theorem cell23_441082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3].length) (baseStart_441082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441082 prefixEnd_441082 := by exact prefixLift 441082
  have htrace : WordTrace (prefixWord ++ tailWord_441082) baseStart_441082 baseEnd_441082 := by
    simpa [prefixWord, tailWord_441082, baseEnd_441082] using wordTrace_append hprefix tailTrace_441082
  have hstable : (prefixWord ++ tailWord_441082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441082).length < 2 ^ (prefixWord ++ tailWord_441082).sum := by decide
  have hdescent : baseEnd_441082 < baseStart_441082 := by decide
  rcases family_descends (prefixWord ++ tailWord_441082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441105 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 5, 3, 2]
def baseStart_441105 : Nat := 118140960795 + 441105 * 2 ^ 59
def prefixEnd_441105 : Nat := 4983230072969 + 3 ^ 40 * 441105 * 2
def baseEnd_441105 : Nat := 226498884101601908358901

theorem tailTrace_441105 : CollatzResearch.WordTrace tailWord_441105 prefixEnd_441105 226498884101601908358901 := by
  unfold tailWord_441105
  simp only [CollatzResearch.WordTrace]
  refine ⟨16088421066959394581404769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10725614044639596387603179 16088421066959394581404769)
  ·
    refine ⟨12066315800219545936053577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16088421066959394581404769 12066315800219545936053577)
    ·
      refine ⟨9049736850164659452040183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12066315800219545936053577 9049736850164659452040183)
      ·
        refine ⟨13574605275246989178060275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9049736850164659452040183 13574605275246989178060275)
        ·
          refine ⟨20361907912870483767090413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13574605275246989178060275 20361907912870483767090413)
          ·
            refine ⟨7635715467326431412658905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20361907912870483767090413 7635715467326431412658905)
            ·
              refine ⟨5726786600494823559494179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7635715467326431412658905 5726786600494823559494179)
              ·
                refine ⟨8590179900742235339241269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726786600494823559494179 8590179900742235339241269)
                ·
                  refine ⟨805329365694584563053869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8590179900742235339241269 805329365694584563053869)
                  ·
                    refine ⟨301998512135469211145201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 805329365694584563053869 301998512135469211145201)
                    ·
                      refine ⟨226498884101601908358901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 301998512135469211145201 226498884101601908358901)
                      ·
                        rfl

theorem cell23_441105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 3, 2].length) (baseStart_441105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441105 prefixEnd_441105 := by exact prefixLift 441105
  have htrace : WordTrace (prefixWord ++ tailWord_441105) baseStart_441105 baseEnd_441105 := by
    simpa [prefixWord, tailWord_441105, baseEnd_441105] using wordTrace_append hprefix tailTrace_441105
  have hstable : (prefixWord ++ tailWord_441105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441105).length < 2 ^ (prefixWord ++ tailWord_441105).sum := by decide
  have hdescent : baseEnd_441105 < baseStart_441105 := by decide
  rcases family_descends (prefixWord ++ tailWord_441105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441106 : List Nat := [3, 2, 4, 1, 2, 1, 3, 1, 2, 4]
def baseStart_441106 : Nat := 118140960795 + 441106 * 2 ^ 59
def prefixEnd_441106 : Nat := 4983230072969 + 3 ^ 40 * 441106 * 2
def baseEnd_441106 : Nat := 75499799194085468148799

theorem tailTrace_441106 : CollatzResearch.WordTrace tailWord_441106 prefixEnd_441106 75499799194085468148799 := by
  unfold tailWord_441106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4022114384988942938047793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10725638359970514501460781 4022114384988942938047793)
  ·
    refine ⟨3016585788741707203535845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4022114384988942938047793 3016585788741707203535845)
    ·
      refine ⟨565609835389070100662971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3016585788741707203535845 565609835389070100662971)
      ·
        refine ⟨848414753083605150994457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565609835389070100662971 848414753083605150994457)
        ·
          refine ⟨636311064812703863245843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848414753083605150994457 636311064812703863245843)
          ·
            refine ⟨954466597219055794868765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636311064812703863245843 954466597219055794868765)
            ·
              refine ⟨357924973957145923075787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 954466597219055794868765 357924973957145923075787)
              ·
                refine ⟨536887460935718884613681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357924973957145923075787 536887460935718884613681)
                ·
                  refine ⟨402665595701789163460261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536887460935718884613681 402665595701789163460261)
                  ·
                    refine ⟨75499799194085468148799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 402665595701789163460261 75499799194085468148799)
                    ·
                      rfl

theorem cell23_441106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_441106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441106 prefixEnd_441106 := by exact prefixLift 441106
  have htrace : WordTrace (prefixWord ++ tailWord_441106) baseStart_441106 baseEnd_441106 := by
    simpa [prefixWord, tailWord_441106, baseEnd_441106] using wordTrace_append hprefix tailTrace_441106
  have hstable : (prefixWord ++ tailWord_441106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441106).length < 2 ^ (prefixWord ++ tailWord_441106).sum := by decide
  have hdescent : baseEnd_441106 < baseStart_441106 := by decide
  rcases family_descends (prefixWord ++ tailWord_441106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441130 : List Nat := [3, 1, 4, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_441130 : Nat := 118140960795 + 441130 * 2 ^ 59
def prefixEnd_441130 : Nat := 4983230072969 + 3 ^ 40 * 441130 * 2
def baseEnd_441130 : Nat := 226511721117964310546287

theorem tailTrace_441130 : CollatzResearch.WordTrace tailWord_441130 prefixEnd_441130 226511721117964310546287 := by
  unfold tailWord_441130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4022333222967205962766211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10726221927912549234043229 4022333222967205962766211)
  ·
    refine ⟨6033499834450808944149317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4022333222967205962766211 6033499834450808944149317)
    ·
      refine ⟨1131281218959526677027997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6033499834450808944149317 1131281218959526677027997)
      ·
        refine ⟨424230457109822503885499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1131281218959526677027997 424230457109822503885499)
        ·
          refine ⟨636345685664733755828249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424230457109822503885499 636345685664733755828249)
          ·
            refine ⟨477259264248550316871187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636345685664733755828249 477259264248550316871187)
            ·
              refine ⟨715888896372825475306781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477259264248550316871187 715888896372825475306781)
              ·
                refine ⟨268458336139809553240043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 715888896372825475306781 268458336139809553240043)
                ·
                  refine ⟨402687504209714329860065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268458336139809553240043 402687504209714329860065)
                  ·
                    refine ⟨302015628157285747395049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 402687504209714329860065 302015628157285747395049)
                    ·
                      refine ⟨226511721117964310546287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 302015628157285747395049 226511721117964310546287)
                      ·
                        rfl

theorem cell23_441130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_441130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441130 prefixEnd_441130 := by exact prefixLift 441130
  have htrace : WordTrace (prefixWord ++ tailWord_441130) baseStart_441130 baseEnd_441130 := by
    simpa [prefixWord, tailWord_441130, baseEnd_441130] using wordTrace_append hprefix tailTrace_441130
  have hstable : (prefixWord ++ tailWord_441130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441130).length < 2 ^ (prefixWord ++ tailWord_441130).sum := by decide
  have hdescent : baseEnd_441130 < baseStart_441130 := by decide
  rcases family_descends (prefixWord ++ tailWord_441130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441209 : List Nat := [1, 2, 1, 3, 2, 5, 2, 2, 5]
def baseStart_441209 : Nat := 118140960795 + 441209 * 2 ^ 59
def prefixEnd_441209 : Nat := 4983230072969 + 3 ^ 40 * 441209 * 2
def baseEnd_441209 : Nat := 25172476232185500162047

theorem tailTrace_441209 : CollatzResearch.WordTrace tailWord_441209 prefixEnd_441209 25172476232185500162047 := by
  unfold tailWord_441209
  simp only [CollatzResearch.WordTrace]
  refine ⟨16092214258582620343190681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10728142839055080228793787 16092214258582620343190681)
  ·
    refine ⟨12069160693936965257393011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16092214258582620343190681 12069160693936965257393011)
    ·
      refine ⟨18103741040905447886089517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12069160693936965257393011 18103741040905447886089517)
      ·
        refine ⟨6788902890339542957283569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18103741040905447886089517 6788902890339542957283569)
        ·
          refine ⟨5091677167754657217962677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6788902890339542957283569 5091677167754657217962677)
          ·
            refine ⟨477344734476999114184001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5091677167754657217962677 477344734476999114184001)
            ·
              refine ⟨358008550857749335638001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477344734476999114184001 358008550857749335638001)
              ·
                refine ⟨268506413143312001728501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358008550857749335638001 268506413143312001728501)
                ·
                  refine ⟨25172476232185500162047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 268506413143312001728501 25172476232185500162047)
                  ·
                    rfl

theorem cell23_441209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 5].length) (baseStart_441209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441209 prefixEnd_441209 := by exact prefixLift 441209
  have htrace : WordTrace (prefixWord ++ tailWord_441209) baseStart_441209 baseEnd_441209 := by
    simpa [prefixWord, tailWord_441209, baseEnd_441209] using wordTrace_append hprefix tailTrace_441209
  have hstable : (prefixWord ++ tailWord_441209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441209).length < 2 ^ (prefixWord ++ tailWord_441209).sum := by decide
  have hdescent : baseEnd_441209 < baseStart_441209 := by decide
  rcases family_descends (prefixWord ++ tailWord_441209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441242 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4]
def baseStart_441242 : Nat := 118140960795 + 441242 * 2 ^ 59
def prefixEnd_441242 : Nat := 4983230072969 + 3 ^ 40 * 441242 * 2
def baseEnd_441242 : Nat := 226569230951267872345771

theorem tailTrace_441242 : CollatzResearch.WordTrace tailWord_441242 prefixEnd_441242 226569230951267872345771 := by
  unfold tailWord_441242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4023354466865766744785495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10728945244975377986094653 4023354466865766744785495)
  ·
    refine ⟨6035031700298650117178243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4023354466865766744785495 6035031700298650117178243)
    ·
      refine ⟨9052547550447975175767365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6035031700298650117178243 9052547550447975175767365)
      ·
        refine ⟨1697352665708995345456381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9052547550447975175767365 1697352665708995345456381)
        ·
          refine ⟨636507249640873254546143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1697352665708995345456381 636507249640873254546143)
          ·
            refine ⟨954760874461309881819215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636507249640873254546143 954760874461309881819215)
            ·
              refine ⟨1432141311691964822728823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954760874461309881819215 1432141311691964822728823)
              ·
                refine ⟨2148211967537947234093235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432141311691964822728823 2148211967537947234093235)
                ·
                  refine ⟨3222317951306920851139853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148211967537947234093235 3222317951306920851139853)
                  ·
                    refine ⟨1208369231740095319177445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3222317951306920851139853 1208369231740095319177445)
                    ·
                      refine ⟨226569230951267872345771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1208369231740095319177445 226569230951267872345771)
                      ·
                        rfl

theorem cell23_441242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_441242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441242 prefixEnd_441242 := by exact prefixLift 441242
  have htrace : WordTrace (prefixWord ++ tailWord_441242) baseStart_441242 baseEnd_441242 := by
    simpa [prefixWord, tailWord_441242, baseEnd_441242] using wordTrace_append hprefix tailTrace_441242
  have hstable : (prefixWord ++ tailWord_441242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441242).length < 2 ^ (prefixWord ++ tailWord_441242).sum := by decide
  have hdescent : baseEnd_441242 < baseStart_441242 := by decide
  rcases family_descends (prefixWord ++ tailWord_441242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441269 : List Nat := [1, 3, 3, 2, 1, 1, 1, 6, 1, 4]
def baseStart_441269 : Nat := 118140960795 + 441269 * 2 ^ 59
def prefixEnd_441269 : Nat := 4983230072969 + 3 ^ 40 * 441269 * 2
def baseEnd_441269 : Nat := 75527698309646422236049

theorem tailTrace_441269 : CollatzResearch.WordTrace tailWord_441269 prefixEnd_441269 75527698309646422236049 := by
  unfold tailWord_441269
  simp only [CollatzResearch.WordTrace]
  refine ⟨16094402638365250590374861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10729601758910167060249907 16094402638365250590374861)
  ·
    refine ⟨6035400989386968971390573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16094402638365250590374861 6035400989386968971390573)
    ·
      refine ⟨2263275371020113364271465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6035400989386968971390573 2263275371020113364271465)
      ·
        refine ⟨1697456528265085023203599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2263275371020113364271465 1697456528265085023203599)
        ·
          refine ⟨2546184792397627534805399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1697456528265085023203599 2546184792397627534805399)
          ·
            refine ⟨3819277188596441302208099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546184792397627534805399 3819277188596441302208099)
            ·
              refine ⟨5728915782894661953312149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819277188596441302208099 5728915782894661953312149)
              ·
                refine ⟨268542927323187279061507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5728915782894661953312149 268542927323187279061507)
                ·
                  refine ⟨402814390984780918592261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268542927323187279061507 402814390984780918592261)
                  ·
                    refine ⟨75527698309646422236049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 402814390984780918592261 75527698309646422236049)
                    ·
                      rfl

theorem cell23_441269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_441269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441269 prefixEnd_441269 := by exact prefixLift 441269
  have htrace : WordTrace (prefixWord ++ tailWord_441269) baseStart_441269 baseEnd_441269 := by
    simpa [prefixWord, tailWord_441269, baseEnd_441269] using wordTrace_append hprefix tailTrace_441269
  have hstable : (prefixWord ++ tailWord_441269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441269).length < 2 ^ (prefixWord ++ tailWord_441269).sum := by decide
  have hdescent : baseEnd_441269 < baseStart_441269 := by decide
  rcases family_descends (prefixWord ++ tailWord_441269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441319 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_441319 : Nat := 118140960795 + 441319 * 2 ^ 59
def prefixEnd_441319 : Nat := 4983230072969 + 3 ^ 40 * 441319 * 2
def baseEnd_441319 : Nat := 226608768961664071082917

theorem tailTrace_441319 : CollatzResearch.WordTrace tailWord_441319 prefixEnd_441319 226608768961664071082917 := by
  unfold tailWord_441319
  simp only [CollatzResearch.WordTrace]
  refine ⟨16096226288184109129695011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10730817525456072753130007 16096226288184109129695011)
  ·
    refine ⟨24144339432276163694542517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16096226288184109129695011 24144339432276163694542517)
    ·
      refine ⟨2263531821775890346363361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24144339432276163694542517 2263531821775890346363361)
      ·
        refine ⟨1697648866331917759772521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2263531821775890346363361 1697648866331917759772521)
        ·
          refine ⟨1273236649748938319829391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1697648866331917759772521 1273236649748938319829391)
          ·
            refine ⟨1909854974623407479744087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273236649748938319829391 1909854974623407479744087)
            ·
              refine ⟨2864782461935111219616131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909854974623407479744087 2864782461935111219616131)
              ·
                refine ⟨4297173692902666829424197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864782461935111219616131 4297173692902666829424197)
                ·
                  refine ⟨805720067419250030517037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4297173692902666829424197 805720067419250030517037)
                  ·
                    refine ⟨302145025282218761443889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 805720067419250030517037 302145025282218761443889)
                    ·
                      refine ⟨226608768961664071082917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 302145025282218761443889 226608768961664071082917)
                      ·
                        rfl

theorem cell23_441319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_441319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441319 prefixEnd_441319 := by exact prefixLift 441319
  have htrace : WordTrace (prefixWord ++ tailWord_441319) baseStart_441319 baseEnd_441319 := by
    simpa [prefixWord, tailWord_441319, baseEnd_441319] using wordTrace_append hprefix tailTrace_441319
  have hstable : (prefixWord ++ tailWord_441319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441319).length < 2 ^ (prefixWord ++ tailWord_441319).sum := by decide
  have hdescent : baseEnd_441319 < baseStart_441319 := by decide
  rcases family_descends (prefixWord ++ tailWord_441319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441333 : List Nat := [1, 3, 5, 2, 1, 2, 2, 1, 6]
def baseStart_441333 : Nat := 118140960795 + 441333 * 2 ^ 59
def prefixEnd_441333 : Nat := 4983230072969 + 3 ^ 40 * 441333 * 2
def baseEnd_441333 : Nat := 25179550854536335145317

theorem tailTrace_441333 : CollatzResearch.WordTrace tailWord_441333 prefixEnd_441333 25179550854536335145317 := by
  unfold tailWord_441333
  simp only [CollatzResearch.WordTrace]
  refine ⟨16096736910133389520704653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10731157940088926347136435 16096736910133389520704653)
  ·
    refine ⟨6036276341300021070264245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16096736910133389520704653 6036276341300021070264245)
    ·
      refine ⟨565900906996876975337273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6036276341300021070264245 565900906996876975337273)
      ·
        refine ⟨424425680247657731502955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 565900906996876975337273 424425680247657731502955)
        ·
          refine ⟨636638520371486597254433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424425680247657731502955 636638520371486597254433)
          ·
            refine ⟨477478890278614947940825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636638520371486597254433 477478890278614947940825)
            ·
              refine ⟨358109167708961210955619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477478890278614947940825 358109167708961210955619)
              ·
                refine ⟨537163751563441816433429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358109167708961210955619 537163751563441816433429)
                ·
                  refine ⟨25179550854536335145317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 537163751563441816433429 25179550854536335145317)
                  ·
                    rfl

theorem cell23_441333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 6].length) (baseStart_441333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441333 prefixEnd_441333 := by exact prefixLift 441333
  have htrace : WordTrace (prefixWord ++ tailWord_441333) baseStart_441333 baseEnd_441333 := by
    simpa [prefixWord, tailWord_441333, baseEnd_441333] using wordTrace_append hprefix tailTrace_441333
  have hstable : (prefixWord ++ tailWord_441333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441333).length < 2 ^ (prefixWord ++ tailWord_441333).sum := by decide
  have hdescent : baseEnd_441333 < baseStart_441333 := by decide
  rcases family_descends (prefixWord ++ tailWord_441333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441346 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_441346 : Nat := 118140960795 + 441346 * 2 ^ 59
def prefixEnd_441346 : Nat := 4983230072969 + 3 ^ 40 * 441346 * 2
def baseEnd_441346 : Nat := 75540877646445155148431

theorem tailTrace_441346 : CollatzResearch.WordTrace tailWord_441346 prefixEnd_441346 75540877646445155148431 := by
  unfold tailWord_441346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4024302764771573185231973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10731474039390861827285261 4024302764771573185231973)
  ·
    refine ⟨754556768394669972230995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4024302764771573185231973 754556768394669972230995)
    ·
      refine ⟨1131835152592004958346493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754556768394669972230995 1131835152592004958346493)
      ·
        refine ⟨424438182222001859379935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1131835152592004958346493 424438182222001859379935)
        ·
          refine ⟨636657273333002789069903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424438182222001859379935 636657273333002789069903)
          ·
            refine ⟨954985909999504183604855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636657273333002789069903 954985909999504183604855)
            ·
              refine ⟨1432478864999256275407283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954985909999504183604855 1432478864999256275407283)
              ·
                refine ⟨2148718297498884413110925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432478864999256275407283 2148718297498884413110925)
                ·
                  refine ⟨805769361562081654916597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2148718297498884413110925 805769361562081654916597)
                  ·
                    refine ⟨75540877646445155148431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 805769361562081654916597 75540877646445155148431)
                    ·
                      rfl

theorem cell23_441346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_441346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441346 prefixEnd_441346 := by exact prefixLift 441346
  have htrace : WordTrace (prefixWord ++ tailWord_441346) baseStart_441346 baseEnd_441346 := by
    simpa [prefixWord, tailWord_441346, baseEnd_441346] using wordTrace_append hprefix tailTrace_441346
  have hstable : (prefixWord ++ tailWord_441346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441346).length < 2 ^ (prefixWord ++ tailWord_441346).sum := by decide
  have hdescent : baseEnd_441346 < baseStart_441346 := by decide
  rcases family_descends (prefixWord ++ tailWord_441346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441349 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 5, 2, 2]
def baseStart_441349 : Nat := 118140960795 + 441349 * 2 ^ 59
def prefixEnd_441349 : Nat := 4983230072969 + 3 ^ 40 * 441349 * 2
def baseEnd_441349 : Nat := 226624173381298953707779

theorem tailTrace_441349 : CollatzResearch.WordTrace tailWord_441349 prefixEnd_441349 226624173381298953707779 := by
  unfold tailWord_441349
  simp only [CollatzResearch.WordTrace]
  refine ⟨16097320478075424253287101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10731546985383616168858067 16097320478075424253287101)
  ·
    refine ⟨6036495179278284094982663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16097320478075424253287101 6036495179278284094982663)
    ·
      refine ⟨9054742768917426142473995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6036495179278284094982663 9054742768917426142473995)
      ·
        refine ⟨13582114153376139213710993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9054742768917426142473995 13582114153376139213710993)
        ·
          refine ⟨10186585615032104410283245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13582114153376139213710993 10186585615032104410283245)
          ·
            refine ⟨3819969605637039153856217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10186585615032104410283245 3819969605637039153856217)
            ·
              refine ⟨2864977204227779365392163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3819969605637039153856217 2864977204227779365392163)
              ·
                refine ⟨4297465806341669048088245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864977204227779365392163 4297465806341669048088245)
                ·
                  refine ⟨402887419344531473258273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4297465806341669048088245 402887419344531473258273)
                  ·
                    refine ⟨302165564508398604943705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 402887419344531473258273 302165564508398604943705)
                    ·
                      refine ⟨226624173381298953707779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 302165564508398604943705 226624173381298953707779)
                      ·
                        rfl

theorem cell23_441349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 2, 2].length) (baseStart_441349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441349 prefixEnd_441349 := by exact prefixLift 441349
  have htrace : WordTrace (prefixWord ++ tailWord_441349) baseStart_441349 baseEnd_441349 := by
    simpa [prefixWord, tailWord_441349, baseEnd_441349] using wordTrace_append hprefix tailTrace_441349
  have hstable : (prefixWord ++ tailWord_441349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441349).length < 2 ^ (prefixWord ++ tailWord_441349).sum := by decide
  have hdescent : baseEnd_441349 < baseStart_441349 := by decide
  rcases family_descends (prefixWord ++ tailWord_441349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441355 : List Nat := [1, 1, 1, 1, 6, 2, 2, 9]
def baseStart_441355 : Nat := 118140960795 + 441355 * 2 ^ 59
def prefixEnd_441355 : Nat := 4983230072969 + 3 ^ 40 * 441355 * 2
def baseEnd_441355 : Nat := 8393602009823182601213

theorem tailTrace_441355 : CollatzResearch.WordTrace tailWord_441355 prefixEnd_441355 8393602009823182601213 := by
  unfold tailWord_441355
  simp only [CollatzResearch.WordTrace]
  refine ⟨16097539316053687278005519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10731692877369124852003679 16097539316053687278005519)
  ·
    refine ⟨24146308974080530917008279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16097539316053687278005519 24146308974080530917008279)
    ·
      refine ⟨36219463461120796375512419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24146308974080530917008279 36219463461120796375512419)
      ·
        refine ⟨54329195191681194563268629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36219463461120796375512419 54329195191681194563268629)
        ·
          refine ⟨2546681024610055995153217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54329195191681194563268629 2546681024610055995153217)
          ·
            refine ⟨1910010768457541996364913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2546681024610055995153217 1910010768457541996364913)
            ·
              refine ⟨1432508076343156497273685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1910010768457541996364913 1432508076343156497273685)
              ·
                refine ⟨8393602009823182601213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1432508076343156497273685 8393602009823182601213)
                ·
                  rfl

theorem cell23_441355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 9].length) (baseStart_441355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441355 prefixEnd_441355 := by exact prefixLift 441355
  have htrace : WordTrace (prefixWord ++ tailWord_441355) baseStart_441355 baseEnd_441355 := by
    simpa [prefixWord, tailWord_441355, baseEnd_441355] using wordTrace_append hprefix tailTrace_441355
  have hstable : (prefixWord ++ tailWord_441355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441355).length < 2 ^ (prefixWord ++ tailWord_441355).sum := by decide
  have hdescent : baseEnd_441355 < baseStart_441355 := by decide
  rcases family_descends (prefixWord ++ tailWord_441355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441372 : List Nat := [2, 2, 3, 1, 5, 10]
def baseStart_441372 : Nat := 118140960795 + 441372 * 2 ^ 59
def prefixEnd_441372 : Nat := 4983230072969 + 3 ^ 40 * 441372 * 2
def baseEnd_441372 : Nat := 932658368050832772511

theorem tailTrace_441372 : CollatzResearch.WordTrace tailWord_441372 prefixEnd_441372 932658368050832772511 := by
  unfold tailWord_441372
  simp only [CollatzResearch.WordTrace]
  refine ⟨8049079678496049590687185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10732106237994732787582913 8049079678496049590687185)
  ·
    refine ⟨6036809758872037193015389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8049079678496049590687185 6036809758872037193015389)
    ·
      refine ⟨2263803659577013947380771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6036809758872037193015389 2263803659577013947380771)
      ·
        refine ⟨3395705489365520921071157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263803659577013947380771 3395705489365520921071157)
        ·
          refine ⟨318347389628017586350421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3395705489365520921071157 318347389628017586350421)
          ·
            refine ⟨932658368050832772511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 318347389628017586350421 932658368050832772511)
            ·
              rfl

theorem cell23_441372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 10].length) (baseStart_441372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441372 prefixEnd_441372 := by exact prefixLift 441372
  have htrace : WordTrace (prefixWord ++ tailWord_441372) baseStart_441372 baseEnd_441372 := by
    simpa [prefixWord, tailWord_441372, baseEnd_441372] using wordTrace_append hprefix tailTrace_441372
  have hstable : (prefixWord ++ tailWord_441372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441372).length < 2 ^ (prefixWord ++ tailWord_441372).sum := by decide
  have hdescent : baseEnd_441372 < baseStart_441372 := by decide
  rcases family_descends (prefixWord ++ tailWord_441372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441395 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 5]
def baseStart_441395 : Nat := 118140960795 + 441395 * 2 ^ 59
def prefixEnd_441395 : Nat := 4983230072969 + 3 ^ 40 * 441395 * 2
def baseEnd_441395 : Nat := 226647793491405773732567

theorem tailTrace_441395 : CollatzResearch.WordTrace tailWord_441395 prefixEnd_441395 226647793491405773732567 := by
  unfold tailWord_441395
  simp only [CollatzResearch.WordTrace]
  refine ⟨16098998235908774109461639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10732665490605849406307759 16098998235908774109461639)
  ·
    refine ⟨24148497353863161164192459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16098998235908774109461639 24148497353863161164192459)
    ·
      refine ⟨36222746030794741746288689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24148497353863161164192459 36222746030794741746288689)
      ·
        refine ⟨27167059523096056309716517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36222746030794741746288689 27167059523096056309716517)
        ·
          refine ⟨5093823660580510558071847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27167059523096056309716517 5093823660580510558071847)
          ·
            refine ⟨7640735490870765837107771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5093823660580510558071847 7640735490870765837107771)
            ·
              refine ⟨11461103236306148755661657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7640735490870765837107771 11461103236306148755661657)
              ·
                refine ⟨8595827427229611566746243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11461103236306148755661657 8595827427229611566746243)
                ·
                  refine ⟨12893741140844417350119365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8595827427229611566746243 12893741140844417350119365)
                  ·
                    refine ⟨2417576463908328253147381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12893741140844417350119365 2417576463908328253147381)
                    ·
                      refine ⟨226647793491405773732567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2417576463908328253147381 226647793491405773732567)
                      ·
                        rfl

theorem cell23_441395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_441395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441395 prefixEnd_441395 := by exact prefixLift 441395
  have htrace : WordTrace (prefixWord ++ tailWord_441395) baseStart_441395 baseEnd_441395 := by
    simpa [prefixWord, tailWord_441395, baseEnd_441395] using wordTrace_append hprefix tailTrace_441395
  have hstable : (prefixWord ++ tailWord_441395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441395).length < 2 ^ (prefixWord ++ tailWord_441395).sum := by decide
  have hdescent : baseEnd_441395 < baseStart_441395 := by decide
  rcases family_descends (prefixWord ++ tailWord_441395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441396 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_441396 : Nat := 118140960795 + 441396 * 2 ^ 59
def prefixEnd_441396 : Nat := 4983230072969 + 3 ^ 40 * 441396 * 2
def baseEnd_441396 : Nat := 226648306972060269820063

theorem tailTrace_441396 : CollatzResearch.WordTrace tailWord_441396 prefixEnd_441396 226648306972060269820063 := by
  unfold tailWord_441396
  simp only [CollatzResearch.WordTrace]
  refine ⟨8049517354452575640124021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10732689805936767520165361 8049517354452575640124021)
  ·
    refine ⟨754642251979928966261627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8049517354452575640124021 754642251979928966261627)
    ·
      refine ⟨1131963377969893449392441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754642251979928966261627 1131963377969893449392441)
      ·
        refine ⟨848972533477420087044331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1131963377969893449392441 848972533477420087044331)
        ·
          refine ⟨1273458800216130130566497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848972533477420087044331 1273458800216130130566497)
          ·
            refine ⟨955094100162097597924873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1273458800216130130566497 955094100162097597924873)
            ·
              refine ⟨716320575121573198443655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955094100162097597924873 716320575121573198443655)
              ·
                refine ⟨1074480862682359797665483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716320575121573198443655 1074480862682359797665483)
                ·
                  refine ⟨1611721294023539696498225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074480862682359797665483 1611721294023539696498225)
                  ·
                    refine ⟨1208790970517654772373669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1611721294023539696498225 1208790970517654772373669)
                    ·
                      refine ⟨226648306972060269820063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1208790970517654772373669 226648306972060269820063)
                      ·
                        rfl

theorem cell23_441396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_441396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441396 prefixEnd_441396 := by exact prefixLift 441396
  have htrace : WordTrace (prefixWord ++ tailWord_441396) baseStart_441396 baseEnd_441396 := by
    simpa [prefixWord, tailWord_441396, baseEnd_441396] using wordTrace_append hprefix tailTrace_441396
  have hstable : (prefixWord ++ tailWord_441396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441396).length < 2 ^ (prefixWord ++ tailWord_441396).sum := by decide
  have hdescent : baseEnd_441396 < baseStart_441396 := by decide
  rcases family_descends (prefixWord ++ tailWord_441396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441452 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_441452 : Nat := 118140960795 + 441452 * 2 ^ 59
def prefixEnd_441452 : Nat := 4983230072969 + 3 ^ 40 * 441452 * 2
def baseEnd_441452 : Nat := 226677061888712050719805

theorem tailTrace_441452 : CollatzResearch.WordTrace tailWord_441452 prefixEnd_441452 226677061888712050719805 := by
  unfold tailWord_441452
  simp only [CollatzResearch.WordTrace]
  refine ⟨8050538598351136422143305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10734051464468181896191073 8050538598351136422143305)
  ·
    refine ⟨6037903948763352316607479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8050538598351136422143305 6037903948763352316607479)
    ·
      refine ⟨9056855923145028474911219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6037903948763352316607479 9056855923145028474911219)
      ·
        refine ⟨13585283884717542712366829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9056855923145028474911219 13585283884717542712366829)
        ·
          refine ⟨5094481456769078517137561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13585283884717542712366829 5094481456769078517137561)
          ·
            refine ⟨3820861092576808887853171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5094481456769078517137561 3820861092576808887853171)
            ·
              refine ⟨5731291638865213331779757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820861092576808887853171 5731291638865213331779757)
              ·
                refine ⟨2149234364574454999417409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5731291638865213331779757 2149234364574454999417409)
                ·
                  refine ⟨1611925773430841249563057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2149234364574454999417409 1611925773430841249563057)
                  ·
                    refine ⟨1208944330073130937172293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1611925773430841249563057 1208944330073130937172293)
                    ·
                      refine ⟨226677061888712050719805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1208944330073130937172293 226677061888712050719805)
                      ·
                        rfl

theorem cell23_441452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_441452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441452 prefixEnd_441452 := by exact prefixLift 441452
  have htrace : WordTrace (prefixWord ++ tailWord_441452) baseStart_441452 baseEnd_441452 := by
    simpa [prefixWord, tailWord_441452, baseEnd_441452] using wordTrace_append hprefix tailTrace_441452
  have hstable : (prefixWord ++ tailWord_441452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441452).length < 2 ^ (prefixWord ++ tailWord_441452).sum := by decide
  have hdescent : baseEnd_441452 < baseStart_441452 := by decide
  rcases family_descends (prefixWord ++ tailWord_441452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441472 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 3]
def baseStart_441472 : Nat := 118140960795 + 441472 * 2 ^ 59
def prefixEnd_441472 : Nat := 4983230072969 + 3 ^ 40 * 441472 * 2
def baseEnd_441472 : Nat := 226687331501801972469713

theorem tailTrace_441472 : CollatzResearch.WordTrace tailWord_441472 prefixEnd_441472 226687331501801972469713 := by
  unfold tailWord_441472
  simp only [CollatzResearch.WordTrace]
  refine ⟨8050903328314908130007335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10734537771086544173343113 8050903328314908130007335)
  ·
    refine ⟨12076354992472362195011003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8050903328314908130007335 12076354992472362195011003)
    ·
      refine ⟨18114532488708543292516505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12076354992472362195011003 18114532488708543292516505)
      ·
        refine ⟨13585899366531407469387379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18114532488708543292516505 13585899366531407469387379)
        ·
          refine ⟨20378849049797111204081069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13585899366531407469387379 20378849049797111204081069)
          ·
            refine ⟨7642068393673916701530401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20378849049797111204081069 7642068393673916701530401)
            ·
              refine ⟨5731551295255437526147801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7642068393673916701530401 5731551295255437526147801)
              ·
                refine ⟨4298663471441578144610851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5731551295255437526147801 4298663471441578144610851)
                ·
                  refine ⟨6447995207162367216916277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298663471441578144610851 6447995207162367216916277)
                  ·
                    refine ⟨604499550671471926585901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6447995207162367216916277 604499550671471926585901)
                    ·
                      refine ⟨226687331501801972469713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 604499550671471926585901 226687331501801972469713)
                      ·
                        rfl

theorem cell23_441472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_441472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441472 prefixEnd_441472 := by exact prefixLift 441472
  have htrace : WordTrace (prefixWord ++ tailWord_441472) baseStart_441472 baseEnd_441472 := by
    simpa [prefixWord, tailWord_441472, baseEnd_441472] using wordTrace_append hprefix tailTrace_441472
  have hstable : (prefixWord ++ tailWord_441472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441472).length < 2 ^ (prefixWord ++ tailWord_441472).sum := by decide
  have hdescent : baseEnd_441472 < baseStart_441472 := by decide
  rcases family_descends (prefixWord ++ tailWord_441472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441529 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 2, 1, 4]
def baseStart_441529 : Nat := 118140960795 + 441529 * 2 ^ 59
def prefixEnd_441529 : Nat := 4983230072969 + 3 ^ 40 * 441529 * 2
def baseEnd_441529 : Nat := 226716599899108249456951

theorem tailTrace_441529 : CollatzResearch.WordTrace tailWord_441529 prefixEnd_441529 226716599899108249456951 := by
  unfold tailWord_441529
  simp only [CollatzResearch.WordTrace]
  refine ⟨16103885617423314994839641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10735923744948876663226427 16103885617423314994839641)
  ·
    refine ⟨12077914213067486246129731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16103885617423314994839641 12077914213067486246129731)
    ·
      refine ⟨18116871319601229369194597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12077914213067486246129731 18116871319601229369194597)
      ·
        refine ⟨3396913372425230506723987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18116871319601229369194597 3396913372425230506723987)
        ·
          refine ⟨5095370058637845760085981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3396913372425230506723987 5095370058637845760085981)
          ·
            refine ⟨1910763771989192160032243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5095370058637845760085981 1910763771989192160032243)
            ·
              refine ⟨2866145657983788240048365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910763771989192160032243 2866145657983788240048365)
              ·
                refine ⟨1074804621743920590018137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2866145657983788240048365 1074804621743920590018137)
                ·
                  refine ⟨806103466307940442513603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1074804621743920590018137 806103466307940442513603)
                  ·
                    refine ⟨1209155199461910663770405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 806103466307940442513603 1209155199461910663770405)
                    ·
                      refine ⟨226716599899108249456951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1209155199461910663770405 226716599899108249456951)
                      ·
                        rfl

theorem cell23_441529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_441529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441529 prefixEnd_441529 := by exact prefixLift 441529
  have htrace : WordTrace (prefixWord ++ tailWord_441529) baseStart_441529 baseEnd_441529 := by
    simpa [prefixWord, tailWord_441529, baseEnd_441529] using wordTrace_append hprefix tailTrace_441529
  have hstable : (prefixWord ++ tailWord_441529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441529).length < 2 ^ (prefixWord ++ tailWord_441529).sum := by decide
  have hdescent : baseEnd_441529 < baseStart_441529 := by decide
  rcases family_descends (prefixWord ++ tailWord_441529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441569 : List Nat := [1, 2, 3, 1, 3, 2, 2, 3, 6]
def baseStart_441569 : Nat := 118140960795 + 441569 * 2 ^ 59
def prefixEnd_441569 : Nat := 4983230072969 + 3 ^ 40 * 441569 * 2
def baseEnd_441569 : Nat := 25193015458365343661863

theorem tailTrace_441569 : CollatzResearch.WordTrace tailWord_441569 prefixEnd_441569 25193015458365343661863 := by
  unfold tailWord_441569
  simp only [CollatzResearch.WordTrace]
  refine ⟨16105344537278401826295761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10736896358185601217530507 16105344537278401826295761)
  ·
    refine ⟨12079008402958801369721821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16105344537278401826295761 12079008402958801369721821)
    ·
      refine ⟨4529628151109550513645683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12079008402958801369721821 4529628151109550513645683)
      ·
        refine ⟨6794442226664325770468525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4529628151109550513645683 6794442226664325770468525)
        ·
          refine ⟨2547915834999122163925697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6794442226664325770468525 2547915834999122163925697)
          ·
            refine ⟨1910936876249341622944273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2547915834999122163925697 1910936876249341622944273)
            ·
              refine ⟨1433202657187006217208205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1910936876249341622944273 1433202657187006217208205)
              ·
                refine ⟨537450996445127331453077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1433202657187006217208205 537450996445127331453077)
                ·
                  refine ⟨25193015458365343661863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 537450996445127331453077 25193015458365343661863)
                  ·
                    rfl

theorem cell23_441569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 6].length) (baseStart_441569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441569 prefixEnd_441569 := by exact prefixLift 441569
  have htrace : WordTrace (prefixWord ++ tailWord_441569) baseStart_441569 baseEnd_441569 := by
    simpa [prefixWord, tailWord_441569, baseEnd_441569] using wordTrace_append hprefix tailTrace_441569
  have hstable : (prefixWord ++ tailWord_441569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441569).length < 2 ^ (prefixWord ++ tailWord_441569).sum := by decide
  have hdescent : baseEnd_441569 < baseStart_441569 := by decide
  rcases family_descends (prefixWord ++ tailWord_441569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441583 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 2, 2, 3]
def baseStart_441583 : Nat := 118140960795 + 441583 * 2 ^ 59
def prefixEnd_441583 : Nat := 4983230072969 + 3 ^ 40 * 441583 * 2
def baseEnd_441583 : Nat := 226744327854451038181703

theorem tailTrace_441583 : CollatzResearch.WordTrace tailWord_441583 prefixEnd_441583 226744327854451038181703 := by
  unfold tailWord_441583
  simp only [CollatzResearch.WordTrace]
  refine ⟨16105855159227682217305403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10737236772818454811536935 16105855159227682217305403)
  ·
    refine ⟨24158782738841523325958105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16105855159227682217305403 24158782738841523325958105)
    ·
      refine ⟨18119087054131142494468579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24158782738841523325958105 18119087054131142494468579)
      ·
        refine ⟨27178630581196713741702869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18119087054131142494468579 27178630581196713741702869)
        ·
          refine ⟨636999154246797978321161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27178630581196713741702869 636999154246797978321161)
          ·
            refine ⟨477749365685098483740871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636999154246797978321161 477749365685098483740871)
            ·
              refine ⟨716624048527647725611307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477749365685098483740871 716624048527647725611307)
              ·
                refine ⟨1074936072791471588416961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716624048527647725611307 1074936072791471588416961)
                ·
                  refine ⟨806202054593603691312721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1074936072791471588416961 806202054593603691312721)
                  ·
                    refine ⟨604651540945202768484541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 806202054593603691312721 604651540945202768484541)
                    ·
                      refine ⟨226744327854451038181703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 604651540945202768484541 226744327854451038181703)
                      ·
                        rfl

theorem cell23_441583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 2, 3].length) (baseStart_441583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441583 prefixEnd_441583 := by exact prefixLift 441583
  have htrace : WordTrace (prefixWord ++ tailWord_441583) baseStart_441583 baseEnd_441583 := by
    simpa [prefixWord, tailWord_441583, baseEnd_441583] using wordTrace_append hprefix tailTrace_441583
  have hstable : (prefixWord ++ tailWord_441583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441583).length < 2 ^ (prefixWord ++ tailWord_441583).sum := by decide
  have hdescent : baseEnd_441583 < baseStart_441583 := by decide
  rcases family_descends (prefixWord ++ tailWord_441583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441592 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_441592 : Nat := 118140960795 + 441592 * 2 ^ 59
def prefixEnd_441592 : Nat := 4983230072969 + 3 ^ 40 * 441592 * 2
def baseEnd_441592 : Nat := 226748949180341502969161

theorem tailTrace_441592 : CollatzResearch.WordTrace tailWord_441592 prefixEnd_441592 226748949180341502969161 := by
  unfold tailWord_441592
  simp only [CollatzResearch.WordTrace]
  refine ⟨8053091708097538377191515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10737455610796717836255353 8053091708097538377191515)
  ·
    refine ⟨12079637562146307565787273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8053091708097538377191515 12079637562146307565787273)
    ·
      refine ⟨9059728171609730674340455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12079637562146307565787273 9059728171609730674340455)
      ·
        refine ⟨13589592257414596011510683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9059728171609730674340455 13589592257414596011510683)
        ·
          refine ⟨20384388386121894017266025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13589592257414596011510683 20384388386121894017266025)
          ·
            refine ⟨15288291289591420512949519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20384388386121894017266025 15288291289591420512949519)
            ·
              refine ⟨22932436934387130769424279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15288291289591420512949519 22932436934387130769424279)
              ·
                refine ⟨34398655401580696154136419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22932436934387130769424279 34398655401580696154136419)
                ·
                  refine ⟨51597983102371044231204629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34398655401580696154136419 51597983102371044231204629)
                  ·
                    refine ⟨2418655457923642698337717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51597983102371044231204629 2418655457923642698337717)
                    ·
                      refine ⟨226748949180341502969161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2418655457923642698337717 226748949180341502969161)
                      ·
                        rfl

theorem cell23_441592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_441592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441592 prefixEnd_441592 := by exact prefixLift 441592
  have htrace : WordTrace (prefixWord ++ tailWord_441592) baseStart_441592 baseEnd_441592 := by
    simpa [prefixWord, tailWord_441592, baseEnd_441592] using wordTrace_append hprefix tailTrace_441592
  have hstable : (prefixWord ++ tailWord_441592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441592).length < 2 ^ (prefixWord ++ tailWord_441592).sum := by decide
  have hdescent : baseEnd_441592 < baseStart_441592 := by decide
  rcases family_descends (prefixWord ++ tailWord_441592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441636 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 2, 6, 2]
def baseStart_441636 : Nat := 118140960795 + 441636 * 2 ^ 59
def prefixEnd_441636 : Nat := 4983230072969 + 3 ^ 40 * 441636 * 2
def baseEnd_441636 : Nat := 226771542329139330818959

theorem tailTrace_441636 : CollatzResearch.WordTrace tailWord_441636 prefixEnd_441636 226771542329139330818959 := by
  unfold tailWord_441636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8053894114017836134492381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10738525485357114845989841 8053894114017836134492381)
  ·
    refine ⟨3020210292756688550434643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8053894114017836134492381 3020210292756688550434643)
    ·
      refine ⟨4530315439135032825651965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3020210292756688550434643 4530315439135032825651965)
      ·
        refine ⟨1698868289675637309619487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4530315439135032825651965 1698868289675637309619487)
        ·
          refine ⟨2548302434513455964429231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1698868289675637309619487 2548302434513455964429231)
          ·
            refine ⟨3822453651770183946643847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2548302434513455964429231 3822453651770183946643847)
            ·
              refine ⟨5733680477655275919965771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822453651770183946643847 5733680477655275919965771)
              ·
                refine ⟨8600520716482913879948657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733680477655275919965771 8600520716482913879948657)
                ·
                  refine ⟨6450390537362185409961493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8600520716482913879948657 6450390537362185409961493)
                  ·
                    refine ⟨302362056438852441091945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6450390537362185409961493 302362056438852441091945)
                    ·
                      refine ⟨226771542329139330818959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 302362056438852441091945 226771542329139330818959)
                      ·
                        rfl

theorem cell23_441636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_441636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441636 prefixEnd_441636 := by exact prefixLift 441636
  have htrace : WordTrace (prefixWord ++ tailWord_441636) baseStart_441636 baseEnd_441636 := by
    simpa [prefixWord, tailWord_441636, baseEnd_441636] using wordTrace_append hprefix tailTrace_441636
  have hstable : (prefixWord ++ tailWord_441636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441636).length < 2 ^ (prefixWord ++ tailWord_441636).sum := by decide
  have hdescent : baseEnd_441636 < baseStart_441636 := by decide
  rcases family_descends (prefixWord ++ tailWord_441636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441703 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_441703 : Nat := 118140960795 + 441703 * 2 ^ 59
def prefixEnd_441703 : Nat := 4983230072969 + 3 ^ 40 * 441703 * 2
def baseEnd_441703 : Nat := 226805945532990568681151

theorem tailTrace_441703 : CollatzResearch.WordTrace tailWord_441703 prefixEnd_441703 226805945532990568681151 := by
  unfold tailWord_441703
  simp only [CollatzResearch.WordTrace]
  refine ⟨16110231918792942711673763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10740154612528628474449175 16110231918792942711673763)
  ·
    refine ⟨24165347878189414067510645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16110231918792942711673763 24165347878189414067510645)
    ·
      refine ⟨2265501363580257568829123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24165347878189414067510645 2265501363580257568829123)
      ·
        refine ⟨3398252045370386353243685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2265501363580257568829123 3398252045370386353243685)
        ·
          refine ⟨637172258506947441233191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3398252045370386353243685 637172258506947441233191)
          ·
            refine ⟨955758387760421161849787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637172258506947441233191 955758387760421161849787)
            ·
              refine ⟨1433637581640631742774681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955758387760421161849787 1433637581640631742774681)
              ·
                refine ⟨1075228186230473807081011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1433637581640631742774681 1075228186230473807081011)
                ·
                  refine ⟨1612842279345710710621517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075228186230473807081011 1612842279345710710621517)
                  ·
                    refine ⟨604815854754641516483069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1612842279345710710621517 604815854754641516483069)
                    ·
                      refine ⟨226805945532990568681151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 604815854754641516483069 226805945532990568681151)
                      ·
                        rfl

theorem cell23_441703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_441703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441703 prefixEnd_441703 := by exact prefixLift 441703
  have htrace : WordTrace (prefixWord ++ tailWord_441703) baseStart_441703 baseEnd_441703 := by
    simpa [prefixWord, tailWord_441703, baseEnd_441703] using wordTrace_append hprefix tailTrace_441703
  have hstable : (prefixWord ++ tailWord_441703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441703).length < 2 ^ (prefixWord ++ tailWord_441703).sum := by decide
  have hdescent : baseEnd_441703 < baseStart_441703 := by decide
  rcases family_descends (prefixWord ++ tailWord_441703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441713 : List Nat := [1, 2, 2, 2, 1, 2, 2, 5, 1, 3, 2]
def baseStart_441713 : Nat := 118140960795 + 441713 * 2 ^ 59
def prefixEnd_441713 : Nat := 4983230072969 + 3 ^ 40 * 441713 * 2
def baseEnd_441713 : Nat := 226811080339535529556105

theorem tailTrace_441713 : CollatzResearch.WordTrace tailWord_441713 prefixEnd_441713 226811080339535529556105 := by
  unfold tailWord_441713
  simp only [CollatzResearch.WordTrace]
  refine ⟨16110596648756714419537793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10740397765837809613025195 16110596648756714419537793)
  ·
    refine ⟨12082947486567535814653345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16110596648756714419537793 12082947486567535814653345)
    ·
      refine ⟨9062210614925651860990009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12082947486567535814653345 9062210614925651860990009)
      ·
        refine ⟨6796657961194238895742507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9062210614925651860990009 6796657961194238895742507)
        ·
          refine ⟨10194986941791358343613761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6796657961194238895742507 10194986941791358343613761)
          ·
            refine ⟨7646240206343518757710321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10194986941791358343613761 7646240206343518757710321)
            ·
              refine ⟨5734680154757639068282741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7646240206343518757710321 5734680154757639068282741)
              ·
                refine ⟨537626264508528662651507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5734680154757639068282741 537626264508528662651507)
                ·
                  refine ⟨806439396762792993977261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537626264508528662651507 806439396762792993977261)
                  ·
                    refine ⟨302414773786047372741473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 806439396762792993977261 302414773786047372741473)
                    ·
                      refine ⟨226811080339535529556105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 302414773786047372741473 226811080339535529556105)
                      ·
                        rfl

theorem cell23_441713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_441713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441713 prefixEnd_441713 := by exact prefixLift 441713
  have htrace : WordTrace (prefixWord ++ tailWord_441713) baseStart_441713 baseEnd_441713 := by
    simpa [prefixWord, tailWord_441713, baseEnd_441713] using wordTrace_append hprefix tailTrace_441713
  have hstable : (prefixWord ++ tailWord_441713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441713).length < 2 ^ (prefixWord ++ tailWord_441713).sum := by decide
  have hdescent : baseEnd_441713 < baseStart_441713 := by decide
  rcases family_descends (prefixWord ++ tailWord_441713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441719 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 2, 6]
def baseStart_441719 : Nat := 118140960795 + 441719 * 2 ^ 59
def prefixEnd_441719 : Nat := 4983230072969 + 3 ^ 40 * 441719 * 2
def baseEnd_441719 : Nat := 75604720407820835360359

theorem tailTrace_441719 : CollatzResearch.WordTrace tailWord_441719 prefixEnd_441719 75604720407820835360359 := by
  unfold tailWord_441719
  simp only [CollatzResearch.WordTrace]
  refine ⟨16110815486734977444256211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10740543657823318296170807 16110815486734977444256211)
  ·
    refine ⟨24166223230102466166384317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16110815486734977444256211 24166223230102466166384317)
    ·
      refine ⟨9062333711288424812394119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24166223230102466166384317 9062333711288424812394119)
      ·
        refine ⟨13593500566932637218591179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9062333711288424812394119 13593500566932637218591179)
        ·
          refine ⟨20390250850398955827886769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13593500566932637218591179 20390250850398955827886769)
          ·
            refine ⟨15292688137799216870915077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20390250850398955827886769 15292688137799216870915077)
            ·
              refine ⟨2867379025837353163296577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15292688137799216870915077 2867379025837353163296577)
              ·
                refine ⟨2150534269378014872472433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2867379025837353163296577 2150534269378014872472433)
                ·
                  refine ⟨1612900702033511154354325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2150534269378014872472433 1612900702033511154354325)
                  ·
                    refine ⟨75604720407820835360359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1612900702033511154354325 75604720407820835360359)
                    ·
                      rfl

theorem cell23_441719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_441719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441719 prefixEnd_441719 := by exact prefixLift 441719
  have htrace : WordTrace (prefixWord ++ tailWord_441719) baseStart_441719 baseEnd_441719 := by
    simpa [prefixWord, tailWord_441719, baseEnd_441719] using wordTrace_append hprefix tailTrace_441719
  have hstable : (prefixWord ++ tailWord_441719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441719).length < 2 ^ (prefixWord ++ tailWord_441719).sum := by decide
  have hdescent : baseEnd_441719 < baseStart_441719 := by decide
  rcases family_descends (prefixWord ++ tailWord_441719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441736 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 2, 6]
def baseStart_441736 : Nat := 118140960795 + 441736 * 2 ^ 59
def prefixEnd_441736 : Nat := 4983230072969 + 3 ^ 40 * 441736 * 2
def baseEnd_441736 : Nat := 75607630131529646522833

theorem tailTrace_441736 : CollatzResearch.WordTrace tailWord_441736 prefixEnd_441736 75607630131529646522833 := by
  unfold tailWord_441736
  simp only [CollatzResearch.WordTrace]
  refine ⟨8055717763836694673812531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10740957018448926231750041 8055717763836694673812531)
  ·
    refine ⟨12083576645755042010718797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8055717763836694673812531 12083576645755042010718797)
    ·
      refine ⟨4531341242158140754019549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12083576645755042010718797 4531341242158140754019549)
      ·
        refine ⟨1699252965809302782757331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4531341242158140754019549 1699252965809302782757331)
        ·
          refine ⟨2548879448713954174135997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699252965809302782757331 2548879448713954174135997)
          ·
            refine ⟨955829793267732815300999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2548879448713954174135997 955829793267732815300999)
            ·
              refine ⟨1433744689901599222951499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955829793267732815300999 1433744689901599222951499)
              ·
                refine ⟨2150617034852398834427249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433744689901599222951499 2150617034852398834427249)
                ·
                  refine ⟨1612962776139299125820437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2150617034852398834427249 1612962776139299125820437)
                  ·
                    refine ⟨75607630131529646522833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1612962776139299125820437 75607630131529646522833)
                    ·
                      rfl

theorem cell23_441736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_441736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441736 prefixEnd_441736 := by exact prefixLift 441736
  have htrace : WordTrace (prefixWord ++ tailWord_441736) baseStart_441736 baseEnd_441736 := by
    simpa [prefixWord, tailWord_441736, baseEnd_441736] using wordTrace_append hprefix tailTrace_441736
  have hstable : (prefixWord ++ tailWord_441736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441736).length < 2 ^ (prefixWord ++ tailWord_441736).sum := by decide
  have hdescent : baseEnd_441736 < baseStart_441736 := by decide
  rcases family_descends (prefixWord ++ tailWord_441736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441749 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 9]
def baseStart_441749 : Nat := 118140960795 + 441749 * 2 ^ 59
def prefixEnd_441749 : Nat := 4983230072969 + 3 ^ 40 * 441749 * 2
def baseEnd_441749 : Nat := 25203285071455265411771

theorem tailTrace_441749 : CollatzResearch.WordTrace tailWord_441749 prefixEnd_441749 25203285071455265411771 := by
  unfold tailWord_441749
  simp only [CollatzResearch.WordTrace]
  refine ⟨16111909676626292567848301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10741273117750861711898867 16111909676626292567848301)
  ·
    refine ⟨6041966128734859712943113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16111909676626292567848301 6041966128734859712943113)
    ·
      refine ⟨4531474596551144784707335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6041966128734859712943113 4531474596551144784707335)
      ·
        refine ⟨6797211894826717177061003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4531474596551144784707335 6797211894826717177061003)
        ·
          refine ⟨10195817842240075765591505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6797211894826717177061003 10195817842240075765591505)
          ·
            refine ⟨7646863381680056824193629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10195817842240075765591505 7646863381680056824193629)
            ·
              refine ⟨2867573768130021309072611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7646863381680056824193629 2867573768130021309072611)
              ·
                refine ⟨4301360652195031963608917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2867573768130021309072611 4301360652195031963608917)
                ·
                  refine ⟨25203285071455265411771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4301360652195031963608917 25203285071455265411771)
                  ·
                    rfl

theorem cell23_441749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_441749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441749 prefixEnd_441749 := by exact prefixLift 441749
  have htrace : WordTrace (prefixWord ++ tailWord_441749) baseStart_441749 baseEnd_441749 := by
    simpa [prefixWord, tailWord_441749, baseEnd_441749] using wordTrace_append hprefix tailTrace_441749
  have hstable : (prefixWord ++ tailWord_441749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441749).length < 2 ^ (prefixWord ++ tailWord_441749).sum := by decide
  have hdescent : baseEnd_441749 < baseStart_441749 := by decide
  rcases family_descends (prefixWord ++ tailWord_441749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441773 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_441773 : Nat := 118140960795 + 441773 * 2 ^ 59
def prefixEnd_441773 : Nat := 4983230072969 + 3 ^ 40 * 441773 * 2
def baseEnd_441773 : Nat := 226841889178805294805829

theorem tailTrace_441773 : CollatzResearch.WordTrace tailWord_441773 prefixEnd_441773 226841889178805294805829 := by
  unfold tailWord_441773
  simp only [CollatzResearch.WordTrace]
  refine ⟨16112785028539344666721973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10741856685692896444481315 16112785028539344666721973)
  ·
    refine ⟨1510573596425563562505185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16112785028539344666721973 1510573596425563562505185)
    ·
      refine ⟨1132930197319172671878889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1510573596425563562505185 1132930197319172671878889)
      ·
        refine ⟨849697647989379503909167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1132930197319172671878889 849697647989379503909167)
        ·
          refine ⟨1274546471984069255863751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849697647989379503909167 1274546471984069255863751)
          ·
            refine ⟨1911819707976103883795627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274546471984069255863751 1911819707976103883795627)
            ·
              refine ⟨2867729561964155825693441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1911819707976103883795627 2867729561964155825693441)
              ·
                refine ⟨2150797171473116869270081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2867729561964155825693441 2150797171473116869270081)
                ·
                  refine ⟨1613097878604837651952561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2150797171473116869270081 1613097878604837651952561)
                  ·
                    refine ⟨1209823408953628238964421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1613097878604837651952561 1209823408953628238964421)
                    ·
                      refine ⟨226841889178805294805829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1209823408953628238964421 226841889178805294805829)
                      ·
                        rfl

theorem cell23_441773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_441773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441773 prefixEnd_441773 := by exact prefixLift 441773
  have htrace : WordTrace (prefixWord ++ tailWord_441773) baseStart_441773 baseEnd_441773 := by
    simpa [prefixWord, tailWord_441773, baseEnd_441773] using wordTrace_append hprefix tailTrace_441773
  have hstable : (prefixWord ++ tailWord_441773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441773).length < 2 ^ (prefixWord ++ tailWord_441773).sum := by decide
  have hdescent : baseEnd_441773 < baseStart_441773 := by decide
  rcases family_descends (prefixWord ++ tailWord_441773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441816 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_441816 : Nat := 118140960795 + 441816 * 2 ^ 59
def prefixEnd_441816 : Nat := 4983230072969 + 3 ^ 40 * 441816 * 2
def baseEnd_441816 : Nat := 226863968846948626568131

theorem tailTrace_441816 : CollatzResearch.WordTrace tailWord_441816 prefixEnd_441816 226863968846948626568131 := by
  unfold tailWord_441816
  simp only [CollatzResearch.WordTrace]
  refine ⟨8057176683691781505268651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10742902244922375340358201 8057176683691781505268651)
  ·
    refine ⟨12085765025537672257902977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8057176683691781505268651 12085765025537672257902977)
    ·
      refine ⟨9064323769153254193427233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12085765025537672257902977 9064323769153254193427233)
      ·
        refine ⟨6798242826864940645070425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9064323769153254193427233 6798242826864940645070425)
        ·
          refine ⟨5098682120148705483802819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6798242826864940645070425 5098682120148705483802819)
          ·
            refine ⟨7648023180223058225704229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5098682120148705483802819 7648023180223058225704229)
            ·
              refine ⟨1434004346291823417319543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7648023180223058225704229 1434004346291823417319543)
              ·
                refine ⟨2151006519437735125979315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1434004346291823417319543 2151006519437735125979315)
                ·
                  refine ⟨3226509779156602688968973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151006519437735125979315 3226509779156602688968973)
                  ·
                    refine ⟨1209941167183726008363365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3226509779156602688968973 1209941167183726008363365)
                    ·
                      refine ⟨226863968846948626568131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1209941167183726008363365 226863968846948626568131)
                      ·
                        rfl

theorem cell23_441816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_441816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441816 prefixEnd_441816 := by exact prefixLift 441816
  have htrace : WordTrace (prefixWord ++ tailWord_441816) baseStart_441816 baseEnd_441816 := by
    simpa [prefixWord, tailWord_441816, baseEnd_441816] using wordTrace_append hprefix tailTrace_441816
  have hstable : (prefixWord ++ tailWord_441816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441816).length < 2 ^ (prefixWord ++ tailWord_441816).sum := by decide
  have hdescent : baseEnd_441816 < baseStart_441816 := by decide
  rcases family_descends (prefixWord ++ tailWord_441816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441836 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 3]
def baseStart_441836 : Nat := 118140960795 + 441836 * 2 ^ 59
def prefixEnd_441836 : Nat := 4983230072969 + 3 ^ 40 * 441836 * 2
def baseEnd_441836 : Nat := 226874238460038548318039

theorem tailTrace_441836 : CollatzResearch.WordTrace tailWord_441836 prefixEnd_441836 226874238460038548318039 := by
  unfold tailWord_441836
  simp only [CollatzResearch.WordTrace]
  refine ⟨8057541413655553213132681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10743388551540737617510241 8057541413655553213132681)
  ·
    refine ⟨6043156060241664909849511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8057541413655553213132681 6043156060241664909849511)
    ·
      refine ⟨9064734090362497364774267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6043156060241664909849511 9064734090362497364774267)
      ·
        refine ⟨13597101135543746047161401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9064734090362497364774267 13597101135543746047161401)
        ·
          refine ⟨10197825851657809535371051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13597101135543746047161401 10197825851657809535371051)
          ·
            refine ⟨15296738777486714303056577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10197825851657809535371051 15296738777486714303056577)
            ·
              refine ⟨11472554083115035727292433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15296738777486714303056577 11472554083115035727292433)
              ·
                refine ⟨8604415562336276795469325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11472554083115035727292433 8604415562336276795469325)
                ·
                  refine ⟨3226655835876103798300997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8604415562336276795469325 3226655835876103798300997)
                  ·
                    refine ⟨604997969226769462181437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3226655835876103798300997 604997969226769462181437)
                    ·
                      refine ⟨226874238460038548318039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 604997969226769462181437 226874238460038548318039)
                      ·
                        rfl

theorem cell23_441836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_441836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441836 prefixEnd_441836 := by exact prefixLift 441836
  have htrace : WordTrace (prefixWord ++ tailWord_441836) baseStart_441836 baseEnd_441836 := by
    simpa [prefixWord, tailWord_441836, baseEnd_441836] using wordTrace_append hprefix tailTrace_441836
  have hstable : (prefixWord ++ tailWord_441836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441836).length < 2 ^ (prefixWord ++ tailWord_441836).sum := by decide
  have hdescent : baseEnd_441836 < baseStart_441836 := by decide
  rcases family_descends (prefixWord ++ tailWord_441836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441893 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 3, 5, 2]
def baseStart_441893 : Nat := 118140960795 + 441893 * 2 ^ 59
def prefixEnd_441893 : Nat := 4983230072969 + 3 ^ 40 * 441893 * 2
def baseEnd_441893 : Nat := 226903506857344825305277

theorem tailTrace_441893 : CollatzResearch.WordTrace tailWord_441893 prefixEnd_441893 226903506857344825305277 := by
  unfold tailWord_441893
  simp only [CollatzResearch.WordTrace]
  refine ⟨16117161788104605161090333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10744774525403070107393555 16117161788104605161090333)
  ·
    refine ⟨6043935670539226935408875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16117161788104605161090333 6043935670539226935408875)
    ·
      refine ⟨9065903505808840403113313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6043935670539226935408875 9065903505808840403113313)
      ·
        refine ⟨6799427629356630302334985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9065903505808840403113313 6799427629356630302334985)
        ·
          refine ⟨5099570722017472726751239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6799427629356630302334985 5099570722017472726751239)
          ·
            refine ⟨7649356083026209090126859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5099570722017472726751239 7649356083026209090126859)
            ·
              refine ⟨11474034124539313635190289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649356083026209090126859 11474034124539313635190289)
              ·
                refine ⟨8605525593404485226392717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11474034124539313635190289 8605525593404485226392717)
                ·
                  refine ⟨3227072097526681959897269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8605525593404485226392717 3227072097526681959897269)
                  ·
                    refine ⟨302538009143126433740369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3227072097526681959897269 302538009143126433740369)
                    ·
                      refine ⟨226903506857344825305277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 302538009143126433740369 226903506857344825305277)
                      ·
                        rfl

theorem cell23_441893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_441893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441893 prefixEnd_441893 := by exact prefixLift 441893
  have htrace : WordTrace (prefixWord ++ tailWord_441893) baseStart_441893 baseEnd_441893 := by
    simpa [prefixWord, tailWord_441893, baseEnd_441893] using wordTrace_append hprefix tailTrace_441893
  have hstable : (prefixWord ++ tailWord_441893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441893).length < 2 ^ (prefixWord ++ tailWord_441893).sum := by decide
  have hdescent : baseEnd_441893 < baseStart_441893 := by decide
  rcases family_descends (prefixWord ++ tailWord_441893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441917 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 3, 1, 3]
def baseStart_441917 : Nat := 118140960795 + 441917 * 2 ^ 59
def prefixEnd_441917 : Nat := 4983230072969 + 3 ^ 40 * 441917 * 2
def baseEnd_441917 : Nat := 226915830393052731405167

theorem tailTrace_441917 : CollatzResearch.WordTrace tailWord_441917 prefixEnd_441917 226915830393052731405167 := by
  unfold tailWord_441917
  simp only [CollatzResearch.WordTrace]
  refine ⟨16118037140017657259964005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10745358093345104839976003 16118037140017657259964005)
  ·
    refine ⟨3022131963753310736243251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16118037140017657259964005 3022131963753310736243251)
    ·
      refine ⟨4533197945629966104364877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3022131963753310736243251 4533197945629966104364877)
      ·
        refine ⟨1699949229611237289136829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4533197945629966104364877 1699949229611237289136829)
        ·
          refine ⟨637480961104213983426311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1699949229611237289136829 637480961104213983426311)
          ·
            refine ⟨956221441656320975139467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637480961104213983426311 956221441656320975139467)
            ·
              refine ⟨1434332162484481462709201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956221441656320975139467 1434332162484481462709201)
              ·
                refine ⟨1075749121863361097031901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434332162484481462709201 1075749121863361097031901)
                ·
                  refine ⟨403405920698760411386963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075749121863361097031901 403405920698760411386963)
                  ·
                    refine ⟨605108881048140617080445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 403405920698760411386963 605108881048140617080445)
                    ·
                      refine ⟨226915830393052731405167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 605108881048140617080445 226915830393052731405167)
                      ·
                        rfl

theorem cell23_441917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_441917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441917 prefixEnd_441917 := by exact prefixLift 441917
  have htrace : WordTrace (prefixWord ++ tailWord_441917) baseStart_441917 baseEnd_441917 := by
    simpa [prefixWord, tailWord_441917, baseEnd_441917] using wordTrace_append hprefix tailTrace_441917
  have hstable : (prefixWord ++ tailWord_441917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441917).length < 2 ^ (prefixWord ++ tailWord_441917).sum := by decide
  have hdescent : baseEnd_441917 < baseStart_441917 := by decide
  rcases family_descends (prefixWord ++ tailWord_441917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441940 : List Nat := [2, 4, 1, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_441940 : Nat := 118140960795 + 441940 * 2 ^ 59
def prefixEnd_441940 : Nat := 4983230072969 + 3 ^ 40 * 441940 * 2
def baseEnd_441940 : Nat := 226927640448106141417561

theorem tailTrace_441940 : CollatzResearch.WordTrace tailWord_441940 prefixEnd_441940 226927640448106141417561 := by
  unfold tailWord_441940
  simp only [CollatzResearch.WordTrace]
  refine ⟨8059438009467166094025637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10745917345956221458700849 8059438009467166094025637)
  ·
    refine ⟨1511144626775093642629807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8059438009467166094025637 1511144626775093642629807)
    ·
      refine ⟨2266716940162640463944711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1511144626775093642629807 2266716940162640463944711)
      ·
        refine ⟨3400075410243960695917067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2266716940162640463944711 3400075410243960695917067)
        ·
          refine ⟨5100113115365941043875601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3400075410243960695917067 5100113115365941043875601)
          ·
            refine ⟨3825084836524455782906701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5100113115365941043875601 3825084836524455782906701)
            ·
              refine ⟨1434406813696670918590013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3825084836524455782906701 1434406813696670918590013)
              ·
                refine ⟨537902555136251594471255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1434406813696670918590013 537902555136251594471255)
                ·
                  refine ⟨806853832704377391706883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537902555136251594471255 806853832704377391706883)
                  ·
                    refine ⟨1210280749056566087560325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 806853832704377391706883 1210280749056566087560325)
                    ·
                      refine ⟨226927640448106141417561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1210280749056566087560325 226927640448106141417561)
                      ·
                        rfl

theorem cell23_441940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_441940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441940 prefixEnd_441940 := by exact prefixLift 441940
  have htrace : WordTrace (prefixWord ++ tailWord_441940) baseStart_441940 baseEnd_441940 := by
    simpa [prefixWord, tailWord_441940, baseEnd_441940] using wordTrace_append hprefix tailTrace_441940
  have hstable : (prefixWord ++ tailWord_441940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441940).length < 2 ^ (prefixWord ++ tailWord_441940).sum := by decide
  have hdescent : baseEnd_441940 < baseStart_441940 := by decide
  rcases family_descends (prefixWord ++ tailWord_441940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441957 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 3, 2, 2]
def baseStart_441957 : Nat := 118140960795 + 441957 * 2 ^ 59
def prefixEnd_441957 : Nat := 4983230072969 + 3 ^ 40 * 441957 * 2
def baseEnd_441957 : Nat := 226936369619232574904983

theorem tailTrace_441957 : CollatzResearch.WordTrace tailWord_441957 prefixEnd_441957 226936369619232574904983 := by
  unfold tailWord_441957
  simp only [CollatzResearch.WordTrace]
  refine ⟨16119496059872744091420125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10746330706581829394280083 16119496059872744091420125)
  ·
    refine ⟨6044811022452279034282547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16119496059872744091420125 6044811022452279034282547)
    ·
      refine ⟨9067216533678418551423821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6044811022452279034282547 9067216533678418551423821)
      ·
        refine ⟨3400206200129406956783933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9067216533678418551423821 3400206200129406956783933)
        ·
          refine ⟨1275077325048527608793975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3400206200129406956783933 1275077325048527608793975)
          ·
            refine ⟨1912615987572791413190963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275077325048527608793975 1912615987572791413190963)
            ·
              refine ⟨2868923981359187119786445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912615987572791413190963 2868923981359187119786445)
              ·
                refine ⟨1075846493009695169919917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2868923981359187119786445 1075846493009695169919917)
                ·
                  refine ⟨403442434878635688719969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075846493009695169919917 403442434878635688719969)
                  ·
                    refine ⟨302581826158976766539977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 403442434878635688719969 302581826158976766539977)
                    ·
                      refine ⟨226936369619232574904983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 302581826158976766539977 226936369619232574904983)
                      ·
                        rfl

theorem cell23_441957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_441957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441957 prefixEnd_441957 := by exact prefixLift 441957
  have htrace : WordTrace (prefixWord ++ tailWord_441957) baseStart_441957 baseEnd_441957 := by
    simpa [prefixWord, tailWord_441957, baseEnd_441957] using wordTrace_append hprefix tailTrace_441957
  have hstable : (prefixWord ++ tailWord_441957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441957).length < 2 ^ (prefixWord ++ tailWord_441957).sum := by decide
  have hdescent : baseEnd_441957 < baseStart_441957 := by decide
  rcases family_descends (prefixWord ++ tailWord_441957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441960 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_441960 : Nat := 118140960795 + 441960 * 2 ^ 59
def prefixEnd_441960 : Nat := 4983230072969 + 3 ^ 40 * 441960 * 2
def baseEnd_441960 : Nat := 226937910061196063167469

theorem tailTrace_441960 : CollatzResearch.WordTrace tailWord_441960 prefixEnd_441960 226937910061196063167469 := by
  unfold tailWord_441960
  simp only [CollatzResearch.WordTrace]
  refine ⟨8059802739430937801889667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10746403652574583735852889 8059802739430937801889667)
  ·
    refine ⟨12089704109146406702834501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8059802739430937801889667 12089704109146406702834501)
    ·
      refine ⟨2266819520464951256781469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12089704109146406702834501 2266819520464951256781469)
      ·
        refine ⟨850057320174356721293051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2266819520464951256781469 850057320174356721293051)
        ·
          refine ⟨1275085980261535081939577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850057320174356721293051 1275085980261535081939577)
          ·
            refine ⟨956314485196151311454683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1275085980261535081939577 956314485196151311454683)
            ·
              refine ⟨1434471727794226967182025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956314485196151311454683 1434471727794226967182025)
              ·
                refine ⟨1075853795845670225386519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434471727794226967182025 1075853795845670225386519)
                ·
                  refine ⟨1613780693768505338079779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075853795845670225386519 1613780693768505338079779)
                  ·
                    refine ⟨2420671040652758007119669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1613780693768505338079779 2420671040652758007119669)
                    ·
                      refine ⟨226937910061196063167469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2420671040652758007119669 226937910061196063167469)
                      ·
                        rfl

theorem cell23_441960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_441960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441960 prefixEnd_441960 := by exact prefixLift 441960
  have htrace : WordTrace (prefixWord ++ tailWord_441960) baseStart_441960 baseEnd_441960 := by
    simpa [prefixWord, tailWord_441960, baseEnd_441960] using wordTrace_append hprefix tailTrace_441960
  have hstable : (prefixWord ++ tailWord_441960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441960).length < 2 ^ (prefixWord ++ tailWord_441960).sum := by decide
  have hdescent : baseEnd_441960 < baseStart_441960 := by decide
  rcases family_descends (prefixWord ++ tailWord_441960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441970 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_441970 : Nat := 118140960795 + 441970 * 2 ^ 59
def prefixEnd_441970 : Nat := 4983230072969 + 3 ^ 40 * 441970 * 2
def baseEnd_441970 : Nat := 226943044867741024042423

theorem tailTrace_441970 : CollatzResearch.WordTrace tailWord_441970 prefixEnd_441970 226943044867741024042423 := by
  unfold tailWord_441970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4029992552206411827910841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10746646805883764874428909 4029992552206411827910841)
  ·
    refine ⟨3022494414154808870933131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4029992552206411827910841 3022494414154808870933131)
    ·
      refine ⟨4533741621232213306399697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3022494414154808870933131 4533741621232213306399697)
      ·
        refine ⟨3400306215924159979799773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4533741621232213306399697 3400306215924159979799773)
        ·
          refine ⟨1275114830971559992424915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3400306215924159979799773 1275114830971559992424915)
          ·
            refine ⟨1912672246457339988637373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275114830971559992424915 1912672246457339988637373)
            ·
              refine ⟨717252092421502495739015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1912672246457339988637373 717252092421502495739015)
              ·
                refine ⟨1075878138632253743608523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717252092421502495739015 1075878138632253743608523)
                ·
                  refine ⟨1613817207948380615412785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075878138632253743608523 1613817207948380615412785)
                  ·
                    refine ⟨1210362905961285461559589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1613817207948380615412785 1210362905961285461559589)
                    ·
                      refine ⟨226943044867741024042423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1210362905961285461559589 226943044867741024042423)
                      ·
                        rfl

theorem cell23_441970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_441970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441970 prefixEnd_441970 := by exact prefixLift 441970
  have htrace : WordTrace (prefixWord ++ tailWord_441970) baseStart_441970 baseEnd_441970 := by
    simpa [prefixWord, tailWord_441970, baseEnd_441970] using wordTrace_append hprefix tailTrace_441970
  have hstable : (prefixWord ++ tailWord_441970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441970).length < 2 ^ (prefixWord ++ tailWord_441970).sum := by decide
  have hdescent : baseEnd_441970 < baseStart_441970 := by decide
  rcases family_descends (prefixWord ++ tailWord_441970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441974 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_441974 : Nat := 118140960795 + 441974 * 2 ^ 59
def prefixEnd_441974 : Nat := 4983230072969 + 3 ^ 40 * 441974 * 2
def baseEnd_441974 : Nat := 226945098790359008392405

theorem tailTrace_441974 : CollatzResearch.WordTrace tailWord_441974 prefixEnd_441974 226945098790359008392405 := by
  unfold tailWord_441974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1007507256300697249674311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10746744067207437329859317 1007507256300697249674311)
  ·
    refine ⟨1511260884451045874511467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1007507256300697249674311 1511260884451045874511467)
    ·
      refine ⟨2266891326676568811767201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1511260884451045874511467 2266891326676568811767201)
      ·
        refine ⟨1700168495007426608825401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2266891326676568811767201 1700168495007426608825401)
        ·
          refine ⟨1275126371255569956619051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1700168495007426608825401 1275126371255569956619051)
          ·
            refine ⟨1912689556883354934928577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275126371255569956619051 1912689556883354934928577)
            ·
              refine ⟨1434517167662516201196433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1912689556883354934928577 1434517167662516201196433)
              ·
                refine ⟨1075887875746887150897325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434517167662516201196433 1075887875746887150897325)
                ·
                  refine ⟨403457953405082681586497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075887875746887150897325 403457953405082681586497)
                  ·
                    refine ⟨302593465053812011189873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 403457953405082681586497 302593465053812011189873)
                    ·
                      refine ⟨226945098790359008392405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 302593465053812011189873 226945098790359008392405)
                      ·
                        rfl

theorem cell23_441974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_441974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441974 prefixEnd_441974 := by exact prefixLift 441974
  have htrace : WordTrace (prefixWord ++ tailWord_441974) baseStart_441974 baseEnd_441974 := by
    simpa [prefixWord, tailWord_441974, baseEnd_441974] using wordTrace_append hprefix tailTrace_441974
  have hstable : (prefixWord ++ tailWord_441974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441974).length < 2 ^ (prefixWord ++ tailWord_441974).sum := by decide
  have hdescent : baseEnd_441974 < baseStart_441974 := by decide
  rcases family_descends (prefixWord ++ tailWord_441974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441991 : List Nat := [1, 1, 4, 2, 1, 5, 1, 3, 1, 2, 2]
def baseStart_441991 : Nat := 118140960795 + 441991 * 2 ^ 59
def prefixEnd_441991 : Nat := 4983230072969 + 3 ^ 40 * 441991 * 2
def baseEnd_441991 : Nat := 226953827961485441879827

theorem tailTrace_441991 : CollatzResearch.WordTrace tailWord_441991 prefixEnd_441991 226953827961485441879827 := by
  unfold tailWord_441991
  simp only [CollatzResearch.WordTrace]
  refine ⟨16120736141749567898157827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10747157427833045265438551 16120736141749567898157827)
  ·
    refine ⟨24181104212624351847236741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16120736141749567898157827 24181104212624351847236741)
    ·
      refine ⟨4533957039867065971356889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24181104212624351847236741 4533957039867065971356889)
      ·
        refine ⟨3400467779900299478517667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4533957039867065971356889 3400467779900299478517667)
        ·
          refine ⟨5100701669850449217776501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3400467779900299478517667 5100701669850449217776501)
          ·
            refine ⟨478190781548479614166547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5100701669850449217776501 478190781548479614166547)
            ·
              refine ⟨717286172322719421249821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478190781548479614166547 717286172322719421249821)
              ·
                refine ⟨268982314621019782968683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 717286172322719421249821 268982314621019782968683)
                ·
                  refine ⟨403473471931529674453025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268982314621019782968683 403473471931529674453025)
                  ·
                    refine ⟨302605103948647255839769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 403473471931529674453025 302605103948647255839769)
                    ·
                      refine ⟨226953827961485441879827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 302605103948647255839769 226953827961485441879827)
                      ·
                        rfl

theorem cell23_441991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_441991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_441991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_441991 prefixEnd_441991 := by exact prefixLift 441991
  have htrace : WordTrace (prefixWord ++ tailWord_441991) baseStart_441991 baseEnd_441991 := by
    simpa [prefixWord, tailWord_441991, baseEnd_441991] using wordTrace_append hprefix tailTrace_441991
  have hstable : (prefixWord ++ tailWord_441991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441991).length < 2 ^ (prefixWord ++ tailWord_441991).sum := by decide
  have hdescent : baseEnd_441991 < baseStart_441991 := by decide
  rcases family_descends (prefixWord ++ tailWord_441991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442013 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_442013 : Nat := 118140960795 + 442013 * 2 ^ 59
def prefixEnd_442013 : Nat := 4983230072969 + 3 ^ 40 * 442013 * 2
def baseEnd_442013 : Nat := 226965124535884355804725

theorem tailTrace_442013 : CollatzResearch.WordTrace tailWord_442013 prefixEnd_442013 226965124535884355804725 := by
  unfold tailWord_442013
  simp only [CollatzResearch.WordTrace]
  refine ⟨16121538547669865655458693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10747692365113243770305795 16121538547669865655458693)
  ·
    refine ⟨3022788477688099810398505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16121538547669865655458693 3022788477688099810398505)
    ·
      refine ⟨2267091358266074857798879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3022788477688099810398505 2267091358266074857798879)
      ·
        refine ⟨3400637037399112286698319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2267091358266074857798879 3400637037399112286698319)
        ·
          refine ⟨5100955556098668430047479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3400637037399112286698319 5100955556098668430047479)
          ·
            refine ⟨7651433334148002645071219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5100955556098668430047479 7651433334148002645071219)
            ·
              refine ⟨11477150001222003967606829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7651433334148002645071219 11477150001222003967606829)
              ·
                refine ⟨4303931250458251487852561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11477150001222003967606829 4303931250458251487852561)
                ·
                  refine ⟨3227948437843688615889421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4303931250458251487852561 3227948437843688615889421)
                  ·
                    refine ⟨1210480664191383230958533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227948437843688615889421 1210480664191383230958533)
                    ·
                      refine ⟨226965124535884355804725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1210480664191383230958533 226965124535884355804725)
                      ·
                        rfl

theorem cell23_442013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_442013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442013 prefixEnd_442013 := by exact prefixLift 442013
  have htrace : WordTrace (prefixWord ++ tailWord_442013) baseStart_442013 baseEnd_442013 := by
    simpa [prefixWord, tailWord_442013, baseEnd_442013] using wordTrace_append hprefix tailTrace_442013
  have hstable : (prefixWord ++ tailWord_442013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442013).length < 2 ^ (prefixWord ++ tailWord_442013).sum := by decide
  have hdescent : baseEnd_442013 < baseStart_442013 := by decide
  rcases family_descends (prefixWord ++ tailWord_442013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442018 : List Nat := [3, 3, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_442018 : Nat := 118140960795 + 442018 * 2 ^ 59
def prefixEnd_442018 : Nat := 4983230072969 + 3 ^ 40 * 442018 * 2
def baseEnd_442018 : Nat := 75655897313052278747401

theorem tailTrace_442018 : CollatzResearch.WordTrace tailWord_442018 prefixEnd_442018 75655897313052278747401 := by
  unfold tailWord_442018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030430228162937877347677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10747813941767834339593805 4030430228162937877347677)
  ·
    refine ⟨1511411335561101704005379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4030430228162937877347677 1511411335561101704005379)
    ·
      refine ⟨2267117003341652556008069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1511411335561101704005379 2267117003341652556008069)
      ·
        refine ⟨425084438126559854251513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2267117003341652556008069 425084438126559854251513)
        ·
          refine ⟨318813328594919890688635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425084438126559854251513 318813328594919890688635)
          ·
            refine ⟨478219992892379836032953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318813328594919890688635 478219992892379836032953)
            ·
              refine ⟨358664994669284877024715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478219992892379836032953 358664994669284877024715)
              ·
                refine ⟨537997492003927315537073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358664994669284877024715 537997492003927315537073)
                ·
                  refine ⟨403498119002945486652805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537997492003927315537073 403498119002945486652805)
                  ·
                    refine ⟨75655897313052278747401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 403498119002945486652805 75655897313052278747401)
                    ·
                      rfl

theorem cell23_442018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_442018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442018 prefixEnd_442018 := by exact prefixLift 442018
  have htrace : WordTrace (prefixWord ++ tailWord_442018) baseStart_442018 baseEnd_442018 := by
    simpa [prefixWord, tailWord_442018, baseEnd_442018] using wordTrace_append hprefix tailTrace_442018
  have hstable : (prefixWord ++ tailWord_442018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442018).length < 2 ^ (prefixWord ++ tailWord_442018).sum := by decide
  have hdescent : baseEnd_442018 < baseStart_442018 := by decide
  rcases family_descends (prefixWord ++ tailWord_442018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442063 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 3]
def baseStart_442063 : Nat := 118140960795 + 442063 * 2 ^ 59
def prefixEnd_442063 : Nat := 4983230072969 + 3 ^ 40 * 442063 * 2
def baseEnd_442063 : Nat := 226990798568609160179495

theorem tailTrace_442063 : CollatzResearch.WordTrace tailWord_442063 prefixEnd_442063 226990798568609160179495 := by
  unfold tailWord_442063
  simp only [CollatzResearch.WordTrace]
  refine ⟨16123362197488724194778843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10748908131659149463185895 16123362197488724194778843)
  ·
    refine ⟨24185043296233086292168265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16123362197488724194778843 24185043296233086292168265)
    ·
      refine ⟨18138782472174814719126199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24185043296233086292168265 18138782472174814719126199)
      ·
        refine ⟨27208173708262222078689299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18138782472174814719126199 27208173708262222078689299)
        ·
          refine ⟨40812260562393333118033949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27208173708262222078689299 40812260562393333118033949)
          ·
            refine ⟨15304597710897499919262731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40812260562393333118033949 15304597710897499919262731)
            ·
              refine ⟨22956896566346249878894097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15304597710897499919262731 22956896566346249878894097)
              ·
                refine ⟨17217672424759687409170573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22956896566346249878894097 17217672424759687409170573)
                ·
                  refine ⟨6456627159284882778438965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17217672424759687409170573 6456627159284882778438965)
                  ·
                    refine ⟨605308796182957760478653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6456627159284882778438965 605308796182957760478653)
                    ·
                      refine ⟨226990798568609160179495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 605308796182957760478653 226990798568609160179495)
                      ·
                        rfl

theorem cell23_442063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 3].length) (baseStart_442063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442063 prefixEnd_442063 := by exact prefixLift 442063
  have htrace : WordTrace (prefixWord ++ tailWord_442063) baseStart_442063 baseEnd_442063 := by
    simpa [prefixWord, tailWord_442063, baseEnd_442063] using wordTrace_append hprefix tailTrace_442063
  have hstable : (prefixWord ++ tailWord_442063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442063).length < 2 ^ (prefixWord ++ tailWord_442063).sum := by decide
  have hdescent : baseEnd_442063 < baseStart_442063 := by decide
  rcases family_descends (prefixWord ++ tailWord_442063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442087 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 7]
def baseStart_442087 : Nat := 118140960795 + 442087 * 2 ^ 59
def prefixEnd_442087 : Nat := 4983230072969 + 3 ^ 40 * 442087 * 2
def baseEnd_442087 : Nat := 25222569122701896253265

theorem tailTrace_442087 : CollatzResearch.WordTrace tailWord_442087 prefixEnd_442087 25222569122701896253265 := by
  unfold tailWord_442087
  simp only [CollatzResearch.WordTrace]
  refine ⟨16124237549401776293652515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10749491699601184195768343 16124237549401776293652515)
  ·
    refine ⟨24186356324102664440478773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16124237549401776293652515 24186356324102664440478773)
    ·
      refine ⟨2267470905384624791294885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24186356324102664440478773 2267470905384624791294885)
      ·
        refine ⟨425150794759617148367791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2267470905384624791294885 425150794759617148367791)
        ·
          refine ⟨637726192139425722551687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425150794759617148367791 637726192139425722551687)
          ·
            refine ⟨956589288209138583827531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637726192139425722551687 956589288209138583827531)
            ·
              refine ⟨1434883932313707875741297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956589288209138583827531 1434883932313707875741297)
              ·
                refine ⟨1076162949235280906805973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434883932313707875741297 1076162949235280906805973)
                ·
                  refine ⟨25222569122701896253265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1076162949235280906805973 25222569122701896253265)
                  ·
                    rfl

theorem cell23_442087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 7].length) (baseStart_442087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442087 prefixEnd_442087 := by exact prefixLift 442087
  have htrace : WordTrace (prefixWord ++ tailWord_442087) baseStart_442087 baseEnd_442087 := by
    simpa [prefixWord, tailWord_442087, baseEnd_442087] using wordTrace_append hprefix tailTrace_442087
  have hstable : (prefixWord ++ tailWord_442087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442087).length < 2 ^ (prefixWord ++ tailWord_442087).sum := by decide
  have hdescent : baseEnd_442087 < baseStart_442087 := by decide
  rcases family_descends (prefixWord ++ tailWord_442087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442120 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_442120 : Nat := 118140960795 + 442120 * 2 ^ 59
def prefixEnd_442120 : Nat := 4983230072969 + 3 ^ 40 * 442120 * 2
def baseEnd_442120 : Nat := 227020066965915437166733

theorem tailTrace_442120 : CollatzResearch.WordTrace tailWord_442120 prefixEnd_442120 227020066965915437166733 := by
  unfold tailWord_442120
  simp only [CollatzResearch.WordTrace]
  refine ⟨8062720579141111464801907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10750294105521481953069209 8062720579141111464801907)
  ·
    refine ⟨12094080868711667197202861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8062720579141111464801907 12094080868711667197202861)
    ·
      refine ⟨4535280325766875198951073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12094080868711667197202861 4535280325766875198951073)
      ·
        refine ⟨3401460244325156399213305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4535280325766875198951073 3401460244325156399213305)
        ·
          refine ⟨2551095183243867299409979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3401460244325156399213305 2551095183243867299409979)
          ·
            refine ⟨3826642774865800949114969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551095183243867299409979 3826642774865800949114969)
            ·
              refine ⟨2869982081149350711836227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3826642774865800949114969 2869982081149350711836227)
              ·
                refine ⟨4304973121724026067754341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869982081149350711836227 4304973121724026067754341)
                ·
                  refine ⟨807182460323254887703939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4304973121724026067754341 807182460323254887703939)
                  ·
                    refine ⟨1210773690484882331555909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 807182460323254887703939 1210773690484882331555909)
                    ·
                      refine ⟨227020066965915437166733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1210773690484882331555909 227020066965915437166733)
                      ·
                        rfl

theorem cell23_442120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_442120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442120 prefixEnd_442120 := by exact prefixLift 442120
  have htrace : WordTrace (prefixWord ++ tailWord_442120) baseStart_442120 baseEnd_442120 := by
    simpa [prefixWord, tailWord_442120, baseEnd_442120] using wordTrace_append hprefix tailTrace_442120
  have hstable : (prefixWord ++ tailWord_442120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442120).length < 2 ^ (prefixWord ++ tailWord_442120).sum := by decide
  have hdescent : baseEnd_442120 < baseStart_442120 := by decide
  rcases family_descends (prefixWord ++ tailWord_442120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442123 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 5]
def baseStart_442123 : Nat := 118140960795 + 442123 * 2 ^ 59
def prefixEnd_442123 : Nat := 4983230072969 + 3 ^ 40 * 442123 * 2
def baseEnd_442123 : Nat := 227021607407878925429219

theorem tailTrace_442123 : CollatzResearch.WordTrace tailWord_442123 prefixEnd_442123 227021607407878925429219 := by
  unfold tailWord_442123
  simp only [CollatzResearch.WordTrace]
  refine ⟨16125550577271354441963023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10750367051514236294642015 16125550577271354441963023)
  ·
    refine ⟨24188325865907031662944535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16125550577271354441963023 24188325865907031662944535)
    ·
      refine ⟨36282488798860547494416803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24188325865907031662944535 36282488798860547494416803)
      ·
        refine ⟨54423733198290821241625205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36282488798860547494416803 54423733198290821241625205)
        ·
          refine ⟨5102224987339764491402363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54423733198290821241625205 5102224987339764491402363)
          ·
            refine ⟨7653337481009646737103545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5102224987339764491402363 7653337481009646737103545)
            ·
              refine ⟨5740003110757235052827659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7653337481009646737103545 5740003110757235052827659)
              ·
                refine ⟨8610004666135852579241489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5740003110757235052827659 8610004666135852579241489)
                ·
                  refine ⟨6457503499601889434431117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8610004666135852579241489 6457503499601889434431117)
                  ·
                    refine ⟨2421563812350708537911669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6457503499601889434431117 2421563812350708537911669)
                    ·
                      refine ⟨227021607407878925429219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2421563812350708537911669 227021607407878925429219)
                      ·
                        rfl

theorem cell23_442123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 5].length) (baseStart_442123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442123 prefixEnd_442123 := by exact prefixLift 442123
  have htrace : WordTrace (prefixWord ++ tailWord_442123) baseStart_442123 baseEnd_442123 := by
    simpa [prefixWord, tailWord_442123, baseEnd_442123] using wordTrace_append hprefix tailTrace_442123
  have hstable : (prefixWord ++ tailWord_442123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442123).length < 2 ^ (prefixWord ++ tailWord_442123).sum := by decide
  have hdescent : baseEnd_442123 < baseStart_442123 := by decide
  rcases family_descends (prefixWord ++ tailWord_442123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442132 : List Nat := [2, 4, 4, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_442132 : Nat := 118140960795 + 442132 * 2 ^ 59
def prefixEnd_442132 : Nat := 4983230072969 + 3 ^ 40 * 442132 * 2
def baseEnd_442132 : Nat := 227026228733769390216679

theorem tailTrace_442132 : CollatzResearch.WordTrace tailWord_442132 prefixEnd_442132 227026228733769390216679 := by
  unfold tailWord_442132
  simp only [CollatzResearch.WordTrace]
  refine ⟨8062939417119374489520325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10750585889492499319360433 8062939417119374489520325)
  ·
    refine ⟨1511801140709882716785061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8062939417119374489520325 1511801140709882716785061)
    ·
      refine ⟨283462713883103009397199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1511801140709882716785061 283462713883103009397199)
      ·
        refine ⟨425194070824654514095799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283462713883103009397199 425194070824654514095799)
        ·
          refine ⟨637791106236981771143699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425194070824654514095799 637791106236981771143699)
          ·
            refine ⟨956686659355472656715549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637791106236981771143699 956686659355472656715549)
            ·
              refine ⟨358757497258302246268331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 956686659355472656715549 358757497258302246268331)
              ·
                refine ⟨538136245887453369402497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358757497258302246268331 538136245887453369402497)
                ·
                  refine ⟨403602184415590027051873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538136245887453369402497 403602184415590027051873)
                  ·
                    refine ⟨302701638311692520288905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 403602184415590027051873 302701638311692520288905)
                    ·
                      refine ⟨227026228733769390216679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 302701638311692520288905 227026228733769390216679)
                      ·
                        rfl

theorem cell23_442132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_442132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442132 prefixEnd_442132 := by exact prefixLift 442132
  have htrace : WordTrace (prefixWord ++ tailWord_442132) baseStart_442132 baseEnd_442132 := by
    simpa [prefixWord, tailWord_442132, baseEnd_442132] using wordTrace_append hprefix tailTrace_442132
  have hstable : (prefixWord ++ tailWord_442132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442132).length < 2 ^ (prefixWord ++ tailWord_442132).sum := by decide
  have hdescent : baseEnd_442132 < baseStart_442132 := by decide
  rcases family_descends (prefixWord ++ tailWord_442132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442140 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_442140 : Nat := 118140960795 + 442140 * 2 ^ 59
def prefixEnd_442140 : Nat := 4983230072969 + 3 ^ 40 * 442140 * 2
def baseEnd_442140 : Nat := 227030336579005358916641

theorem tailTrace_442140 : CollatzResearch.WordTrace tailWord_442140 prefixEnd_442140 227030336579005358916641 := by
  unfold tailWord_442140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8063085309104883172665937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10750780412139844230221249 8063085309104883172665937)
  ·
    refine ⟨6047313981828662379499453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8063085309104883172665937 6047313981828662379499453)
    ·
      refine ⟨2267742743185748392312295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6047313981828662379499453 2267742743185748392312295)
      ·
        refine ⟨3401614114778622588468443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2267742743185748392312295 3401614114778622588468443)
        ·
          refine ⟨5102421172167933882702665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3401614114778622588468443 5102421172167933882702665)
          ·
            refine ⟨3826815879125950412026999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5102421172167933882702665 3826815879125950412026999)
            ·
              refine ⟨5740223818688925618040499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3826815879125950412026999 5740223818688925618040499)
              ·
                refine ⟨8610335728033388427060749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5740223818688925618040499 8610335728033388427060749)
                ·
                  refine ⟨3228875898012520660147781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8610335728033388427060749 3228875898012520660147781)
                  ·
                    refine ⟨605414230877347623777709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3228875898012520660147781 605414230877347623777709)
                    ·
                      refine ⟨227030336579005358916641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 605414230877347623777709 227030336579005358916641)
                      ·
                        rfl

theorem cell23_442140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_442140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442140 prefixEnd_442140 := by exact prefixLift 442140
  have htrace : WordTrace (prefixWord ++ tailWord_442140) baseStart_442140 baseEnd_442140 := by
    simpa [prefixWord, tailWord_442140, baseEnd_442140] using wordTrace_append hprefix tailTrace_442140
  have hstable : (prefixWord ++ tailWord_442140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442140).length < 2 ^ (prefixWord ++ tailWord_442140).sum := by decide
  have hdescent : baseEnd_442140 < baseStart_442140 := by decide
  rcases family_descends (prefixWord ++ tailWord_442140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442174 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_442174 : Nat := 118140960795 + 442174 * 2 ^ 59
def prefixEnd_442174 : Nat := 4983230072969 + 3 ^ 40 * 442174 * 2
def baseEnd_442174 : Nat := 227047794921258225891485

theorem tailTrace_442174 : CollatzResearch.WordTrace tailWord_442174 prefixEnd_442174 227047794921258225891485 := by
  unfold tailWord_442174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015926337510823769008697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10751607133391060101379717 2015926337510823769008697)
  ·
    refine ⟨1511944753133117826756523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2015926337510823769008697 1511944753133117826756523)
    ·
      refine ⟨2267917129699676740134785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1511944753133117826756523 2267917129699676740134785)
      ·
        refine ⟨1700937847274757555101089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2267917129699676740134785 1700937847274757555101089)
        ·
          refine ⟨1275703385456068166325817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1700937847274757555101089 1275703385456068166325817)
          ·
            refine ⟨956777539092051124744363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1275703385456068166325817 956777539092051124744363)
            ·
              refine ⟨1435166308638076687116545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956777539092051124744363 1435166308638076687116545)
              ·
                refine ⟨1076374731478557515337409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1435166308638076687116545 1076374731478557515337409)
                ·
                  refine ⟨807281048608918136503057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1076374731478557515337409 807281048608918136503057)
                  ·
                    refine ⟨605460786456688602377293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 807281048608918136503057 605460786456688602377293)
                    ·
                      refine ⟨227047794921258225891485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 605460786456688602377293 227047794921258225891485)
                      ·
                        rfl

theorem cell23_442174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_442174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442174 prefixEnd_442174 := by exact prefixLift 442174
  have htrace : WordTrace (prefixWord ++ tailWord_442174) baseStart_442174 baseEnd_442174 := by
    simpa [prefixWord, tailWord_442174, baseEnd_442174] using wordTrace_append hprefix tailTrace_442174
  have hstable : (prefixWord ++ tailWord_442174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442174).length < 2 ^ (prefixWord ++ tailWord_442174).sum := by decide
  have hdescent : baseEnd_442174 < baseStart_442174 := by decide
  rcases family_descends (prefixWord ++ tailWord_442174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442194 : List Nat := [3, 2, 2, 1, 1, 5, 2, 1, 6]
def baseStart_442194 : Nat := 118140960795 + 442194 * 2 ^ 59
def prefixEnd_442194 : Nat := 4983230072969 + 3 ^ 40 * 442194 * 2
def baseEnd_442194 : Nat := 25228673837149794182377

theorem tailTrace_442194 : CollatzResearch.WordTrace tailWord_442194 prefixEnd_442194 25228673837149794182377 := by
  unfold tailWord_442194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4032035040003533391949409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10752093440009422378531757 4032035040003533391949409)
  ·
    refine ⟨3024026280002650043962057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4032035040003533391949409 3024026280002650043962057)
    ·
      refine ⟨2268019710001987532971543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3024026280002650043962057 2268019710001987532971543)
      ·
        refine ⟨3402029565002981299457315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2268019710001987532971543 3402029565002981299457315)
        ·
          refine ⟨5103044347504471949185973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3402029565002981299457315 5103044347504471949185973)
          ·
            refine ⟨478410407578544245236185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5103044347504471949185973 478410407578544245236185)
            ·
              refine ⟨358807805683908183927139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478410407578544245236185 358807805683908183927139)
              ·
                refine ⟨538211708525862275890709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358807805683908183927139 538211708525862275890709)
                ·
                  refine ⟨25228673837149794182377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 538211708525862275890709 25228673837149794182377)
                  ·
                    rfl

theorem cell23_442194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_442194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442194 prefixEnd_442194 := by exact prefixLift 442194
  have htrace : WordTrace (prefixWord ++ tailWord_442194) baseStart_442194 baseEnd_442194 := by
    simpa [prefixWord, tailWord_442194, baseEnd_442194] using wordTrace_append hprefix tailTrace_442194
  have hstable : (prefixWord ++ tailWord_442194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442194).length < 2 ^ (prefixWord ++ tailWord_442194).sum := by decide
  have hdescent : baseEnd_442194 < baseStart_442194 := by decide
  rcases family_descends (prefixWord ++ tailWord_442194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442203 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 3, 12]
def baseStart_442203 : Nat := 118140960795 + 442203 * 2 ^ 59
def prefixEnd_442203 : Nat := 4983230072969 + 3 ^ 40 * 442203 * 2
def baseEnd_442203 : Nat := 75687561953412870809617

theorem tailTrace_442203 : CollatzResearch.WordTrace tailWord_442203 prefixEnd_442203 75687561953412870809617 := by
  unfold tailWord_442203
  simp only [CollatzResearch.WordTrace]
  refine ⟨16128468416981528104875263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10752312277987685403250175 16128468416981528104875263)
  ·
    refine ⟨24192702625472292157312895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16128468416981528104875263 24192702625472292157312895)
    ·
      refine ⟨36289053938208438235969343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24192702625472292157312895 36289053938208438235969343)
      ·
        refine ⟨54433580907312657353954015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36289053938208438235969343 54433580907312657353954015)
        ·
          refine ⟨81650371360968986030931023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54433580907312657353954015 81650371360968986030931023)
          ·
            refine ⟨122475557041453479046396535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81650371360968986030931023 122475557041453479046396535)
            ·
              refine ⟨183713335562180218569594803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122475557041453479046396535 183713335562180218569594803)
              ·
                refine ⟨275570003343270327854392205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183713335562180218569594803 275570003343270327854392205)
                ·
                  refine ⟨103338751253726372945397077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275570003343270327854392205 103338751253726372945397077)
                  ·
                    refine ⟨75687561953412870809617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 103338751253726372945397077 75687561953412870809617)
                    ·
                      rfl

theorem cell23_442203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 12].length) (baseStart_442203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442203 prefixEnd_442203 := by exact prefixLift 442203
  have htrace : WordTrace (prefixWord ++ tailWord_442203) baseStart_442203 baseEnd_442203 := by
    simpa [prefixWord, tailWord_442203, baseEnd_442203] using wordTrace_append hprefix tailTrace_442203
  have hstable : (prefixWord ++ tailWord_442203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442203).length < 2 ^ (prefixWord ++ tailWord_442203).sum := by decide
  have hdescent : baseEnd_442203 < baseStart_442203 := by decide
  rcases family_descends (prefixWord ++ tailWord_442203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442207 : List Nat := [1, 1, 2, 3, 1, 4, 3, 2, 1, 5]
def baseStart_442207 : Nat := 118140960795 + 442207 * 2 ^ 59
def prefixEnd_442207 : Nat := 4983230072969 + 3 ^ 40 * 442207 * 2
def baseEnd_442207 : Nat := 75688246594285532259611

theorem tailTrace_442207 : CollatzResearch.WordTrace tailWord_442207 prefixEnd_442207 75688246594285532259611 := by
  unfold tailWord_442207
  simp only [CollatzResearch.WordTrace]
  refine ⟨16128614308967036788020875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10752409539311357858680583 16128614308967036788020875)
  ·
    refine ⟨24192921463450555182031313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16128614308967036788020875 24192921463450555182031313)
    ·
      refine ⟨18144691097587916386523485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24192921463450555182031313 18144691097587916386523485)
      ·
        refine ⟨6804259161595468644946307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18144691097587916386523485 6804259161595468644946307)
        ·
          refine ⟨10206388742393202967419461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6804259161595468644946307 10206388742393202967419461)
          ·
            refine ⟨1913697889198725556391149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10206388742393202967419461 1913697889198725556391149)
            ·
              refine ⟨717636708449522083646681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1913697889198725556391149 717636708449522083646681)
              ·
                refine ⟨538227531337141562735011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717636708449522083646681 538227531337141562735011)
                ·
                  refine ⟨807341297005712344102517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538227531337141562735011 807341297005712344102517)
                  ·
                    refine ⟨75688246594285532259611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 807341297005712344102517 75688246594285532259611)
                    ·
                      rfl

theorem cell23_442207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 5].length) (baseStart_442207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442207 prefixEnd_442207 := by exact prefixLift 442207
  have htrace : WordTrace (prefixWord ++ tailWord_442207) baseStart_442207 baseEnd_442207 := by
    simpa [prefixWord, tailWord_442207, baseEnd_442207] using wordTrace_append hprefix tailTrace_442207
  have hstable : (prefixWord ++ tailWord_442207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442207).length < 2 ^ (prefixWord ++ tailWord_442207).sum := by decide
  have hdescent : baseEnd_442207 < baseStart_442207 := by decide
  rcases family_descends (prefixWord ++ tailWord_442207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442220 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 3, 6]
def baseStart_442220 : Nat := 118140960795 + 442220 * 2 ^ 59
def prefixEnd_442220 : Nat := 4983230072969 + 3 ^ 40 * 442220 * 2
def baseEnd_442220 : Nat := 75690471677121681972091

theorem tailTrace_442220 : CollatzResearch.WordTrace tailWord_442220 prefixEnd_442220 75690471677121681972091 := by
  unfold tailWord_442220
  simp only [CollatzResearch.WordTrace]
  refine ⟨8064544228959970004122057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10752725638613293338829409 8064544228959970004122057)
  ·
    refine ⟨6048408171719977503091543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8064544228959970004122057 6048408171719977503091543)
    ·
      refine ⟨9072612257579966254637315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6048408171719977503091543 9072612257579966254637315)
      ·
        refine ⟨13608918386369949381955973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9072612257579966254637315 13608918386369949381955973)
        ·
          refine ⟨2551672197444365509116745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13608918386369949381955973 2551672197444365509116745)
          ·
            refine ⟨1913754148083274131837559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2551672197444365509116745 1913754148083274131837559)
            ·
              refine ⟨2870631222124911197756339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913754148083274131837559 2870631222124911197756339)
              ·
                refine ⟨4305946833187366796634509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870631222124911197756339 4305946833187366796634509)
                ·
                  refine ⟨1614730062445262548737941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4305946833187366796634509 1614730062445262548737941)
                  ·
                    refine ⟨75690471677121681972091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1614730062445262548737941 75690471677121681972091)
                    ·
                      rfl

theorem cell23_442220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_442220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442220 prefixEnd_442220 := by exact prefixLift 442220
  have htrace : WordTrace (prefixWord ++ tailWord_442220) baseStart_442220 baseEnd_442220 := by
    simpa [prefixWord, tailWord_442220, baseEnd_442220] using wordTrace_append hprefix tailTrace_442220
  have hstable : (prefixWord ++ tailWord_442220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442220).length < 2 ^ (prefixWord ++ tailWord_442220).sum := by decide
  have hdescent : baseEnd_442220 < baseStart_442220 := by decide
  rcases family_descends (prefixWord ++ tailWord_442220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442240 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 4]
def baseStart_442240 : Nat := 118140960795 + 442240 * 2 ^ 59
def prefixEnd_442240 : Nat := 4983230072969 + 3 ^ 40 * 442240 * 2
def baseEnd_442240 : Nat := 227081684644454967666181

theorem tailTrace_442240 : CollatzResearch.WordTrace tailWord_442240 prefixEnd_442240 227081684644454967666181 := by
  unfold tailWord_442240
  simp only [CollatzResearch.WordTrace]
  refine ⟨8064908958923741711986087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10753211945231655615981449 8064908958923741711986087)
  ·
    refine ⟨12097363438385612567979131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8064908958923741711986087 12097363438385612567979131)
    ·
      refine ⟨18146045157578418851968697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12097363438385612567979131 18146045157578418851968697)
      ·
        refine ⟨13609533868183814138976523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18146045157578418851968697 13609533868183814138976523)
        ·
          refine ⟨20414300802275721208464785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13609533868183814138976523 20414300802275721208464785)
          ·
            refine ⟨15310725601706790906348589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20414300802275721208464785 15310725601706790906348589)
            ·
              refine ⟨5741522100640046589880721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15310725601706790906348589 5741522100640046589880721)
              ·
                refine ⟨4306141575480034942410541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741522100640046589880721 4306141575480034942410541)
                ·
                  refine ⟨1614803090805013103403953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4306141575480034942410541 1614803090805013103403953)
                  ·
                    refine ⟨1211102318103759827552965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1614803090805013103403953 1211102318103759827552965)
                    ·
                      refine ⟨227081684644454967666181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1211102318103759827552965 227081684644454967666181)
                      ·
                        rfl

theorem cell23_442240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_442240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442240 prefixEnd_442240 := by exact prefixLift 442240
  have htrace : WordTrace (prefixWord ++ tailWord_442240) baseStart_442240 baseEnd_442240 := by
    simpa [prefixWord, tailWord_442240, baseEnd_442240] using wordTrace_append hprefix tailTrace_442240
  have hstable : (prefixWord ++ tailWord_442240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442240).length < 2 ^ (prefixWord ++ tailWord_442240).sum := by decide
  have hdescent : baseEnd_442240 < baseStart_442240 := by decide
  rcases family_descends (prefixWord ++ tailWord_442240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442351 : List Nat := [1, 1, 2, 1, 4, 2, 2, 4, 2, 2, 2]
def baseStart_442351 : Nat := 118140960795 + 442351 * 2 ^ 59
def prefixEnd_442351 : Nat := 4983230072969 + 3 ^ 40 * 442351 * 2
def baseEnd_442351 : Nat := 227138680997104033378171

theorem tailTrace_442351 : CollatzResearch.WordTrace tailWord_442351 prefixEnd_442351 227138680997104033378171 := by
  unfold tailWord_442351
  simp only [CollatzResearch.WordTrace]
  refine ⟨16133866420445349381262907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10755910946963566254175271 16133866420445349381262907)
  ·
    refine ⟨24200799630668024071894361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16133866420445349381262907 24200799630668024071894361)
    ·
      refine ⟨18150599723001018053920771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24200799630668024071894361 18150599723001018053920771)
      ·
        refine ⟨27225899584501527080881157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18150599723001018053920771 27225899584501527080881157)
        ·
          refine ⟨5104856172094036327665217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27225899584501527080881157 5104856172094036327665217)
          ·
            refine ⟨3828642129070527245748913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5104856172094036327665217 3828642129070527245748913)
            ·
              refine ⟨2871481596802895434311685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3828642129070527245748913 2871481596802895434311685)
              ·
                refine ⟨538402799400542893933441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2871481596802895434311685 538402799400542893933441)
                ·
                  refine ⟨403802099550407170450081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538402799400542893933441 403802099550407170450081)
                  ·
                    refine ⟨302851574662805377837561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 403802099550407170450081 302851574662805377837561)
                    ·
                      refine ⟨227138680997104033378171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 302851574662805377837561 227138680997104033378171)
                      ·
                        rfl

theorem cell23_442351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 2, 2].length) (baseStart_442351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442351 prefixEnd_442351 := by exact prefixLift 442351
  have htrace : WordTrace (prefixWord ++ tailWord_442351) baseStart_442351 baseEnd_442351 := by
    simpa [prefixWord, tailWord_442351, baseEnd_442351] using wordTrace_append hprefix tailTrace_442351
  have hstable : (prefixWord ++ tailWord_442351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442351).length < 2 ^ (prefixWord ++ tailWord_442351).sum := by decide
  have hdescent : baseEnd_442351 < baseStart_442351 := by decide
  rcases family_descends (prefixWord ++ tailWord_442351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442367 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 3]
def baseStart_442367 : Nat := 118140960795 + 442367 * 2 ^ 59
def prefixEnd_442367 : Nat := 4983230072969 + 3 ^ 40 * 442367 * 2
def baseEnd_442367 : Nat := 227146896687575970778097

theorem tailTrace_442367 : CollatzResearch.WordTrace tailWord_442367 prefixEnd_442367 227146896687575970778097 := by
  unfold tailWord_442367
  simp only [CollatzResearch.WordTrace]
  refine ⟨16134449988387384113845355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10756299992258256075896903 16134449988387384113845355)
  ·
    refine ⟨24201674982581076170768033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16134449988387384113845355 24201674982581076170768033)
    ·
      refine ⟨18151256236935807128076025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24201674982581076170768033 18151256236935807128076025)
      ·
        refine ⟨13613442177701855346057019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18151256236935807128076025 13613442177701855346057019)
        ·
          refine ⟨20420163266552783019085529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13613442177701855346057019 20420163266552783019085529)
          ·
            refine ⟨15315122449914587264314147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20420163266552783019085529 15315122449914587264314147)
            ·
              refine ⟨22972683674871880896471221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15315122449914587264314147 22972683674871880896471221)
              ·
                refine ⟨2153689094519238834044177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22972683674871880896471221 2153689094519238834044177)
                ·
                  refine ⟨1615266820889429125533133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2153689094519238834044177 1615266820889429125533133)
                  ·
                    refine ⟨605725057833535922074925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1615266820889429125533133 605725057833535922074925)
                    ·
                      refine ⟨227146896687575970778097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 605725057833535922074925 227146896687575970778097)
                      ·
                        rfl

theorem cell23_442367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_442367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442367 prefixEnd_442367 := by exact prefixLift 442367
  have htrace : WordTrace (prefixWord ++ tailWord_442367) baseStart_442367 baseEnd_442367 := by
    simpa [prefixWord, tailWord_442367, baseEnd_442367] using wordTrace_append hprefix tailTrace_442367
  have hstable : (prefixWord ++ tailWord_442367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442367).length < 2 ^ (prefixWord ++ tailWord_442367).sum := by decide
  have hdescent : baseEnd_442367 < baseStart_442367 := by decide
  rcases family_descends (prefixWord ++ tailWord_442367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442372 : List Nat := [2, 3, 2, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_442372 : Nat := 118140960795 + 442372 * 2 ^ 59
def prefixEnd_442372 : Nat := 4983230072969 + 3 ^ 40 * 442372 * 2
def baseEnd_442372 : Nat := 227149464090848451215575

theorem tailTrace_442372 : CollatzResearch.WordTrace tailWord_442372 prefixEnd_442372 227149464090848451215575 := by
  unfold tailWord_442372
  simp only [CollatzResearch.WordTrace]
  refine ⟨8067316176684634983888685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10756421568912846645184913 8067316176684634983888685)
  ·
    refine ⟨3025243566256738118958257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8067316176684634983888685 3025243566256738118958257)
    ·
      refine ⟨2268932674692553589218693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3025243566256738118958257 2268932674692553589218693)
      ·
        refine ⟨425424876504853797978505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2268932674692553589218693 425424876504853797978505)
        ·
          refine ⟨319068657378640348483879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425424876504853797978505 319068657378640348483879)
          ·
            refine ⟨478602986067960522725819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319068657378640348483879 478602986067960522725819)
            ·
              refine ⟨717904479101940784088729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478602986067960522725819 717904479101940784088729)
              ·
                refine ⟨538428359326455588066547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717904479101940784088729 538428359326455588066547)
                ·
                  refine ⟨807642538989683382099821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538428359326455588066547 807642538989683382099821)
                  ·
                    refine ⟨302865952121131268287433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 807642538989683382099821 302865952121131268287433)
                    ·
                      refine ⟨227149464090848451215575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 302865952121131268287433 227149464090848451215575)
                      ·
                        rfl

theorem cell23_442372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_442372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442372 prefixEnd_442372 := by exact prefixLift 442372
  have htrace : WordTrace (prefixWord ++ tailWord_442372) baseStart_442372 baseEnd_442372 := by
    simpa [prefixWord, tailWord_442372, baseEnd_442372] using wordTrace_append hprefix tailTrace_442372
  have hstable : (prefixWord ++ tailWord_442372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442372).length < 2 ^ (prefixWord ++ tailWord_442372).sum := by decide
  have hdescent : baseEnd_442372 < baseStart_442372 := by decide
  rcases family_descends (prefixWord ++ tailWord_442372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442387 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 2, 5]
def baseStart_442387 : Nat := 118140960795 + 442387 * 2 ^ 59
def prefixEnd_442387 : Nat := 4983230072969 + 3 ^ 40 * 442387 * 2
def baseEnd_442387 : Nat := 75719055433555297509335

theorem tailTrace_442387 : CollatzResearch.WordTrace tailWord_442387 prefixEnd_442387 75719055433555297509335 := by
  unfold tailWord_442387
  simp only [CollatzResearch.WordTrace]
  refine ⟨16135179448314927529573415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10756786298876618353048943 16135179448314927529573415)
  ·
    refine ⟨24202769172472391294360123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16135179448314927529573415 24202769172472391294360123)
    ·
      refine ⟨36304153758708586941540185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24202769172472391294360123 36304153758708586941540185)
      ·
        refine ⟨27228115319031440206155139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36304153758708586941540185 27228115319031440206155139)
        ·
          refine ⟨40842172978547160309232709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27228115319031440206155139 40842172978547160309232709)
          ·
            refine ⟨7657907433477592557981133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40842172978547160309232709 7657907433477592557981133)
            ·
              refine ⟨2871715287554097209242925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7657907433477592557981133 2871715287554097209242925)
              ·
                refine ⟨1076893232832786453466097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2871715287554097209242925 1076893232832786453466097)
                ·
                  refine ⟨807669924624589840099573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1076893232832786453466097 807669924624589840099573)
                  ·
                    refine ⟨75719055433555297509335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 807669924624589840099573 75719055433555297509335)
                    ·
                      rfl

theorem cell23_442387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 5].length) (baseStart_442387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442387 prefixEnd_442387 := by exact prefixLift 442387
  have htrace : WordTrace (prefixWord ++ tailWord_442387) baseStart_442387 baseEnd_442387 := by
    simpa [prefixWord, tailWord_442387, baseEnd_442387] using wordTrace_append hprefix tailTrace_442387
  have hstable : (prefixWord ++ tailWord_442387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442387).length < 2 ^ (prefixWord ++ tailWord_442387).sum := by decide
  have hdescent : baseEnd_442387 < baseStart_442387 := by decide
  rcases family_descends (prefixWord ++ tailWord_442387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442408 : List Nat := [2, 1, 5, 3, 1, 1, 1, 4, 5]
def baseStart_442408 : Nat := 118140960795 + 442408 * 2 ^ 59
def prefixEnd_442408 : Nat := 4983230072969 + 3 ^ 40 * 442408 * 2
def baseEnd_442408 : Nat := 25240883266045590040601

theorem tailTrace_442408 : CollatzResearch.WordTrace tailWord_442408 prefixEnd_442408 25240883266045590040601 := by
  unfold tailWord_442408
  simp only [CollatzResearch.WordTrace]
  refine ⟨8067972690619424058043939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10757296920825898744058585 8067972690619424058043939)
  ·
    refine ⟨12101959035929136087065909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8067972690619424058043939 12101959035929136087065909)
    ·
      refine ⟨1134558659618356508162429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12101959035929136087065909 1134558659618356508162429)
      ·
        refine ⟨425459497356883690560911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1134558659618356508162429 425459497356883690560911)
        ·
          refine ⟨638189246035325535841367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425459497356883690560911 638189246035325535841367)
          ·
            refine ⟨957283869052988303762051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638189246035325535841367 957283869052988303762051)
            ·
              refine ⟨1435925803579482455643077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957283869052988303762051 1435925803579482455643077)
              ·
                refine ⟨269236088171152960433077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1435925803579482455643077 269236088171152960433077)
                ·
                  refine ⟨25240883266045590040601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269236088171152960433077 25240883266045590040601)
                  ·
                    rfl

theorem cell23_442408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 5].length) (baseStart_442408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442408 prefixEnd_442408 := by exact prefixLift 442408
  have htrace : WordTrace (prefixWord ++ tailWord_442408) baseStart_442408 baseEnd_442408 := by
    simpa [prefixWord, tailWord_442408, baseEnd_442408] using wordTrace_append hprefix tailTrace_442408
  have hstable : (prefixWord ++ tailWord_442408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442408).length < 2 ^ (prefixWord ++ tailWord_442408).sum := by decide
  have hdescent : baseEnd_442408 < baseStart_442408 := by decide
  rcases family_descends (prefixWord ++ tailWord_442408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442414 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_442414 : Nat := 118140960795 + 442414 * 2 ^ 59
def prefixEnd_442414 : Nat := 4983230072969 + 3 ^ 40 * 442414 * 2
def baseEnd_442414 : Nat := 227171030278337286890381

theorem tailTrace_442414 : CollatzResearch.WordTrace tailWord_442414 prefixEnd_442414 227171030278337286890381 := by
  unfold tailWord_442414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2017020527402138892600787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10757442812811407427204197 2017020527402138892600787)
  ·
    refine ⟨3025530791103208338901181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2017020527402138892600787 3025530791103208338901181)
    ·
      refine ⟨1134574046663703127087943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3025530791103208338901181 1134574046663703127087943)
      ·
        refine ⟨1701861069995554690631915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134574046663703127087943 1701861069995554690631915)
        ·
          refine ⟨2552791604993332035947873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1701861069995554690631915 2552791604993332035947873)
          ·
            refine ⟨1914593703744999026960905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2552791604993332035947873 1914593703744999026960905)
            ·
              refine ⟨1435945277808749270220679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1914593703744999026960905 1435945277808749270220679)
              ·
                refine ⟨2153917916713123905331019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435945277808749270220679 2153917916713123905331019)
                ·
                  refine ⟨3230876875069685857996529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153917916713123905331019 3230876875069685857996529)
                  ·
                    refine ⟨2423157656302264393497397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3230876875069685857996529 2423157656302264393497397)
                    ·
                      refine ⟨227171030278337286890381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2423157656302264393497397 227171030278337286890381)
                      ·
                        rfl

theorem cell23_442414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_442414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442414 prefixEnd_442414 := by exact prefixLift 442414
  have htrace : WordTrace (prefixWord ++ tailWord_442414) baseStart_442414 baseEnd_442414 := by
    simpa [prefixWord, tailWord_442414, baseEnd_442414] using wordTrace_append hprefix tailTrace_442414
  have hstable : (prefixWord ++ tailWord_442414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442414).length < 2 ^ (prefixWord ++ tailWord_442414).sum := by decide
  have hdescent : baseEnd_442414 < baseStart_442414 := by decide
  rcases family_descends (prefixWord ++ tailWord_442414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442427 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 3]
def baseStart_442427 : Nat := 118140960795 + 442427 * 2 ^ 59
def prefixEnd_442427 : Nat := 4983230072969 + 3 ^ 40 * 442427 * 2
def baseEnd_442427 : Nat := 227177705526845736027821

theorem tailTrace_442427 : CollatzResearch.WordTrace tailWord_442427 prefixEnd_442427 227177705526845736027821 := by
  unfold tailWord_442427
  simp only [CollatzResearch.WordTrace]
  refine ⟨16136638368170014361029535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10757758912113342907353023 16136638368170014361029535)
  ·
    refine ⟨24204957552255021541544303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16136638368170014361029535 24204957552255021541544303)
    ·
      refine ⟨36307436328382532312316455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24204957552255021541544303 36307436328382532312316455)
      ·
        refine ⟨54461154492573798468474683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36307436328382532312316455 54461154492573798468474683)
        ·
          refine ⟨81691731738860697702712025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54461154492573798468474683 81691731738860697702712025)
          ·
            refine ⟨61268798804145523277034019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81691731738860697702712025 61268798804145523277034019)
            ·
              refine ⟨91903198206218284915551029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61268798804145523277034019 91903198206218284915551029)
              ·
                refine ⟨8615924831832964210832909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91903198206218284915551029 8615924831832964210832909)
                ·
                  refine ⟨3230971811937361579062341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8615924831832964210832909 3230971811937361579062341)
                  ·
                    refine ⟨605807214738255296074189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3230971811937361579062341 605807214738255296074189)
                    ·
                      refine ⟨227177705526845736027821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 605807214738255296074189 227177705526845736027821)
                      ·
                        rfl

theorem cell23_442427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 3].length) (baseStart_442427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442427 prefixEnd_442427 := by exact prefixLift 442427
  have htrace : WordTrace (prefixWord ++ tailWord_442427) baseStart_442427 baseEnd_442427 := by
    simpa [prefixWord, tailWord_442427, baseEnd_442427] using wordTrace_append hprefix tailTrace_442427
  have hstable : (prefixWord ++ tailWord_442427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442427).length < 2 ^ (prefixWord ++ tailWord_442427).sum := by decide
  have hdescent : baseEnd_442427 < baseStart_442427 := by decide
  rcases family_descends (prefixWord ++ tailWord_442427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442464 : List Nat := [2, 1, 1, 3, 2, 3, 3, 2, 6]
def baseStart_442464 : Nat := 118140960795 + 442464 * 2 ^ 59
def prefixEnd_442464 : Nat := 4983230072969 + 3 ^ 40 * 442464 * 2
def baseEnd_442464 : Nat := 25244078256784676807239

theorem tailTrace_442464 : CollatzResearch.WordTrace tailWord_442464 prefixEnd_442464 25244078256784676807239 := by
  unfold tailWord_442464
  simp only [CollatzResearch.WordTrace]
  refine ⟨8068993934517984840063223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10758658579357313120084297 8068993934517984840063223)
  ·
    refine ⟨12103490901776977260094835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8068993934517984840063223 12103490901776977260094835)
    ·
      refine ⟨18155236352665465890142253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12103490901776977260094835 18155236352665465890142253)
      ·
        refine ⟨6808213632249549708803345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18155236352665465890142253 6808213632249549708803345)
        ·
          refine ⟨5106160224187162281602509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6808213632249549708803345 5106160224187162281602509)
          ·
            refine ⟨1914810084070185855600941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5106160224187162281602509 1914810084070185855600941)
            ·
              refine ⟨718053781526319695850353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1914810084070185855600941 718053781526319695850353)
              ·
                refine ⟨538540336144739771887765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718053781526319695850353 538540336144739771887765)
                ·
                  refine ⟨25244078256784676807239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 538540336144739771887765 25244078256784676807239)
                  ·
                    rfl

theorem cell23_442464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 6].length) (baseStart_442464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442464 prefixEnd_442464 := by exact prefixLift 442464
  have htrace : WordTrace (prefixWord ++ tailWord_442464) baseStart_442464 baseEnd_442464 := by
    simpa [prefixWord, tailWord_442464, baseEnd_442464] using wordTrace_append hprefix tailTrace_442464
  have hstable : (prefixWord ++ tailWord_442464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442464).length < 2 ^ (prefixWord ++ tailWord_442464).sum := by decide
  have hdescent : baseEnd_442464 < baseStart_442464 := by decide
  rcases family_descends (prefixWord ++ tailWord_442464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442467 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 6]
def baseStart_442467 : Nat := 118140960795 + 442467 * 2 ^ 59
def prefixEnd_442467 : Nat := 4983230072969 + 3 ^ 40 * 442467 * 2
def baseEnd_442467 : Nat := 227198244753025579527637

theorem tailTrace_442467 : CollatzResearch.WordTrace tailWord_442467 prefixEnd_442467 227198244753025579527637 := by
  unfold tailWord_442467
  simp only [CollatzResearch.WordTrace]
  refine ⟨16138097288025101192485655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10758731525350067461657103 16138097288025101192485655)
  ·
    refine ⟨24207145932037651788728483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16138097288025101192485655 24207145932037651788728483)
    ·
      refine ⟨36310718898056477683092725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24207145932037651788728483 36310718898056477683092725)
      ·
        refine ⟨3404129896692794782789943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36310718898056477683092725 3404129896692794782789943)
        ·
          refine ⟨5106194845039192174184915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3404129896692794782789943 5106194845039192174184915)
          ·
            refine ⟨7659292267558788261277373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5106194845039192174184915 7659292267558788261277373)
            ·
              refine ⟨2872234600334545597979015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7659292267558788261277373 2872234600334545597979015)
              ·
                refine ⟨4308351900501818396968523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2872234600334545597979015 4308351900501818396968523)
                ·
                  refine ⟨6462527850752727595452785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308351900501818396968523 6462527850752727595452785)
                  ·
                    refine ⟨4846895888064545696589589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6462527850752727595452785 4846895888064545696589589)
                    ·
                      refine ⟨227198244753025579527637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4846895888064545696589589 227198244753025579527637)
                      ·
                        rfl

theorem cell23_442467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_442467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442467 prefixEnd_442467 := by exact prefixLift 442467
  have htrace : WordTrace (prefixWord ++ tailWord_442467) baseStart_442467 baseEnd_442467 := by
    simpa [prefixWord, tailWord_442467, baseEnd_442467] using wordTrace_append hprefix tailTrace_442467
  have hstable : (prefixWord ++ tailWord_442467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442467).length < 2 ^ (prefixWord ++ tailWord_442467).sum := by decide
  have hdescent : baseEnd_442467 < baseStart_442467 := by decide
  rcases family_descends (prefixWord ++ tailWord_442467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442501 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 1, 5, 2]
def baseStart_442501 : Nat := 118140960795 + 442501 * 2 ^ 59
def prefixEnd_442501 : Nat := 4983230072969 + 3 ^ 40 * 442501 * 2
def baseEnd_442501 : Nat := 227215703095278446502481

theorem tailTrace_442501 : CollatzResearch.WordTrace tailWord_442501 prefixEnd_442501 227215703095278446502481 := by
  unfold tailWord_442501
  simp only [CollatzResearch.WordTrace]
  refine ⟨16139337369901924999223357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10759558246601283332815571 16139337369901924999223357)
  ·
    refine ⟨6052251513713221874708759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16139337369901924999223357 6052251513713221874708759)
    ·
      refine ⟨9078377270569832812063139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6052251513713221874708759 9078377270569832812063139)
      ·
        refine ⟨13617565905854749218094709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9078377270569832812063139 13617565905854749218094709)
        ·
          refine ⟨1276646803673882739196379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13617565905854749218094709 1276646803673882739196379)
          ·
            refine ⟨1914970205510824108794569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276646803673882739196379 1914970205510824108794569)
            ·
              refine ⟨1436227654133118081595927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1914970205510824108794569 1436227654133118081595927)
              ·
                refine ⟨2154341481199677122393891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436227654133118081595927 2154341481199677122393891)
                ·
                  refine ⟨3231512221799515683590837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154341481199677122393891 3231512221799515683590837)
                  ·
                    refine ⟨302954270793704595336641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3231512221799515683590837 302954270793704595336641)
                    ·
                      refine ⟨227215703095278446502481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 302954270793704595336641 227215703095278446502481)
                      ·
                        rfl

theorem cell23_442501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 5, 2].length) (baseStart_442501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442501 prefixEnd_442501 := by exact prefixLift 442501
  have htrace : WordTrace (prefixWord ++ tailWord_442501) baseStart_442501 baseEnd_442501 := by
    simpa [prefixWord, tailWord_442501, baseEnd_442501] using wordTrace_append hprefix tailTrace_442501
  have hstable : (prefixWord ++ tailWord_442501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442501).length < 2 ^ (prefixWord ++ tailWord_442501).sum := by decide
  have hdescent : baseEnd_442501 < baseStart_442501 := by decide
  rcases family_descends (prefixWord ++ tailWord_442501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442545 : List Nat := [1, 2, 2, 5, 3, 1, 1, 2, 1, 5]
def baseStart_442545 : Nat := 118140960795 + 442545 * 2 ^ 59
def prefixEnd_442545 : Nat := 4983230072969 + 3 ^ 40 * 442545 * 2
def baseEnd_442545 : Nat := 75746098748025424784093

theorem tailTrace_442545 : CollatzResearch.WordTrace tailWord_442545 prefixEnd_442545 75746098748025424784093 := by
  unfold tailWord_442545
  simp only [CollatzResearch.WordTrace]
  refine ⟨16140942181742520513825089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10760628121161680342550059 16140942181742520513825089)
  ·
    refine ⟨12105706636306890385368817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16140942181742520513825089 12105706636306890385368817)
    ·
      refine ⟨9079279977230167789026613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12105706636306890385368817 9079279977230167789026613)
      ·
        refine ⟨851182497865328230221245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9079279977230167789026613 851182497865328230221245)
        ·
          refine ⟨319193436699498086332967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 851182497865328230221245 319193436699498086332967)
          ·
            refine ⟨478790155049247129499451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319193436699498086332967 478790155049247129499451)
            ·
              refine ⟨718185232573870694249177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478790155049247129499451 718185232573870694249177)
              ·
                refine ⟨538638924430403020686883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718185232573870694249177 538638924430403020686883)
                ·
                  refine ⟨807958386645604531030325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538638924430403020686883 807958386645604531030325)
                  ·
                    refine ⟨75746098748025424784093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 807958386645604531030325 75746098748025424784093)
                    ·
                      rfl

theorem cell23_442545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_442545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442545 prefixEnd_442545 := by exact prefixLift 442545
  have htrace : WordTrace (prefixWord ++ tailWord_442545) baseStart_442545 baseEnd_442545 := by
    simpa [prefixWord, tailWord_442545, baseEnd_442545] using wordTrace_append hprefix tailTrace_442545
  have hstable : (prefixWord ++ tailWord_442545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442545).length < 2 ^ (prefixWord ++ tailWord_442545).sum := by decide
  have hdescent : baseEnd_442545 < baseStart_442545 := by decide
  rcases family_descends (prefixWord ++ tailWord_442545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442551 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 3]
def baseStart_442551 : Nat := 118140960795 + 442551 * 2 ^ 59
def prefixEnd_442551 : Nat := 4983230072969 + 3 ^ 40 * 442551 * 2
def baseEnd_442551 : Nat := 227241377128003250877251

theorem tailTrace_442551 : CollatzResearch.WordTrace tailWord_442551 prefixEnd_442551 227241377128003250877251 := by
  unfold tailWord_442551
  simp only [CollatzResearch.WordTrace]
  refine ⟨16141161019720783538543507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10760774013147189025695671 16141161019720783538543507)
  ·
    refine ⟨24211741529581175307815261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16141161019720783538543507 24211741529581175307815261)
    ·
      refine ⟨9079403073592940740430723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24211741529581175307815261 9079403073592940740430723)
      ·
        refine ⟨13619104610389411110646085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9079403073592940740430723 13619104610389411110646085)
        ·
          refine ⟨2553582114448014583246141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13619104610389411110646085 2553582114448014583246141)
          ·
            refine ⟨957593292918005468717303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2553582114448014583246141 957593292918005468717303)
            ·
              refine ⟨1436389939377008203075955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957593292918005468717303 1436389939377008203075955)
              ·
                refine ⟨2154584909065512304613933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436389939377008203075955 2154584909065512304613933)
                ·
                  refine ⟨807969340899567114230225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2154584909065512304613933 807969340899567114230225)
                  ·
                    refine ⟨605977005674675335672669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 807969340899567114230225 605977005674675335672669)
                    ·
                      refine ⟨227241377128003250877251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 605977005674675335672669 227241377128003250877251)
                      ·
                        rfl

theorem cell23_442551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_442551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442551 prefixEnd_442551 := by exact prefixLift 442551
  have htrace : WordTrace (prefixWord ++ tailWord_442551) baseStart_442551 baseEnd_442551 := by
    simpa [prefixWord, tailWord_442551, baseEnd_442551] using wordTrace_append hprefix tailTrace_442551
  have hstable : (prefixWord ++ tailWord_442551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442551).length < 2 ^ (prefixWord ++ tailWord_442551).sum := by decide
  have hdescent : baseEnd_442551 < baseStart_442551 := by decide
  rcases family_descends (prefixWord ++ tailWord_442551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442562 : List Nat := [3, 5, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_442562 : Nat := 118140960795 + 442562 * 2 ^ 59
def prefixEnd_442562 : Nat := 4983230072969 + 3 ^ 40 * 442562 * 2
def baseEnd_442562 : Nat := 75749008471734235946567

theorem tailTrace_442562 : CollatzResearch.WordTrace tailWord_442562 prefixEnd_442562 75749008471734235946567 := by
  unfold tailWord_442562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4035390555670233104298485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10761041481787288278129293 4035390555670233104298485)
  ·
    refine ⟨378317864594084353527983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4035390555670233104298485 378317864594084353527983)
    ·
      refine ⟨567476796891126530291975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378317864594084353527983 567476796891126530291975)
      ·
        refine ⟨851215195336689795437963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567476796891126530291975 851215195336689795437963)
        ·
          refine ⟨1276822793005034693156945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851215195336689795437963 1276822793005034693156945)
          ·
            refine ⟨957617094753776019867709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1276822793005034693156945 957617094753776019867709)
            ·
              refine ⟨359106410532666007450391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 957617094753776019867709 359106410532666007450391)
              ·
                refine ⟨538659615798999011175587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359106410532666007450391 538659615798999011175587)
                ·
                  refine ⟨807989423698498516763381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538659615798999011175587 807989423698498516763381)
                  ·
                    refine ⟨75749008471734235946567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 807989423698498516763381 75749008471734235946567)
                    ·
                      rfl

theorem cell23_442562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_442562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442562 prefixEnd_442562 := by exact prefixLift 442562
  have htrace : WordTrace (prefixWord ++ tailWord_442562) baseStart_442562 baseEnd_442562 := by
    simpa [prefixWord, tailWord_442562, baseEnd_442562] using wordTrace_append hprefix tailTrace_442562
  have hstable : (prefixWord ++ tailWord_442562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442562).length < 2 ^ (prefixWord ++ tailWord_442562).sum := by decide
  have hdescent : baseEnd_442562 < baseStart_442562 := by decide
  rcases family_descends (prefixWord ++ tailWord_442562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442584 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 2, 7]
def baseStart_442584 : Nat := 118140960795 + 442584 * 2 ^ 59
def prefixEnd_442584 : Nat := 4983230072969 + 3 ^ 40 * 442584 * 2
def baseEnd_442584 : Nat := 75752773996533873921533

theorem tailTrace_442584 : CollatzResearch.WordTrace tailWord_442584 prefixEnd_442584 75752773996533873921533 := by
  unfold tailWord_442584
  simp only [CollatzResearch.WordTrace]
  refine ⟨8071182314300615087247403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10761576419067486782996537 8071182314300615087247403)
  ·
    refine ⟨12106773471450922630871105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8071182314300615087247403 12106773471450922630871105)
    ·
      refine ⟨9080080103588191973153329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12106773471450922630871105 9080080103588191973153329)
      ·
        refine ⟨6810060077691143979864997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9080080103588191973153329 6810060077691143979864997)
        ·
          refine ⟨1276886264567089496224687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6810060077691143979864997 1276886264567089496224687)
          ·
            refine ⟨1915329396850634244337031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276886264567089496224687 1915329396850634244337031)
            ·
              refine ⟨2872994095275951366505547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1915329396850634244337031 2872994095275951366505547)
              ·
                refine ⟨4309491142913927049758321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2872994095275951366505547 4309491142913927049758321)
                ·
                  refine ⟨3232118357185445287318741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4309491142913927049758321 3232118357185445287318741)
                  ·
                    refine ⟨75752773996533873921533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3232118357185445287318741 75752773996533873921533)
                    ·
                      rfl

theorem cell23_442584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_442584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442584 prefixEnd_442584 := by exact prefixLift 442584
  have htrace : WordTrace (prefixWord ++ tailWord_442584) baseStart_442584 baseEnd_442584 := by
    simpa [prefixWord, tailWord_442584, baseEnd_442584] using wordTrace_append hprefix tailTrace_442584
  have hstable : (prefixWord ++ tailWord_442584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442584).length < 2 ^ (prefixWord ++ tailWord_442584).sum := by decide
  have hdescent : baseEnd_442584 < baseStart_442584 := by decide
  rcases family_descends (prefixWord ++ tailWord_442584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442604 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_442604 : Nat := 118140960795 + 442604 * 2 ^ 59
def prefixEnd_442604 : Nat := 4983230072969 + 3 ^ 40 * 442604 * 2
def baseEnd_442604 : Nat := 227268591602691543514507

theorem tailTrace_442604 : CollatzResearch.WordTrace tailWord_442604 prefixEnd_442604 227268591602691543514507 := by
  unfold tailWord_442604
  simp only [CollatzResearch.WordTrace]
  refine ⟨8071547044264386795111433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10762062725685849060148577 8071547044264386795111433)
  ·
    refine ⟨6053660283198290096333575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8071547044264386795111433 6053660283198290096333575)
    ·
      refine ⟨9080490424797435144500363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6053660283198290096333575 9080490424797435144500363)
      ·
        refine ⟨13620735637196152716750545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9080490424797435144500363 13620735637196152716750545)
        ·
          refine ⟨10215551727897114537562909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13620735637196152716750545 10215551727897114537562909)
          ·
            refine ⟨3830831897961417951586091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10215551727897114537562909 3830831897961417951586091)
            ·
              refine ⟨5746247846942126927379137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3830831897961417951586091 5746247846942126927379137)
              ·
                refine ⟨4309685885206595195534353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5746247846942126927379137 4309685885206595195534353)
                ·
                  refine ⟨3232264413904946396650765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4309685885206595195534353 3232264413904946396650765)
                  ·
                    refine ⟨1212099155214354898744037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3232264413904946396650765 1212099155214354898744037)
                    ·
                      refine ⟨227268591602691543514507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1212099155214354898744037 227268591602691543514507)
                      ·
                        rfl

theorem cell23_442604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_442604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442604 prefixEnd_442604 := by exact prefixLift 442604
  have htrace : WordTrace (prefixWord ++ tailWord_442604) baseStart_442604 baseEnd_442604 := by
    simpa [prefixWord, tailWord_442604, baseEnd_442604] using wordTrace_append hprefix tailTrace_442604
  have hstable : (prefixWord ++ tailWord_442604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442604).length < 2 ^ (prefixWord ++ tailWord_442604).sum := by decide
  have hdescent : baseEnd_442604 < baseStart_442604 := by decide
  rcases family_descends (prefixWord ++ tailWord_442604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442624 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 5]
def baseStart_442624 : Nat := 118140960795 + 442624 * 2 ^ 59
def prefixEnd_442624 : Nat := 4983230072969 + 3 ^ 40 * 442624 * 2
def baseEnd_442624 : Nat := 227278861215781465264415

theorem tailTrace_442624 : CollatzResearch.WordTrace tailWord_442624 prefixEnd_442624 227278861215781465264415 := by
  unfold tailWord_442624
  simp only [CollatzResearch.WordTrace]
  refine ⟨8071911774228158502975463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10762549032304211337300617 8071911774228158502975463)
  ·
    refine ⟨12107867661342237754463195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8071911774228158502975463 12107867661342237754463195)
    ·
      refine ⟨18161801492013356631694793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12107867661342237754463195 18161801492013356631694793)
      ·
        refine ⟨13621351119010017473771095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18161801492013356631694793 13621351119010017473771095)
        ·
          refine ⟨20432026678515026210656643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13621351119010017473771095 20432026678515026210656643)
          ·
            refine ⟨30648040017772539315984965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20432026678515026210656643 30648040017772539315984965)
            ·
              refine ⟨5746507503332351121747181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30648040017772539315984965 5746507503332351121747181)
              ·
                refine ⟨2154940313749631670655193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5746507503332351121747181 2154940313749631670655193)
                ·
                  refine ⟨1616205235312223752991395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2154940313749631670655193 1616205235312223752991395)
                  ·
                    refine ⟨2424307852968335629487093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1616205235312223752991395 2424307852968335629487093)
                    ·
                      refine ⟨227278861215781465264415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2424307852968335629487093 227278861215781465264415)
                      ·
                        rfl

theorem cell23_442624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_442624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442624 prefixEnd_442624 := by exact prefixLift 442624
  have htrace : WordTrace (prefixWord ++ tailWord_442624) baseStart_442624 baseEnd_442624 := by
    simpa [prefixWord, tailWord_442624, baseEnd_442624] using wordTrace_append hprefix tailTrace_442624
  have hstable : (prefixWord ++ tailWord_442624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442624).length < 2 ^ (prefixWord ++ tailWord_442624).sum := by decide
  have hdescent : baseEnd_442624 < baseStart_442624 := by decide
  rcases family_descends (prefixWord ++ tailWord_442624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442655 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 1, 4, 2]
def baseStart_442655 : Nat := 118140960795 + 442655 * 2 ^ 59
def prefixEnd_442655 : Nat := 4983230072969 + 3 ^ 40 * 442655 * 2
def baseEnd_442655 : Nat := 227294779116070843976773

theorem tailTrace_442655 : CollatzResearch.WordTrace tailWord_442655 prefixEnd_442655 227294779116070843976773 := by
  unfold tailWord_442655
  simp only [CollatzResearch.WordTrace]
  refine ⟨16144954211344009300329419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10763302807562672866886279 16144954211344009300329419)
  ·
    refine ⟨24217431317016013950494129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16144954211344009300329419 24217431317016013950494129)
    ·
      refine ⟨18163073487762010462870597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24217431317016013950494129 18163073487762010462870597)
      ·
        refine ⟨3405576278955376961788237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18163073487762010462870597 3405576278955376961788237)
        ·
          refine ⟨1277091104608266360670589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3405576278955376961788237 1277091104608266360670589)
          ·
            refine ⟨478909164228099885251471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1277091104608266360670589 478909164228099885251471)
            ·
              refine ⟨718363746342149827877207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478909164228099885251471 718363746342149827877207)
              ·
                refine ⟨1077545619513224741815811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718363746342149827877207 1077545619513224741815811)
                ·
                  refine ⟨1616318429269837112723717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077545619513224741815811 1616318429269837112723717)
                  ·
                    refine ⟨303059705488094458635697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1616318429269837112723717 303059705488094458635697)
                    ·
                      refine ⟨227294779116070843976773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 303059705488094458635697 227294779116070843976773)
                      ·
                        rfl

theorem cell23_442655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_442655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442655 prefixEnd_442655 := by exact prefixLift 442655
  have htrace : WordTrace (prefixWord ++ tailWord_442655) baseStart_442655 baseEnd_442655 := by
    simpa [prefixWord, tailWord_442655, baseEnd_442655] using wordTrace_append hprefix tailTrace_442655
  have hstable : (prefixWord ++ tailWord_442655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442655).length < 2 ^ (prefixWord ++ tailWord_442655).sum := by decide
  have hdescent : baseEnd_442655 < baseStart_442655 := by decide
  rcases family_descends (prefixWord ++ tailWord_442655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442711 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 4]
def baseStart_442711 : Nat := 118140960795 + 442711 * 2 ^ 59
def prefixEnd_442711 : Nat := 4983230072969 + 3 ^ 40 * 442711 * 2
def baseEnd_442711 : Nat := 227323534032722624876515

theorem tailTrace_442711 : CollatzResearch.WordTrace tailWord_442711 prefixEnd_442711 227323534032722624876515 := by
  unfold tailWord_442711
  simp only [CollatzResearch.WordTrace]
  refine ⟨16146996699141130864367987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10764664466094087242911991 16146996699141130864367987)
  ·
    refine ⟨24220495048711696296551981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16146996699141130864367987 24220495048711696296551981)
    ·
      refine ⟨9082685643266886111206993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24220495048711696296551981 9082685643266886111206993)
      ·
        refine ⟨6812014232450164583405245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9082685643266886111206993 6812014232450164583405245)
        ·
          refine ⟨2554505337168811718776967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6812014232450164583405245 2554505337168811718776967)
          ·
            refine ⟨3831758005753217578165451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554505337168811718776967 3831758005753217578165451)
            ·
              refine ⟨5747637008629826367248177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3831758005753217578165451 5747637008629826367248177)
              ·
                refine ⟨4310727756472369775436133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5747637008629826367248177 4310727756472369775436133)
                ·
                  refine ⟨808261454338569332894275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4310727756472369775436133 808261454338569332894275)
                  ·
                    refine ⟨1212392181507853999341413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 808261454338569332894275 1212392181507853999341413)
                    ·
                      refine ⟨227323534032722624876515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1212392181507853999341413 227323534032722624876515)
                      ·
                        rfl

theorem cell23_442711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_442711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442711 prefixEnd_442711 := by exact prefixLift 442711
  have htrace : WordTrace (prefixWord ++ tailWord_442711) baseStart_442711 baseEnd_442711 := by
    simpa [prefixWord, tailWord_442711, baseEnd_442711] using wordTrace_append hprefix tailTrace_442711
  have hstable : (prefixWord ++ tailWord_442711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442711).length < 2 ^ (prefixWord ++ tailWord_442711).sum := by decide
  have hdescent : baseEnd_442711 < baseStart_442711 := by decide
  rcases family_descends (prefixWord ++ tailWord_442711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442728 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_442728 : Nat := 118140960795 + 442728 * 2 ^ 59
def prefixEnd_442728 : Nat := 4983230072969 + 3 ^ 40 * 442728 * 2
def baseEnd_442728 : Nat := 227332263203849058363937

theorem tailTrace_442728 : CollatzResearch.WordTrace tailWord_442728 prefixEnd_442728 227332263203849058363937 := by
  unfold tailWord_442728
  simp only [CollatzResearch.WordTrace]
  refine ⟨8073808370039771383868419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10765077826719695178491225 8073808370039771383868419)
  ·
    refine ⟨12110712555059657075802629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8073808370039771383868419 12110712555059657075802629)
    ·
      refine ⟨2270758604073685701712993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12110712555059657075802629 2270758604073685701712993)
      ·
        refine ⟨1703068953055264276284745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2270758604073685701712993 1703068953055264276284745)
        ·
          refine ⟨1277301714791448207213559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1703068953055264276284745 1277301714791448207213559)
          ·
            refine ⟨1915952572187172310820339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277301714791448207213559 1915952572187172310820339)
            ·
              refine ⟨2873928858280758466230509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1915952572187172310820339 2873928858280758466230509)
              ·
                refine ⟨1077723321855284424836441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2873928858280758466230509 1077723321855284424836441)
                ·
                  refine ⟨808292491391463318627331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1077723321855284424836441 808292491391463318627331)
                  ·
                    refine ⟨1212438737087194977940997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 808292491391463318627331 1212438737087194977940997)
                    ·
                      refine ⟨227332263203849058363937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1212438737087194977940997 227332263203849058363937)
                      ·
                        rfl

theorem cell23_442728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_442728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442728 prefixEnd_442728 := by exact prefixLift 442728
  have htrace : WordTrace (prefixWord ++ tailWord_442728) baseStart_442728 baseEnd_442728 := by
    simpa [prefixWord, tailWord_442728, baseEnd_442728] using wordTrace_append hprefix tailTrace_442728
  have hstable : (prefixWord ++ tailWord_442728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442728).length < 2 ^ (prefixWord ++ tailWord_442728).sum := by decide
  have hdescent : baseEnd_442728 < baseStart_442728 := by decide
  rcases family_descends (prefixWord ++ tailWord_442728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442731 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 3]
def baseStart_442731 : Nat := 118140960795 + 442731 * 2 ^ 59
def prefixEnd_442731 : Nat := 4983230072969 + 3 ^ 40 * 442731 * 2
def baseEnd_442731 : Nat := 227333803645812546626423

theorem tailTrace_442731 : CollatzResearch.WordTrace tailWord_442731 prefixEnd_442731 227333803645812546626423 := by
  unfold tailWord_442731
  simp only [CollatzResearch.WordTrace]
  refine ⟨16147726159068674280096047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10765150772712449520064031 16147726159068674280096047)
  ·
    refine ⟨24221589238603011420144071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16147726159068674280096047 24221589238603011420144071)
    ·
      refine ⟨36332383857904517130216107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24221589238603011420144071 36332383857904517130216107)
      ·
        refine ⟨54498575786856775695324161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36332383857904517130216107 54498575786856775695324161)
        ·
          refine ⟨40873931840142581771493121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54498575786856775695324161 40873931840142581771493121)
          ·
            refine ⟨30655448880106936328619841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40873931840142581771493121 30655448880106936328619841)
            ·
              refine ⟨22991586660080202246464881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30655448880106936328619841 22991586660080202246464881)
              ·
                refine ⟨17243689995060151684848661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22991586660080202246464881 17243689995060151684848661)
                ·
                  refine ⟨808297968518444610227281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17243689995060151684848661 808297968518444610227281)
                  ·
                    refine ⟨606223476388833457670461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 808297968518444610227281 606223476388833457670461)
                    ·
                      refine ⟨227333803645812546626423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 606223476388833457670461 227333803645812546626423)
                      ·
                        rfl

theorem cell23_442731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 3].length) (baseStart_442731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442731 prefixEnd_442731 := by exact prefixLift 442731
  have htrace : WordTrace (prefixWord ++ tailWord_442731) baseStart_442731 baseEnd_442731 := by
    simpa [prefixWord, tailWord_442731, baseEnd_442731] using wordTrace_append hprefix tailTrace_442731
  have hstable : (prefixWord ++ tailWord_442731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442731).length < 2 ^ (prefixWord ++ tailWord_442731).sum := by decide
  have hdescent : baseEnd_442731 < baseStart_442731 := by decide
  rcases family_descends (prefixWord ++ tailWord_442731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442762 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 2, 4, 2]
def baseStart_442762 : Nat := 118140960795 + 442762 * 2 ^ 59
def prefixEnd_442762 : Nat := 4983230072969 + 3 ^ 40 * 442762 * 2
def baseEnd_442762 : Nat := 227349721546101925338781

theorem tailTrace_442762 : CollatzResearch.WordTrace tailWord_442762 prefixEnd_442762 227349721546101925338781 := by
  unfold tailWord_442762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4037214205489091643618635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10765904547970911049649693 4037214205489091643618635)
  ·
    refine ⟨6055821308233637465427953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4037214205489091643618635 6055821308233637465427953)
    ·
      refine ⟨4541865981175228099070965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6055821308233637465427953 4541865981175228099070965)
      ·
        refine ⟨425799935735177634287903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4541865981175228099070965 425799935735177634287903)
        ·
          refine ⟨638699903602766451431855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425799935735177634287903 638699903602766451431855)
          ·
            refine ⟨958049855404149677147783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638699903602766451431855 958049855404149677147783)
            ·
              refine ⟨1437074783106224515721675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958049855404149677147783 1437074783106224515721675)
              ·
                refine ⟨2155612174659336773582513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437074783106224515721675 2155612174659336773582513)
                ·
                  refine ⟨1616709130994502580186885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2155612174659336773582513 1616709130994502580186885)
                  ·
                    refine ⟨303132962061469233785041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1616709130994502580186885 303132962061469233785041)
                    ·
                      refine ⟨227349721546101925338781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 303132962061469233785041 227349721546101925338781)
                      ·
                        rfl

theorem cell23_442762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_442762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442762 prefixEnd_442762 := by exact prefixLift 442762
  have htrace : WordTrace (prefixWord ++ tailWord_442762) baseStart_442762 baseEnd_442762 := by
    simpa [prefixWord, tailWord_442762, baseEnd_442762] using wordTrace_append hprefix tailTrace_442762
  have hstable : (prefixWord ++ tailWord_442762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442762).length < 2 ^ (prefixWord ++ tailWord_442762).sum := by decide
  have hdescent : baseEnd_442762 < baseStart_442762 := by decide
  rcases family_descends (prefixWord ++ tailWord_442762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442782 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_442782 : Nat := 118140960795 + 442782 * 2 ^ 59
def prefixEnd_442782 : Nat := 4983230072969 + 3 ^ 40 * 442782 * 2
def baseEnd_442782 : Nat := 227359991159191847088689

theorem tailTrace_442782 : CollatzResearch.WordTrace tailWord_442782 prefixEnd_442782 227359991159191847088689 := by
  unfold tailWord_442782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2018698285235488748775325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10766390854589273326801733 2018698285235488748775325)
  ·
    refine ⟨757011856963308280790747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2018698285235488748775325 757011856963308280790747)
    ·
      refine ⟨1135517785444962421186121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 757011856963308280790747 1135517785444962421186121)
      ·
        refine ⟨851638339083721815889591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1135517785444962421186121 851638339083721815889591)
        ·
          refine ⟨1277457508625582723834387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851638339083721815889591 1277457508625582723834387)
          ·
            refine ⟨1916186262938374085751581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277457508625582723834387 1916186262938374085751581)
            ·
              refine ⟨718569848601890282156843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1916186262938374085751581 718569848601890282156843)
              ·
                refine ⟨1077854772902835423235265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718569848601890282156843 1077854772902835423235265)
                ·
                  refine ⟨808391079677126567426449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1077854772902835423235265 808391079677126567426449)
                  ·
                    refine ⟨606293309757844925569837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 808391079677126567426449 606293309757844925569837)
                    ·
                      refine ⟨227359991159191847088689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 606293309757844925569837 227359991159191847088689)
                      ·
                        rfl

theorem cell23_442782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_442782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442782 prefixEnd_442782 := by exact prefixLift 442782
  have htrace : WordTrace (prefixWord ++ tailWord_442782) baseStart_442782 baseEnd_442782 := by
    simpa [prefixWord, tailWord_442782, baseEnd_442782] using wordTrace_append hprefix tailTrace_442782
  have hstable : (prefixWord ++ tailWord_442782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442782).length < 2 ^ (prefixWord ++ tailWord_442782).sum := by decide
  have hdescent : baseEnd_442782 < baseStart_442782 := by decide
  rcases family_descends (prefixWord ++ tailWord_442782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442812 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 3, 1, 3]
def baseStart_442812 : Nat := 118140960795 + 442812 * 2 ^ 59
def prefixEnd_442812 : Nat := 4983230072969 + 3 ^ 40 * 442812 * 2
def baseEnd_442812 : Nat := 227375395578826729713551

theorem tailTrace_442812 : CollatzResearch.WordTrace tailWord_442812 prefixEnd_442812 227375395578826729713551 := by
  unfold tailWord_442812
  simp only [CollatzResearch.WordTrace]
  refine ⟨8075340235887612556897345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10767120314516816742529793 8075340235887612556897345)
  ·
    refine ⟨6056505176915709417673009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8075340235887612556897345 6056505176915709417673009)
    ·
      refine ⟨4542378882686782063254757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6056505176915709417673009 4542378882686782063254757)
      ·
        refine ⟨851696040503771636860267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4542378882686782063254757 851696040503771636860267)
        ·
          refine ⟨1277544060755657455290401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851696040503771636860267 1277544060755657455290401)
          ·
            refine ⟨958158045566743091467801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1277544060755657455290401 958158045566743091467801)
            ·
              refine ⟨718618534175057318600851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958158045566743091467801 718618534175057318600851)
              ·
                refine ⟨1077927801262585977901277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718618534175057318600851 1077927801262585977901277)
                ·
                  refine ⟨404222925473469741712979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077927801262585977901277 404222925473469741712979)
                  ·
                    refine ⟨606334388210204612569469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 404222925473469741712979 606334388210204612569469)
                    ·
                      refine ⟨227375395578826729713551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 606334388210204612569469 227375395578826729713551)
                      ·
                        rfl

theorem cell23_442812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_442812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442812 prefixEnd_442812 := by exact prefixLift 442812
  have htrace : WordTrace (prefixWord ++ tailWord_442812) baseStart_442812 baseEnd_442812 := by
    simpa [prefixWord, tailWord_442812, baseEnd_442812] using wordTrace_append hprefix tailTrace_442812
  have hstable : (prefixWord ++ tailWord_442812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442812).length < 2 ^ (prefixWord ++ tailWord_442812).sum := by decide
  have hdescent : baseEnd_442812 < baseStart_442812 := by decide
  rcases family_descends (prefixWord ++ tailWord_442812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442841 : List Nat := [1, 2, 1, 2, 4, 1, 3, 9]
def baseStart_442841 : Nat := 118140960795 + 442841 * 2 ^ 59
def prefixEnd_442841 : Nat := 4983230072969 + 3 ^ 40 * 442841 * 2
def baseEnd_442841 : Nat := 8421862463622485787071

theorem tailTrace_442841 : CollatzResearch.WordTrace tailWord_442841 prefixEnd_442841 8421862463622485787071 := by
  unfold tailWord_442841
  simp only [CollatzResearch.WordTrace]
  refine ⟨16151738188670163066600377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10767825459113442044400251 16151738188670163066600377)
  ·
    refine ⟨12113803641502622299950283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16151738188670163066600377 12113803641502622299950283)
    ·
      refine ⟨18170705462253933449925425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12113803641502622299950283 18170705462253933449925425)
      ·
        refine ⟨13628029096690450087444069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18170705462253933449925425 13628029096690450087444069)
        ·
          refine ⟨2555255455629459391395763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13628029096690450087444069 2555255455629459391395763)
          ·
            refine ⟨3832883183444189087093645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555255455629459391395763 3832883183444189087093645)
            ·
              refine ⟨1437331193791570907660117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3832883183444189087093645 1437331193791570907660117)
              ·
                refine ⟨8421862463622485787071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1437331193791570907660117 8421862463622485787071)
                ·
                  rfl

theorem cell23_442841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 9].length) (baseStart_442841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442841 prefixEnd_442841 := by exact prefixLift 442841
  have htrace : WordTrace (prefixWord ++ tailWord_442841) baseStart_442841 baseEnd_442841 := by
    simpa [prefixWord, tailWord_442841, baseEnd_442841] using wordTrace_append hprefix tailTrace_442841
  have hstable : (prefixWord ++ tailWord_442841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442841).length < 2 ^ (prefixWord ++ tailWord_442841).sum := by decide
  have hdescent : baseEnd_442841 < baseStart_442841 := by decide
  rcases family_descends (prefixWord ++ tailWord_442841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442855 : List Nat := [1, 1, 5, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_442855 : Nat := 118140960795 + 442855 * 2 ^ 59
def prefixEnd_442855 : Nat := 4983230072969 + 3 ^ 40 * 442855 * 2
def baseEnd_442855 : Nat := 227397475246970061475853

theorem tailTrace_442855 : CollatzResearch.WordTrace tailWord_442855 prefixEnd_442855 227397475246970061475853 := by
  unfold tailWord_442855
  simp only [CollatzResearch.WordTrace]
  refine ⟨16152248810619443457610019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10768165873746295638406679 16152248810619443457610019)
  ·
    refine ⟨24228373215929165186415029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16152248810619443457610019 24228373215929165186415029)
    ·
      refine ⟨2271409988993359236226409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24228373215929165186415029 2271409988993359236226409)
      ·
        refine ⟨1703557491745019427169807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2271409988993359236226409 1703557491745019427169807)
        ·
          refine ⟨2555336237617529140754711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703557491745019427169807 2555336237617529140754711)
          ·
            refine ⟨3833004356426293711132067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555336237617529140754711 3833004356426293711132067)
            ·
              refine ⟨5749506534639440566698101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833004356426293711132067 5749506534639440566698101)
              ·
                refine ⟨539016237622447553127947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5749506534639440566698101 539016237622447553127947)
                ·
                  refine ⟨808524356433671329691921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539016237622447553127947 808524356433671329691921)
                  ·
                    refine ⟨606393267325253497268941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 808524356433671329691921 606393267325253497268941)
                    ·
                      refine ⟨227397475246970061475853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 606393267325253497268941 227397475246970061475853)
                      ·
                        rfl

theorem cell23_442855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_442855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442855 prefixEnd_442855 := by exact prefixLift 442855
  have htrace : WordTrace (prefixWord ++ tailWord_442855) baseStart_442855 baseEnd_442855 := by
    simpa [prefixWord, tailWord_442855, baseEnd_442855] using wordTrace_append hprefix tailTrace_442855
  have hstable : (prefixWord ++ tailWord_442855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442855).length < 2 ^ (prefixWord ++ tailWord_442855).sum := by decide
  have hdescent : baseEnd_442855 < baseStart_442855 := by decide
  rcases family_descends (prefixWord ++ tailWord_442855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442858 : List Nat := [3, 1, 3, 1, 3, 3, 9]
def baseStart_442858 : Nat := 118140960795 + 442858 * 2 ^ 59
def prefixEnd_442858 : Nat := 4983230072969 + 3 ^ 40 * 442858 * 2
def baseEnd_442858 : Nat := 2807395255418932712819

theorem tailTrace_442858 : CollatzResearch.WordTrace tailWord_442858 prefixEnd_442858 2807395255418932712819 := by
  unfold tailWord_442858
  simp only [CollatzResearch.WordTrace]
  refine ⟨4038089557402143742492307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10768238819739049979979485 4038089557402143742492307)
  ·
    refine ⟨6057134336103215613738461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4038089557402143742492307 6057134336103215613738461)
    ·
      refine ⟨2271425376038705855151923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6057134336103215613738461 2271425376038705855151923)
      ·
        refine ⟨3407138064058058782727885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2271425376038705855151923 3407138064058058782727885)
        ·
          refine ⟨1277676774021772043522957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3407138064058058782727885 1277676774021772043522957)
          ·
            refine ⟨479128790258164516321109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1277676774021772043522957 479128790258164516321109)
            ·
              refine ⟨2807395255418932712819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 479128790258164516321109 2807395255418932712819)
              ·
                rfl

theorem cell23_442858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 9].length) (baseStart_442858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442858 prefixEnd_442858 := by exact prefixLift 442858
  have htrace : WordTrace (prefixWord ++ tailWord_442858) baseStart_442858 baseEnd_442858 := by
    simpa [prefixWord, tailWord_442858, baseEnd_442858] using wordTrace_append hprefix tailTrace_442858
  have hstable : (prefixWord ++ tailWord_442858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442858).length < 2 ^ (prefixWord ++ tailWord_442858).sum := by decide
  have hdescent : baseEnd_442858 < baseStart_442858 := by decide
  rcases family_descends (prefixWord ++ tailWord_442858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442886 : List Nat := [6, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_442886 : Nat := 118140960795 + 442886 * 2 ^ 59
def prefixEnd_442886 : Nat := 4983230072969 + 3 ^ 40 * 442886 * 2
def baseEnd_442886 : Nat := 227413393147259440188211

theorem tailTrace_442886 : CollatzResearch.WordTrace tailWord_442886 prefixEnd_442886 227413393147259440188211 := by
  unfold tailWord_442886
  simp only [CollatzResearch.WordTrace]
  refine ⟨504793108547097992249641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10768919649004757167992341 504793108547097992249641)
  ·
    refine ⟨378594831410323494187231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 504793108547097992249641 378594831410323494187231)
    ·
      refine ⟨567892247115485241280847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378594831410323494187231 567892247115485241280847)
      ·
        refine ⟨851838370673227861921271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567892247115485241280847 851838370673227861921271)
        ·
          refine ⟨1277757556009841792881907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851838370673227861921271 1277757556009841792881907)
          ·
            refine ⟨1916636334014762689322861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277757556009841792881907 1916636334014762689322861)
            ·
              refine ⟨718738625255536008496073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1916636334014762689322861 718738625255536008496073)
              ·
                refine ⟨539053968941652006372055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718738625255536008496073 539053968941652006372055)
                ·
                  refine ⟨808580953412478009558083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539053968941652006372055 808580953412478009558083)
                  ·
                    refine ⟨1212871430118717014337125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 808580953412478009558083 1212871430118717014337125)
                    ·
                      refine ⟨227413393147259440188211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1212871430118717014337125 227413393147259440188211)
                      ·
                        rfl

theorem cell23_442886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_442886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442886 prefixEnd_442886 := by exact prefixLift 442886
  have htrace : WordTrace (prefixWord ++ tailWord_442886) baseStart_442886 baseEnd_442886 := by
    simpa [prefixWord, tailWord_442886, baseEnd_442886] using wordTrace_append hprefix tailTrace_442886
  have hstable : (prefixWord ++ tailWord_442886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442886).length < 2 ^ (prefixWord ++ tailWord_442886).sum := by decide
  have hdescent : baseEnd_442886 < baseStart_442886 := by decide
  rcases family_descends (prefixWord ++ tailWord_442886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442928 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 3]
def baseStart_442928 : Nat := 118140960795 + 442928 * 2 ^ 59
def prefixEnd_442928 : Nat := 4983230072969 + 3 ^ 40 * 442928 * 2
def baseEnd_442928 : Nat := 227434959334748275863017

theorem tailTrace_442928 : CollatzResearch.WordTrace tailWord_442928 prefixEnd_442928 227434959334748275863017 := by
  unfold tailWord_442928
  simp only [CollatzResearch.WordTrace]
  refine ⟨8077455669677488462508719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10769940892903317950011625 8077455669677488462508719)
  ·
    refine ⟨12116183504516232693763079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8077455669677488462508719 12116183504516232693763079)
    ·
      refine ⟨18174275256774349040644619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12116183504516232693763079 18174275256774349040644619)
      ·
        refine ⟨27261412885161523560966929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18174275256774349040644619 27261412885161523560966929)
        ·
          refine ⟨20446059663871142670725197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27261412885161523560966929 20446059663871142670725197)
          ·
            refine ⟨7667272373951678501521949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20446059663871142670725197 7667272373951678501521949)
            ·
              refine ⟨2875227140231879438070731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7667272373951678501521949 2875227140231879438070731)
              ·
                refine ⟨4312840710347819157106097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875227140231879438070731 4312840710347819157106097)
                ·
                  refine ⟨3234630532760864367829573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4312840710347819157106097 3234630532760864367829573)
                  ·
                    refine ⟨606493224892662068968045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3234630532760864367829573 606493224892662068968045)
                    ·
                      refine ⟨227434959334748275863017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 606493224892662068968045 227434959334748275863017)
                      ·
                        rfl

theorem cell23_442928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 3].length) (baseStart_442928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442928 prefixEnd_442928 := by exact prefixLift 442928
  have htrace : WordTrace (prefixWord ++ tailWord_442928) baseStart_442928 baseEnd_442928 := by
    simpa [prefixWord, tailWord_442928, baseEnd_442928] using wordTrace_append hprefix tailTrace_442928
  have hstable : (prefixWord ++ tailWord_442928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442928).length < 2 ^ (prefixWord ++ tailWord_442928).sum := by decide
  have hdescent : baseEnd_442928 < baseStart_442928 := by decide
  rcases family_descends (prefixWord ++ tailWord_442928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442938 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_442938 : Nat := 118140960795 + 442938 * 2 ^ 59
def prefixEnd_442938 : Nat := 4983230072969 + 3 ^ 40 * 442938 * 2
def baseEnd_442938 : Nat := 227440094141293236737971

theorem tailTrace_442938 : CollatzResearch.WordTrace tailWord_442938 prefixEnd_442938 227440094141293236737971 := by
  unfold tailWord_442938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4038819017329687158220367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10770184046212499088587645 4038819017329687158220367)
  ·
    refine ⟨6058228525994530737330551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4038819017329687158220367 6058228525994530737330551)
    ·
      refine ⟨9087342788991796105995827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6058228525994530737330551 9087342788991796105995827)
      ·
        refine ⟨13631014183487694158993741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9087342788991796105995827 13631014183487694158993741)
        ·
          refine ⟨5111630318807885309622653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13631014183487694158993741 5111630318807885309622653)
          ·
            refine ⟨1916861369552956991108495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5111630318807885309622653 1916861369552956991108495)
            ·
              refine ⟨2875292054329435486662743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1916861369552956991108495 2875292054329435486662743)
              ·
                refine ⟨4312938081494153229994115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875292054329435486662743 4312938081494153229994115)
                ·
                  refine ⟨6469407122241229844991173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312938081494153229994115 6469407122241229844991173)
                  ·
                    refine ⟨1213013835420230595935845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6469407122241229844991173 1213013835420230595935845)
                    ·
                      refine ⟨227440094141293236737971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1213013835420230595935845 227440094141293236737971)
                      ·
                        rfl

theorem cell23_442938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_442938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442938 prefixEnd_442938 := by exact prefixLift 442938
  have htrace : WordTrace (prefixWord ++ tailWord_442938) baseStart_442938 baseEnd_442938 := by
    simpa [prefixWord, tailWord_442938, baseEnd_442938] using wordTrace_append hprefix tailTrace_442938
  have hstable : (prefixWord ++ tailWord_442938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442938).length < 2 ^ (prefixWord ++ tailWord_442938).sum := by decide
  have hdescent : baseEnd_442938 < baseStart_442938 := by decide
  rcases family_descends (prefixWord ++ tailWord_442938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442965 : List Nat := [1, 3, 2, 2, 1, 1, 3, 5, 5]
def baseStart_442965 : Nat := 118140960795 + 442965 * 2 ^ 59
def prefixEnd_442965 : Nat := 4983230072969 + 3 ^ 40 * 442965 * 2
def baseEnd_442965 : Nat := 25272662013218292344483

theorem tailTrace_442965 : CollatzResearch.WordTrace tailWord_442965 prefixEnd_442965 25272662013218292344483 := by
  unfold tailWord_442965
  simp only [CollatzResearch.WordTrace]
  refine ⟨16156260840220932244114349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10770840560147288162742899 16156260840220932244114349)
  ·
    refine ⟨6058597815082849591542881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16156260840220932244114349 6058597815082849591542881)
    ·
      refine ⟨4543948361312137193657161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6058597815082849591542881 4543948361312137193657161)
      ·
        refine ⟨3407961270984102895242871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4543948361312137193657161 3407961270984102895242871)
        ·
          refine ⟨5111941906476154342864307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3407961270984102895242871 5111941906476154342864307)
          ·
            refine ⟨7667912859714231514296461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5111941906476154342864307 7667912859714231514296461)
            ·
              refine ⟨2875467322392836817861173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7667912859714231514296461 2875467322392836817861173)
              ·
                refine ⟨269575061474328451674485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2875467322392836817861173 269575061474328451674485)
                ·
                  refine ⟨25272662013218292344483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269575061474328451674485 25272662013218292344483)
                  ·
                    rfl

theorem cell23_442965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 5].length) (baseStart_442965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442965 prefixEnd_442965 := by exact prefixLift 442965
  have htrace : WordTrace (prefixWord ++ tailWord_442965) baseStart_442965 baseEnd_442965 := by
    simpa [prefixWord, tailWord_442965, baseEnd_442965] using wordTrace_append hprefix tailTrace_442965
  have hstable : (prefixWord ++ tailWord_442965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442965).length < 2 ^ (prefixWord ++ tailWord_442965).sum := by decide
  have hdescent : baseEnd_442965 < baseStart_442965 := by decide
  rcases family_descends (prefixWord ++ tailWord_442965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442988 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_442988 : Nat := 118140960795 + 442988 * 2 ^ 59
def prefixEnd_442988 : Nat := 4983230072969 + 3 ^ 40 * 442988 * 2
def baseEnd_442988 : Nat := 227465768174018041112741

theorem tailTrace_442988 : CollatzResearch.WordTrace tailWord_442988 prefixEnd_442988 227465768174018041112741 := by
  unfold tailWord_442988
  simp only [CollatzResearch.WordTrace]
  refine ⟨8078549859568803586100809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10771399812758404781467745 8078549859568803586100809)
  ·
    refine ⟨6058912394676602689575607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8078549859568803586100809 6058912394676602689575607)
    ·
      refine ⟨9088368592014904034363411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6058912394676602689575607 9088368592014904034363411)
      ·
        refine ⟨13632552888022356051545117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9088368592014904034363411 13632552888022356051545117)
        ·
          refine ⟨5112207333008383519329419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13632552888022356051545117 5112207333008383519329419)
          ·
            refine ⟨7668310999512575278994129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5112207333008383519329419 7668310999512575278994129)
            ·
              refine ⟨5751233249634431459245597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7668310999512575278994129 5751233249634431459245597)
              ·
                refine ⟨2156712468612911797217099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5751233249634431459245597 2156712468612911797217099)
                ·
                  refine ⟨3235068702919367695825649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156712468612911797217099 3235068702919367695825649)
                  ·
                    refine ⟨2426301527189525771869237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3235068702919367695825649 2426301527189525771869237)
                    ·
                      refine ⟨227465768174018041112741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2426301527189525771869237 227465768174018041112741)
                      ·
                        rfl

theorem cell23_442988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_442988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_442988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_442988 prefixEnd_442988 := by exact prefixLift 442988
  have htrace : WordTrace (prefixWord ++ tailWord_442988) baseStart_442988 baseEnd_442988 := by
    simpa [prefixWord, tailWord_442988, baseEnd_442988] using wordTrace_append hprefix tailTrace_442988
  have hstable : (prefixWord ++ tailWord_442988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442988).length < 2 ^ (prefixWord ++ tailWord_442988).sum := by decide
  have hdescent : baseEnd_442988 < baseStart_442988 := by decide
  rcases family_descends (prefixWord ++ tailWord_442988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443015 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_443015 : Nat := 118140960795 + 443015 * 2 ^ 59
def prefixEnd_443015 : Nat := 4983230072969 + 3 ^ 40 * 443015 * 2
def baseEnd_443015 : Nat := 227479632151689435475117

theorem tailTrace_443015 : CollatzResearch.WordTrace tailWord_443015 prefixEnd_443015 227479632151689435475117 := by
  unfold tailWord_443015
  simp only [CollatzResearch.WordTrace]
  refine ⟨16158084490039790783434499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10772056326693193855622999 16158084490039790783434499)
  ·
    refine ⟨24237126735059686175151749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16158084490039790783434499 24237126735059686175151749)
    ·
      refine ⟨4544461262823691157840953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24237126735059686175151749 4544461262823691157840953)
      ·
        refine ⟨3408345947117768368380715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4544461262823691157840953 3408345947117768368380715)
        ·
          refine ⟨5112518920676652552571073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3408345947117768368380715 5112518920676652552571073)
          ·
            refine ⟨3834389190507489414428305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5112518920676652552571073 3834389190507489414428305)
            ·
              refine ⟨2875791892880617060821229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3834389190507489414428305 2875791892880617060821229)
              ·
                refine ⟨1078421959830231397807961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2875791892880617060821229 1078421959830231397807961)
                ·
                  refine ⟨808816469872673548355971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1078421959830231397807961 808816469872673548355971)
                  ·
                    refine ⟨1213224704809010322533957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 808816469872673548355971 1213224704809010322533957)
                    ·
                      refine ⟨227479632151689435475117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1213224704809010322533957 227479632151689435475117)
                      ·
                        rfl

theorem cell23_443015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_443015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443015 prefixEnd_443015 := by exact prefixLift 443015
  have htrace : WordTrace (prefixWord ++ tailWord_443015) baseStart_443015 baseEnd_443015 := by
    simpa [prefixWord, tailWord_443015, baseEnd_443015] using wordTrace_append hprefix tailTrace_443015
  have hstable : (prefixWord ++ tailWord_443015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443015).length < 2 ^ (prefixWord ++ tailWord_443015).sum := by decide
  have hdescent : baseEnd_443015 < baseStart_443015 := by decide
  rcases family_descends (prefixWord ++ tailWord_443015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443055 : List Nat := [1, 1, 2, 1, 2, 6, 1, 3, 6]
def baseStart_443055 : Nat := 118140960795 + 443055 * 2 ^ 59
def prefixEnd_443055 : Nat := 4983230072969 + 3 ^ 40 * 443055 * 2
def baseEnd_443055 : Nat := 25277796819763253219437

theorem tailTrace_443055 : CollatzResearch.WordTrace tailWord_443055 prefixEnd_443055 25277796819763253219437 := by
  unfold tailWord_443055
  simp only [CollatzResearch.WordTrace]
  refine ⟨16159543409894877614890619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10773028939929918409927079 16159543409894877614890619)
  ·
    refine ⟨24239315114842316422335929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16159543409894877614890619 24239315114842316422335929)
    ·
      refine ⟨18179486336131737316751947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24239315114842316422335929 18179486336131737316751947)
      ·
        refine ⟨27269229504197605975127921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18179486336131737316751947 27269229504197605975127921)
        ·
          refine ⟨20451922128148204481345941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27269229504197605975127921 20451922128148204481345941)
          ·
            refine ⟨958683849756947085063091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20451922128148204481345941 958683849756947085063091)
            ·
              refine ⟨1438025774635420627594637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958683849756947085063091 1438025774635420627594637)
              ·
                refine ⟨539259665488282735347989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1438025774635420627594637 539259665488282735347989)
                ·
                  refine ⟨25277796819763253219437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 539259665488282735347989 25277796819763253219437)
                  ·
                    rfl

theorem cell23_443055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 6].length) (baseStart_443055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443055 prefixEnd_443055 := by exact prefixLift 443055
  have htrace : WordTrace (prefixWord ++ tailWord_443055) baseStart_443055 baseEnd_443055 := by
    simpa [prefixWord, tailWord_443055, baseEnd_443055] using wordTrace_append hprefix tailTrace_443055
  have hstable : (prefixWord ++ tailWord_443055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443055).length < 2 ^ (prefixWord ++ tailWord_443055).sum := by decide
  have hdescent : baseEnd_443055 < baseStart_443055 := by decide
  rcases family_descends (prefixWord ++ tailWord_443055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443115 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 6, 4]
def baseStart_443115 : Nat := 118140960795 + 443115 * 2 ^ 59
def prefixEnd_443115 : Nat := 4983230072969 + 3 ^ 40 * 443115 * 2
def baseEnd_443115 : Nat := 75843660072379681408219

theorem tailTrace_443115 : CollatzResearch.WordTrace tailWord_443115 prefixEnd_443115 75843660072379681408219 := by
  unfold tailWord_443115
  simp only [CollatzResearch.WordTrace]
  refine ⟨16161731789677507862074799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10774487859785005241383199 16161731789677507862074799)
  ·
    refine ⟨24242597684516261793112199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16161731789677507862074799 24242597684516261793112199)
    ·
      refine ⟨36363896526774392689668299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24242597684516261793112199 36363896526774392689668299)
      ·
        refine ⟨54545844790161589034502449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36363896526774392689668299 54545844790161589034502449)
        ·
          refine ⟨40909383592621191775876837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54545844790161589034502449 40909383592621191775876837)
          ·
            refine ⟨7670509423616473457976907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40909383592621191775876837 7670509423616473457976907)
            ·
              refine ⟨11505764135424710186965361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7670509423616473457976907 11505764135424710186965361)
              ·
                refine ⟨8629323101568532640224021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11505764135424710186965361 8629323101568532640224021)
                ·
                  refine ⟨404499520386024967510501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8629323101568532640224021 404499520386024967510501)
                  ·
                    refine ⟨75843660072379681408219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 404499520386024967510501 75843660072379681408219)
                    ·
                      rfl

theorem cell23_443115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 4].length) (baseStart_443115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443115 prefixEnd_443115 := by exact prefixLift 443115
  have htrace : WordTrace (prefixWord ++ tailWord_443115) baseStart_443115 baseEnd_443115 := by
    simpa [prefixWord, tailWord_443115, baseEnd_443115] using wordTrace_append hprefix tailTrace_443115
  have hstable : (prefixWord ++ tailWord_443115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443115).length < 2 ^ (prefixWord ++ tailWord_443115).sum := by decide
  have hdescent : baseEnd_443115 < baseStart_443115 := by decide
  rcases family_descends (prefixWord ++ tailWord_443115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443122 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_443122 : Nat := 118140960795 + 443122 * 2 ^ 59
def prefixEnd_443122 : Nat := 4983230072969 + 3 ^ 40 * 443122 * 2
def baseEnd_443122 : Nat := 227534574581720516837125

theorem tailTrace_443122 : CollatzResearch.WordTrace tailWord_443122 prefixEnd_443122 227534574581720516837125 := by
  unfold tailWord_443122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4040496775163037014394905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10774658067101432038386413 4040496775163037014394905)
  ·
    refine ⟨3030372581372277760796179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4040496775163037014394905 3030372581372277760796179)
    ·
      refine ⟨4545558872058416641194269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3030372581372277760796179 4545558872058416641194269)
      ·
        refine ⟨1704584577021906240447851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4545558872058416641194269 1704584577021906240447851)
        ·
          refine ⟨2556876865532859360671777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1704584577021906240447851 2556876865532859360671777)
          ·
            refine ⟨1917657649149644520503833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2556876865532859360671777 1917657649149644520503833)
            ·
              refine ⟨1438243236862233390377875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1917657649149644520503833 1438243236862233390377875)
              ·
                refine ⟨2157364855293350085566813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438243236862233390377875 2157364855293350085566813)
                ·
                  refine ⟨809011820735006282087555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2157364855293350085566813 809011820735006282087555)
                  ·
                    refine ⟨1213517731102509423131333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 809011820735006282087555 1213517731102509423131333)
                    ·
                      refine ⟨227534574581720516837125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1213517731102509423131333 227534574581720516837125)
                      ·
                        rfl

theorem cell23_443122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_443122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443122 prefixEnd_443122 := by exact prefixLift 443122
  have htrace : WordTrace (prefixWord ++ tailWord_443122) baseStart_443122 baseEnd_443122 := by
    simpa [prefixWord, tailWord_443122, baseEnd_443122] using wordTrace_append hprefix tailTrace_443122
  have hstable : (prefixWord ++ tailWord_443122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443122).length < 2 ^ (prefixWord ++ tailWord_443122).sum := by decide
  have hdescent : baseEnd_443122 < baseStart_443122 := by decide
  rcases family_descends (prefixWord ++ tailWord_443122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443185 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_443185 : Nat := 118140960795 + 443185 * 2 ^ 59
def prefixEnd_443185 : Nat := 4983230072969 + 3 ^ 40 * 443185 * 2
def baseEnd_443185 : Nat := 227566923862953770349335

theorem tailTrace_443185 : CollatzResearch.WordTrace tailWord_443185 prefixEnd_443185 227566923862953770349335 := by
  unfold tailWord_443185
  simp only [CollatzResearch.WordTrace]
  refine ⟨16164284899423909817123009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10776189932949273211415339 16164284899423909817123009)
  ·
    refine ⟨12123213674567932362842257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16164284899423909817123009 12123213674567932362842257)
    ·
      refine ⟨9092410255925949272131693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12123213674567932362842257 9092410255925949272131693)
      ·
        refine ⟨3409653845972230977049385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9092410255925949272131693 3409653845972230977049385)
        ·
          refine ⟨2557240384479173232787039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3409653845972230977049385 2557240384479173232787039)
          ·
            refine ⟨3835860576718759849180559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2557240384479173232787039 3835860576718759849180559)
            ·
              refine ⟨5753790865078139773770839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835860576718759849180559 5753790865078139773770839)
              ·
                refine ⟨8630686297617209660656259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5753790865078139773770839 8630686297617209660656259)
                ·
                  refine ⟨12946029446425814490984389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8630686297617209660656259 12946029446425814490984389)
                  ·
                    refine ⟨2427380521204840217059573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12946029446425814490984389 2427380521204840217059573)
                    ·
                      refine ⟨227566923862953770349335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2427380521204840217059573 227566923862953770349335)
                      ·
                        rfl

theorem cell23_443185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_443185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443185 prefixEnd_443185 := by exact prefixLift 443185
  have htrace : WordTrace (prefixWord ++ tailWord_443185) baseStart_443185 baseEnd_443185 := by
    simpa [prefixWord, tailWord_443185, baseEnd_443185] using wordTrace_append hprefix tailTrace_443185
  have hstable : (prefixWord ++ tailWord_443185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443185).length < 2 ^ (prefixWord ++ tailWord_443185).sum := by decide
  have hdescent : baseEnd_443185 < baseStart_443185 := by decide
  rcases family_descends (prefixWord ++ tailWord_443185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443189 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_443189 : Nat := 118140960795 + 443189 * 2 ^ 59
def prefixEnd_443189 : Nat := 4983230072969 + 3 ^ 40 * 443189 * 2
def baseEnd_443189 : Nat := 227568977785571754699317

theorem tailTrace_443189 : CollatzResearch.WordTrace tailWord_443189 prefixEnd_443189 227568977785571754699317 := by
  unfold tailWord_443189
  simp only [CollatzResearch.WordTrace]
  refine ⟨16164430791409418500268621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10776287194272945666845747 16164430791409418500268621)
  ·
    refine ⟨6061661546778531937600733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16164430791409418500268621 6061661546778531937600733)
    ·
      refine ⟨2273123080041949476600275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6061661546778531937600733 2273123080041949476600275)
      ·
        refine ⟨3409684620062924214900413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2273123080041949476600275 3409684620062924214900413)
        ·
          refine ⟨1278631732523596580587655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3409684620062924214900413 1278631732523596580587655)
          ·
            refine ⟨1917947598785394870881483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278631732523596580587655 1917947598785394870881483)
            ·
              refine ⟨2876921398178092306322225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1917947598785394870881483 2876921398178092306322225)
              ·
                refine ⟨2157691048633569229741669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2876921398178092306322225 2157691048633569229741669)
                ·
                  refine ⟨404567071618794230576563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2157691048633569229741669 404567071618794230576563)
                  ·
                    refine ⟨606850607428191345864845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 404567071618794230576563 606850607428191345864845)
                    ·
                      refine ⟨227568977785571754699317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 606850607428191345864845 227568977785571754699317)
                      ·
                        rfl

theorem cell23_443189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_443189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443189 prefixEnd_443189 := by exact prefixLift 443189
  have htrace : WordTrace (prefixWord ++ tailWord_443189) baseStart_443189 baseEnd_443189 := by
    simpa [prefixWord, tailWord_443189, baseEnd_443189] using wordTrace_append hprefix tailTrace_443189
  have hstable : (prefixWord ++ tailWord_443189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443189).length < 2 ^ (prefixWord ++ tailWord_443189).sum := by decide
  have hdescent : baseEnd_443189 < baseStart_443189 := by decide
  rcases family_descends (prefixWord ++ tailWord_443189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443205 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 2, 6]
def baseStart_443205 : Nat := 118140960795 + 443205 * 2 ^ 59
def prefixEnd_443205 : Nat := 4983230072969 + 3 ^ 40 * 443205 * 2
def baseEnd_443205 : Nat := 75859064492014564033081

theorem tailTrace_443205 : CollatzResearch.WordTrace tailWord_443205 prefixEnd_443205 75859064492014564033081 := by
  unfold tailWord_443205
  simp only [CollatzResearch.WordTrace]
  refine ⟨16165014359351453232851069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10776676239567635488567379 16165014359351453232851069)
  ·
    refine ⟨6061880384756794962319151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16165014359351453232851069 6061880384756794962319151)
    ·
      refine ⟨9092820577135192443478727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6061880384756794962319151 9092820577135192443478727)
      ·
        refine ⟨13639230865702788665218091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9092820577135192443478727 13639230865702788665218091)
        ·
          refine ⟨20458846298554182997827137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13639230865702788665218091 20458846298554182997827137)
          ·
            refine ⟨15344134723915637248370353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20458846298554182997827137 15344134723915637248370353)
            ·
              refine ⟨11508101042936727936277765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15344134723915637248370353 11508101042936727936277765)
              ·
                refine ⟨2157768945550636488052081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11508101042936727936277765 2157768945550636488052081)
                ·
                  refine ⟨1618326709162977366039061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2157768945550636488052081 1618326709162977366039061)
                  ·
                    refine ⟨75859064492014564033081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1618326709162977366039061 75859064492014564033081)
                    ·
                      rfl

theorem cell23_443205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_443205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443205 prefixEnd_443205 := by exact prefixLift 443205
  have htrace : WordTrace (prefixWord ++ tailWord_443205) baseStart_443205 baseEnd_443205 := by
    simpa [prefixWord, tailWord_443205, baseEnd_443205] using wordTrace_append hprefix tailTrace_443205
  have hstable : (prefixWord ++ tailWord_443205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443205).length < 2 ^ (prefixWord ++ tailWord_443205).sum := by decide
  have hdescent : baseEnd_443205 < baseStart_443205 := by decide
  rcases family_descends (prefixWord ++ tailWord_443205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443223 : List Nat := [1, 1, 3, 2, 4, 3, 2, 1, 2, 1, 3]
def baseStart_443223 : Nat := 118140960795 + 443223 * 2 ^ 59
def prefixEnd_443223 : Nat := 4983230072969 + 3 ^ 40 * 443223 * 2
def baseEnd_443223 : Nat := 227586436127824621674161

theorem tailTrace_443223 : CollatzResearch.WordTrace tailWord_443223 prefixEnd_443223 227586436127824621674161 := by
  unfold tailWord_443223
  simp only [CollatzResearch.WordTrace]
  refine ⟨16165670873286242307006323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10777113915524161538004215 16165670873286242307006323)
  ·
    refine ⟨24248506309929363460509485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16165670873286242307006323 24248506309929363460509485)
    ·
      refine ⟨9093189866223511297691057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24248506309929363460509485 9093189866223511297691057)
      ·
        refine ⟨6819892399667633473268293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9093189866223511297691057 6819892399667633473268293)
        ·
          refine ⟨1278729824937681276237805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6819892399667633473268293 1278729824937681276237805)
          ·
            refine ⟨479523684351630478589177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1278729824937681276237805 479523684351630478589177)
            ·
              refine ⟨359642763263722858941883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479523684351630478589177 359642763263722858941883)
              ·
                refine ⟨539464144895584288412825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359642763263722858941883 539464144895584288412825)
                ·
                  refine ⟨404598108671688216309619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539464144895584288412825 404598108671688216309619)
                  ·
                    refine ⟨606897163007532324464429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 404598108671688216309619 606897163007532324464429)
                    ·
                      refine ⟨227586436127824621674161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 606897163007532324464429 227586436127824621674161)
                      ·
                        rfl

theorem cell23_443223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_443223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443223 prefixEnd_443223 := by exact prefixLift 443223
  have htrace : WordTrace (prefixWord ++ tailWord_443223) baseStart_443223 baseEnd_443223 := by
    simpa [prefixWord, tailWord_443223, baseEnd_443223] using wordTrace_append hprefix tailTrace_443223
  have hstable : (prefixWord ++ tailWord_443223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443223).length < 2 ^ (prefixWord ++ tailWord_443223).sum := by decide
  have hdescent : baseEnd_443223 < baseStart_443223 := by decide
  rcases family_descends (prefixWord ++ tailWord_443223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443269 : List Nat := [1, 3, 1, 1, 3, 4, 1, 4, 5]
def baseStart_443269 : Nat := 118140960795 + 443269 * 2 ^ 59
def prefixEnd_443269 : Nat := 4983230072969 + 3 ^ 40 * 443269 * 2
def baseEnd_443269 : Nat := 25290006248659049077661

theorem tailTrace_443269 : CollatzResearch.WordTrace tailWord_443269 prefixEnd_443269 25290006248659049077661 := by
  unfold tailWord_443269
  simp only [CollatzResearch.WordTrace]
  refine ⟨16167348631119592163180861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10778232420746394775453907 16167348631119592163180861)
  ·
    refine ⟨6062755736669847061192823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16167348631119592163180861 6062755736669847061192823)
    ·
      refine ⟨9094133605004770591789235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6062755736669847061192823 9094133605004770591789235)
      ·
        refine ⟨13641200407507155887683853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9094133605004770591789235 13641200407507155887683853)
        ·
          refine ⟨5115450152815183457881445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13641200407507155887683853 5115450152815183457881445)
          ·
            refine ⟨959146903652846898352771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5115450152815183457881445 959146903652846898352771)
            ·
              refine ⟨1438720355479270347529157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959146903652846898352771 1438720355479270347529157)
              ·
                refine ⟨269760066652363190161717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1438720355479270347529157 269760066652363190161717)
                ·
                  refine ⟨25290006248659049077661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269760066652363190161717 25290006248659049077661)
                  ·
                    rfl

theorem cell23_443269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 5].length) (baseStart_443269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443269 prefixEnd_443269 := by exact prefixLift 443269
  have htrace : WordTrace (prefixWord ++ tailWord_443269) baseStart_443269 baseEnd_443269 := by
    simpa [prefixWord, tailWord_443269, baseEnd_443269] using wordTrace_append hprefix tailTrace_443269
  have hstable : (prefixWord ++ tailWord_443269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443269).length < 2 ^ (prefixWord ++ tailWord_443269).sum := by decide
  have hdescent : baseEnd_443269 < baseStart_443269 := by decide
  rcases family_descends (prefixWord ++ tailWord_443269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443286 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_443286 : Nat := 118140960795 + 443286 * 2 ^ 59
def prefixEnd_443286 : Nat := 4983230072969 + 3 ^ 40 * 443286 * 2
def baseEnd_443286 : Nat := 25290976156561986131819

theorem tailTrace_443286 : CollatzResearch.WordTrace tailWord_443286 prefixEnd_443286 25290976156561986131819 := by
  unfold tailWord_443286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010498042003625254159357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10778645781372002711033141 1010498042003625254159357)
  ·
    refine ⟨378936765751359470309759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1010498042003625254159357 378936765751359470309759)
    ·
      refine ⟨568405148627039205464639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378936765751359470309759 568405148627039205464639)
      ·
        refine ⟨852607722940558808196959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568405148627039205464639 852607722940558808196959)
        ·
          refine ⟨1278911584410838212295439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852607722940558808196959 1278911584410838212295439)
          ·
            refine ⟨1918367376616257318443159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278911584410838212295439 1918367376616257318443159)
            ·
              refine ⟨2877551064924385977664739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918367376616257318443159 2877551064924385977664739)
              ·
                refine ⟨4316326597386578966497109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877551064924385977664739 4316326597386578966497109)
                ·
                  refine ⟨25290976156561986131819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4316326597386578966497109 25290976156561986131819)
                  ·
                    rfl

theorem cell23_443286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_443286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443286 prefixEnd_443286 := by exact prefixLift 443286
  have htrace : WordTrace (prefixWord ++ tailWord_443286) baseStart_443286 baseEnd_443286 := by
    simpa [prefixWord, tailWord_443286, baseEnd_443286] using wordTrace_append hprefix tailTrace_443286
  have hstable : (prefixWord ++ tailWord_443286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443286).length < 2 ^ (prefixWord ++ tailWord_443286).sum := by decide
  have hdescent : baseEnd_443286 < baseStart_443286 := by decide
  rcases family_descends (prefixWord ++ tailWord_443286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443319 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 2, 4, 2]
def baseStart_443319 : Nat := 118140960795 + 443319 * 2 ^ 59
def prefixEnd_443319 : Nat := 4983230072969 + 3 ^ 40 * 443319 * 2
def baseEnd_443319 : Nat := 227635730270656246073719

theorem tailTrace_443319 : CollatzResearch.WordTrace tailWord_443319 prefixEnd_443319 227635730270656246073719 := by
  unfold tailWord_443319
  simp only [CollatzResearch.WordTrace]
  refine ⟨16169172280938450702501011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10779448187292300468334007 16169172280938450702501011)
  ·
    refine ⟨24253758421407676053751517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16169172280938450702501011 24253758421407676053751517)
    ·
      refine ⟨9095159408027878520156819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24253758421407676053751517 9095159408027878520156819)
      ·
        refine ⟨13642739112041817780235229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9095159408027878520156819 13642739112041817780235229)
        ·
          refine ⟨5116027167015681667588211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13642739112041817780235229 5116027167015681667588211)
          ·
            refine ⟨7674040750523522501382317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5116027167015681667588211 7674040750523522501382317)
            ·
              refine ⟨2877765281446320938018369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7674040750523522501382317 2877765281446320938018369)
              ·
                refine ⟨2158323961084740703513777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2877765281446320938018369 2158323961084740703513777)
                ·
                  refine ⟨1618742970813555527635333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2158323961084740703513777 1618742970813555527635333)
                  ·
                    refine ⟨303514307027541661431625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1618742970813555527635333 303514307027541661431625)
                    ·
                      refine ⟨227635730270656246073719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 303514307027541661431625 227635730270656246073719)
                      ·
                        rfl

theorem cell23_443319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 4, 2].length) (baseStart_443319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443319 prefixEnd_443319 := by exact prefixLift 443319
  have htrace : WordTrace (prefixWord ++ tailWord_443319) baseStart_443319 baseEnd_443319 := by
    simpa [prefixWord, tailWord_443319, baseEnd_443319] using wordTrace_append hprefix tailTrace_443319
  have hstable : (prefixWord ++ tailWord_443319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443319).length < 2 ^ (prefixWord ++ tailWord_443319).sum := by decide
  have hdescent : baseEnd_443319 < baseStart_443319 := by decide
  rcases family_descends (prefixWord ++ tailWord_443319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443346 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_443346 : Nat := 118140960795 + 443346 * 2 ^ 59
def prefixEnd_443346 : Nat := 4983230072969 + 3 ^ 40 * 443346 * 2
def baseEnd_443346 : Nat := 75883198082775880145365

theorem tailTrace_443346 : CollatzResearch.WordTrace tailWord_443346 prefixEnd_443346 75883198082775880145365 := by
  unfold tailWord_443346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4042539262960158578433473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10780104701227089542489261 4042539262960158578433473)
  ·
    refine ⟨3031904447220118933825105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4042539262960158578433473 3031904447220118933825105)
    ·
      refine ⟨2273928335415089200368829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3031904447220118933825105 2273928335415089200368829)
      ·
        refine ⟨852723125780658450138311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2273928335415089200368829 852723125780658450138311)
        ·
          refine ⟨1279084688670987675207467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852723125780658450138311 1279084688670987675207467)
          ·
            refine ⟨1918627033006481512811201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279084688670987675207467 1918627033006481512811201)
            ·
              refine ⟨1438970274754861134608401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1918627033006481512811201 1438970274754861134608401)
              ·
                refine ⟨1079227706066145850956301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438970274754861134608401 1079227706066145850956301)
                ·
                  refine ⟨404710389774804694108613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079227706066145850956301 404710389774804694108613)
                  ·
                    refine ⟨75883198082775880145365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 404710389774804694108613 75883198082775880145365)
                    ·
                      rfl

theorem cell23_443346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_443346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443346 prefixEnd_443346 := by exact prefixLift 443346
  have htrace : WordTrace (prefixWord ++ tailWord_443346) baseStart_443346 baseEnd_443346 := by
    simpa [prefixWord, tailWord_443346, baseEnd_443346] using wordTrace_append hprefix tailTrace_443346
  have hstable : (prefixWord ++ tailWord_443346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443346).length < 2 ^ (prefixWord ++ tailWord_443346).sum := by decide
  have hdescent : baseEnd_443346 < baseStart_443346 := by decide
  rcases family_descends (prefixWord ++ tailWord_443346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443372 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 7, 5]
def baseStart_443372 : Nat := 118140960795 + 443372 * 2 ^ 59
def prefixEnd_443372 : Nat := 4983230072969 + 3 ^ 40 * 443372 * 2
def baseEnd_443372 : Nat := 75887648248448179570325

theorem tailTrace_443372 : CollatzResearch.WordTrace tailWord_443372 prefixEnd_443372 75887648248448179570325 := by
  unfold tailWord_443372
  simp only [CollatzResearch.WordTrace]
  refine ⟨8085552674873220377090185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10780736899830960502786913 8085552674873220377090185)
  ·
    refine ⟨6064164506154915282817639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8085552674873220377090185 6064164506154915282817639)
    ·
      refine ⟨9096246759232372924226459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6064164506154915282817639 9096246759232372924226459)
      ·
        refine ⟨13644370138848559386339689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9096246759232372924226459 13644370138848559386339689)
        ·
          refine ⟨10233277604136419539754767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13644370138848559386339689 10233277604136419539754767)
          ·
            refine ⟨15349916406204629309632151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10233277604136419539754767 15349916406204629309632151)
            ·
              refine ⟨23024874609306943964448227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15349916406204629309632151 23024874609306943964448227)
              ·
                refine ⟨34537311913960415946672341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23024874609306943964448227 34537311913960415946672341)
                ·
                  refine ⟨809468247983447248750133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 34537311913960415946672341 809468247983447248750133)
                  ·
                    refine ⟨75887648248448179570325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 809468247983447248750133 75887648248448179570325)
                    ·
                      rfl

theorem cell23_443372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_443372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443372 prefixEnd_443372 := by exact prefixLift 443372
  have htrace : WordTrace (prefixWord ++ tailWord_443372) baseStart_443372 baseEnd_443372 := by
    simpa [prefixWord, tailWord_443372, baseEnd_443372] using wordTrace_append hprefix tailTrace_443372
  have hstable : (prefixWord ++ tailWord_443372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443372).length < 2 ^ (prefixWord ++ tailWord_443372).sum := by decide
  have hdescent : baseEnd_443372 < baseStart_443372 := by decide
  rcases family_descends (prefixWord ++ tailWord_443372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443406 : List Nat := [4, 1, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_443406 : Nat := 118140960795 + 443406 * 2 ^ 59
def prefixEnd_443406 : Nat := 4983230072969 + 3 ^ 40 * 443406 * 2
def baseEnd_443406 : Nat := 75893467695865801895273

theorem tailTrace_443406 : CollatzResearch.WordTrace tailWord_443406 prefixEnd_443406 75893467695865801895273 := by
  unfold tailWord_443406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2021543178952908070114759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10781563621082176373945381 2021543178952908070114759)
  ·
    refine ⟨3032314768429362105172139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2021543178952908070114759 3032314768429362105172139)
    ·
      refine ⟨4548472152644043157758209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3032314768429362105172139 4548472152644043157758209)
      ·
        refine ⟨3411354114483032368318657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4548472152644043157758209 3411354114483032368318657)
        ·
          refine ⟨2558515585862274276238993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3411354114483032368318657 2558515585862274276238993)
          ·
            refine ⟨1918886689396705707179245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2558515585862274276238993 1918886689396705707179245)
            ·
              refine ⟨719582508523764640192217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1918886689396705707179245 719582508523764640192217)
              ·
                refine ⟨539686881392823480144163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719582508523764640192217 539686881392823480144163)
                ·
                  refine ⟨809530322089235220216245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539686881392823480144163 809530322089235220216245)
                  ·
                    refine ⟨75893467695865801895273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 809530322089235220216245 75893467695865801895273)
                    ·
                      rfl

theorem cell23_443406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_443406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443406 prefixEnd_443406 := by exact prefixLift 443406
  have htrace : WordTrace (prefixWord ++ tailWord_443406) baseStart_443406 baseEnd_443406 := by
    simpa [prefixWord, tailWord_443406, baseEnd_443406] using wordTrace_append hprefix tailTrace_443406
  have hstable : (prefixWord ++ tailWord_443406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443406).length < 2 ^ (prefixWord ++ tailWord_443406).sum := by decide
  have hdescent : baseEnd_443406 < baseStart_443406 := by decide
  rcases family_descends (prefixWord ++ tailWord_443406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443409 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 2, 6, 2]
def baseStart_443409 : Nat := 118140960795 + 443409 * 2 ^ 59
def prefixEnd_443409 : Nat := 4983230072969 + 3 ^ 40 * 443409 * 2
def baseEnd_443409 : Nat := 227681943529560893948305

theorem tailTrace_443409 : CollatzResearch.WordTrace tailWord_443409 prefixEnd_443409 227681943529560893948305 := by
  unfold tailWord_443409
  simp only [CollatzResearch.WordTrace]
  refine ⟨16172454850612396073277281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10781636567074930715518187 16172454850612396073277281)
  ·
    refine ⟨12129341137959297054957961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16172454850612396073277281 12129341137959297054957961)
    ·
      refine ⟨9097005853469472791218471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12129341137959297054957961 9097005853469472791218471)
      ·
        refine ⟨13645508780204209186827707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9097005853469472791218471 13645508780204209186827707)
        ·
          refine ⟨20468263170306313780241561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13645508780204209186827707 20468263170306313780241561)
          ·
            refine ⟨15351197377729735335181171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20468263170306313780241561 15351197377729735335181171)
            ·
              refine ⟨23026796066594603002771757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15351197377729735335181171 23026796066594603002771757)
              ·
                refine ⟨8635048524972976126039409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23026796066594603002771757 8635048524972976126039409)
                ·
                  refine ⟨6476286393729732094529557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8635048524972976126039409 6476286393729732094529557)
                  ·
                    refine ⟨303575924706081191931073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6476286393729732094529557 303575924706081191931073)
                    ·
                      refine ⟨227681943529560893948305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 303575924706081191931073 227681943529560893948305)
                      ·
                        rfl

theorem cell23_443409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 6, 2].length) (baseStart_443409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443409 prefixEnd_443409 := by exact prefixLift 443409
  have htrace : WordTrace (prefixWord ++ tailWord_443409) baseStart_443409 baseEnd_443409 := by
    simpa [prefixWord, tailWord_443409, baseEnd_443409] using wordTrace_append hprefix tailTrace_443409
  have hstable : (prefixWord ++ tailWord_443409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443409).length < 2 ^ (prefixWord ++ tailWord_443409).sum := by decide
  have hdescent : baseEnd_443409 < baseStart_443409 := by decide
  rcases family_descends (prefixWord ++ tailWord_443409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443413 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 2, 3, 2]
def baseStart_443413 : Nat := 118140960795 + 443413 * 2 ^ 59
def prefixEnd_443413 : Nat := 4983230072969 + 3 ^ 40 * 443413 * 2
def baseEnd_443413 : Nat := 227683997452178878298287

theorem tailTrace_443413 : CollatzResearch.WordTrace tailWord_443413 prefixEnd_443413 227683997452178878298287 := by
  unfold tailWord_443413
  simp only [CollatzResearch.WordTrace]
  refine ⟨16172600742597904756422893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10781733828398603170948595 16172600742597904756422893)
  ·
    refine ⟨6064725278474214283658585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16172600742597904756422893 6064725278474214283658585)
    ·
      refine ⟨4548543958855660712743939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6064725278474214283658585 4548543958855660712743939)
      ·
        refine ⟨6822815938283491069115909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4548543958855660712743939 6822815938283491069115909)
        ·
          refine ⟨1279277988428154575459233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6822815938283491069115909 1279277988428154575459233)
          ·
            refine ⟨959458491321115931594425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1279277988428154575459233 959458491321115931594425)
            ·
              refine ⟨719593868490836948695819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 959458491321115931594425 719593868490836948695819)
              ·
                refine ⟨1079390802736255423043729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719593868490836948695819 1079390802736255423043729)
                ·
                  refine ⟨809543102052191567282797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1079390802736255423043729 809543102052191567282797)
                  ·
                    refine ⟨303578663269571837731049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 809543102052191567282797 303578663269571837731049)
                    ·
                      refine ⟨227683997452178878298287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 303578663269571837731049 227683997452178878298287)
                      ·
                        rfl

theorem cell23_443413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_443413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443413 prefixEnd_443413 := by exact prefixLift 443413
  have htrace : WordTrace (prefixWord ++ tailWord_443413) baseStart_443413 baseEnd_443413 := by
    simpa [prefixWord, tailWord_443413, baseEnd_443413] using wordTrace_append hprefix tailTrace_443413
  have hstable : (prefixWord ++ tailWord_443413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443413).length < 2 ^ (prefixWord ++ tailWord_443413).sum := by decide
  have hdescent : baseEnd_443413 < baseStart_443413 := by decide
  rcases family_descends (prefixWord ++ tailWord_443413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443432 : List Nat := [2, 1, 5, 15]
def baseStart_443432 : Nat := 118140960795 + 443432 * 2 ^ 59
def prefixEnd_443432 : Nat := 4983230072969 + 3 ^ 40 * 443432 * 2
def baseEnd_443432 : Nat := 104112370180436352977

theorem tailTrace_443432 : CollatzResearch.WordTrace tailWord_443432 prefixEnd_443432 104112370180436352977 := by
  unfold tailWord_443432
  simp only [CollatzResearch.WordTrace]
  refine ⟨8086646864764535500682275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10782195819686047334243033 8086646864764535500682275)
  ·
    refine ⟨12129970297146803251023413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8086646864764535500682275 12129970297146803251023413)
    ·
      refine ⟨1137184715357512804783445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12129970297146803251023413 1137184715357512804783445)
      ·
        refine ⟨104112370180436352977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 1137184715357512804783445 104112370180436352977)
        ·
          rfl

theorem cell23_443432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 15].length) (baseStart_443432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443432 prefixEnd_443432 := by exact prefixLift 443432
  have htrace : WordTrace (prefixWord ++ tailWord_443432) baseStart_443432 baseEnd_443432 := by
    simpa [prefixWord, tailWord_443432, baseEnd_443432] using wordTrace_append hprefix tailTrace_443432
  have hstable : (prefixWord ++ tailWord_443432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443432).length < 2 ^ (prefixWord ++ tailWord_443432).sum := by decide
  have hdescent : baseEnd_443432 < baseStart_443432 := by decide
  rcases family_descends (prefixWord ++ tailWord_443432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443436 : List Nat := [2, 2, 1, 1, 1, 2, 6, 2, 2, 4]
def baseStart_443436 : Nat := 118140960795 + 443436 * 2 ^ 59
def prefixEnd_443436 : Nat := 4983230072969 + 3 ^ 40 * 443436 * 2
def baseEnd_443436 : Nat := 75898602502410762770227

theorem tailTrace_443436 : CollatzResearch.WordTrace tailWord_443436 prefixEnd_443436 75898602502410762770227 := by
  unfold tailWord_443436
  simp only [CollatzResearch.WordTrace]
  refine ⟨8086719810757289842255081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10782293081009719789673441 8086719810757289842255081)
  ·
    refine ⟨6065039858067967381691311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8086719810757289842255081 6065039858067967381691311)
    ·
      refine ⟨9097559787101951072536967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6065039858067967381691311 9097559787101951072536967)
      ·
        refine ⟨13646339680652926608805451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9097559787101951072536967 13646339680652926608805451)
        ·
          refine ⟨20469509520979389913208177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13646339680652926608805451 20469509520979389913208177)
          ·
            refine ⟨15352132140734542434906133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20469509520979389913208177 15352132140734542434906133)
            ·
              refine ⟨719631194096931676636225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15352132140734542434906133 719631194096931676636225)
              ·
                refine ⟨539723395572698757477169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719631194096931676636225 539723395572698757477169)
                ·
                  refine ⟨404792546679524068107877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539723395572698757477169 404792546679524068107877)
                  ·
                    refine ⟨75898602502410762770227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 404792546679524068107877 75898602502410762770227)
                    ·
                      rfl

theorem cell23_443436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_443436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443436 prefixEnd_443436 := by exact prefixLift 443436
  have htrace : WordTrace (prefixWord ++ tailWord_443436) baseStart_443436 baseEnd_443436 := by
    simpa [prefixWord, tailWord_443436, baseEnd_443436] using wordTrace_append hprefix tailTrace_443436
  have hstable : (prefixWord ++ tailWord_443436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443436).length < 2 ^ (prefixWord ++ tailWord_443436).sum := by decide
  have hdescent : baseEnd_443436 < baseStart_443436 := by decide
  rcases family_descends (prefixWord ++ tailWord_443436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443449 : List Nat := [1, 2, 1, 5, 2, 1, 3, 8]
def baseStart_443449 : Nat := 118140960795 + 443449 * 2 ^ 59
def prefixEnd_443449 : Nat := 4983230072969 + 3 ^ 40 * 443449 * 2
def baseEnd_443449 : Nat := 8433425287249656942523

theorem tailTrace_443449 : CollatzResearch.WordTrace tailWord_443449 prefixEnd_443449 8433425287249656942523 := by
  unfold tailWord_443449
  simp only [CollatzResearch.WordTrace]
  refine ⟨16173913770467482904733401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10782609180311655269822267 16173913770467482904733401)
  ·
    refine ⟨12130435327850612178550051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16173913770467482904733401 12130435327850612178550051)
    ·
      refine ⟨18195652991775918267825077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12130435327850612178550051 18195652991775918267825077)
      ·
        refine ⟨1705842467978992337608601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18195652991775918267825077 1705842467978992337608601)
        ·
          refine ⟨1279381850984244253206451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1705842467978992337608601 1279381850984244253206451)
          ·
            refine ⟨1919072776476366379809677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279381850984244253206451 1919072776476366379809677)
            ·
              refine ⟨719652291178637392428629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1919072776476366379809677 719652291178637392428629)
              ·
                refine ⟨8433425287249656942523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 719652291178637392428629 8433425287249656942523)
                ·
                  rfl

theorem cell23_443449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 8].length) (baseStart_443449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443449 prefixEnd_443449 := by exact prefixLift 443449
  have htrace : WordTrace (prefixWord ++ tailWord_443449) baseStart_443449 baseEnd_443449 := by
    simpa [prefixWord, tailWord_443449, baseEnd_443449] using wordTrace_append hprefix tailTrace_443449
  have hstable : (prefixWord ++ tailWord_443449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443449).length < 2 ^ (prefixWord ++ tailWord_443449).sum := by decide
  have hdescent : baseEnd_443449 < baseStart_443449 := by decide
  rcases family_descends (prefixWord ++ tailWord_443449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443476 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_443476 : Nat := 118140960795 + 443476 * 2 ^ 59
def prefixEnd_443476 : Nat := 4983230072969 + 3 ^ 40 * 443476 * 2
def baseEnd_443476 : Nat := 227716346733412131810497

theorem tailTrace_443476 : CollatzResearch.WordTrace tailWord_443476 prefixEnd_443476 227716346733412131810497 := by
  unfold tailWord_443476
  simp only [CollatzResearch.WordTrace]
  refine ⟨8087449270684833257983141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10783265694246444343977521 8087449270684833257983141)
  ·
    refine ⟨1516396738253406235871839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8087449270684833257983141 1516396738253406235871839)
    ·
      refine ⟨2274595107380109353807759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1516396738253406235871839 2274595107380109353807759)
      ·
        refine ⟨3411892661070164030711639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274595107380109353807759 3411892661070164030711639)
        ·
          refine ⟨5117838991605246046067459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3411892661070164030711639 5117838991605246046067459)
          ·
            refine ⟨7676758487407869069101189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5117838991605246046067459 7676758487407869069101189)
            ·
              refine ⟨1439392216388975450456473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7676758487407869069101189 1439392216388975450456473)
              ·
                refine ⟨1079544162291731587842355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439392216388975450456473 1079544162291731587842355)
                ·
                  refine ⟨1619316243437597381763533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079544162291731587842355 1619316243437597381763533)
                  ·
                    refine ⟨607243591289099018161325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1619316243437597381763533 607243591289099018161325)
                    ·
                      refine ⟨227716346733412131810497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 607243591289099018161325 227716346733412131810497)
                      ·
                        rfl

theorem cell23_443476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_443476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443476 prefixEnd_443476 := by exact prefixLift 443476
  have htrace : WordTrace (prefixWord ++ tailWord_443476) baseStart_443476 baseEnd_443476 := by
    simpa [prefixWord, tailWord_443476, baseEnd_443476] using wordTrace_append hprefix tailTrace_443476
  have hstable : (prefixWord ++ tailWord_443476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443476).length < 2 ^ (prefixWord ++ tailWord_443476).sum := by decide
  have hdescent : baseEnd_443476 < baseStart_443476 := by decide
  rcases family_descends (prefixWord ++ tailWord_443476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443549 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_443549 : Nat := 118140960795 + 443549 * 2 ^ 59
def prefixEnd_443549 : Nat := 4983230072969 + 3 ^ 40 * 443549 * 2
def baseEnd_443549 : Nat := 227753830821190346197661

theorem tailTrace_443549 : CollatzResearch.WordTrace tailWord_443549 prefixEnd_443549 227753830821190346197661 := by
  unfold tailWord_443549
  simp only [CollatzResearch.WordTrace]
  refine ⟨16177561070105199983373701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10785040713403466655582467 16177561070105199983373701)
  ·
    refine ⟨3033292700644724996882569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16177561070105199983373701 3033292700644724996882569)
    ·
      refine ⟨2274969525483543747661927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3033292700644724996882569 2274969525483543747661927)
      ·
        refine ⟨3412454288225315621492891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274969525483543747661927 3412454288225315621492891)
        ·
          refine ⟨5118681432337973432239337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3412454288225315621492891 5118681432337973432239337)
          ·
            refine ⟨3839011074253480074179503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5118681432337973432239337 3839011074253480074179503)
            ·
              refine ⟨5758516611380220111269255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839011074253480074179503 5758516611380220111269255)
              ·
                refine ⟨8637774917070330166903883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5758516611380220111269255 8637774917070330166903883)
                ·
                  refine ⟨12956662375605495250355825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8637774917070330166903883 12956662375605495250355825)
                  ·
                    refine ⟨9717496781704121437766869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12956662375605495250355825 9717496781704121437766869)
                    ·
                      refine ⟨227753830821190346197661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9717496781704121437766869 227753830821190346197661)
                      ·
                        rfl

theorem cell23_443549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_443549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443549 prefixEnd_443549 := by exact prefixLift 443549
  have htrace : WordTrace (prefixWord ++ tailWord_443549) baseStart_443549 baseEnd_443549 := by
    simpa [prefixWord, tailWord_443549, baseEnd_443549] using wordTrace_append hprefix tailTrace_443549
  have hstable : (prefixWord ++ tailWord_443549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443549).length < 2 ^ (prefixWord ++ tailWord_443549).sum := by decide
  have hdescent : baseEnd_443549 < baseStart_443549 := by decide
  rcases family_descends (prefixWord ++ tailWord_443549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443556 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 7]
def baseStart_443556 : Nat := 118140960795 + 443556 * 2 ^ 59
def prefixEnd_443556 : Nat := 4983230072969 + 3 ^ 40 * 443556 * 2
def baseEnd_443556 : Nat := 25306380576196868756681

theorem tailTrace_443556 : CollatzResearch.WordTrace tailWord_443556 prefixEnd_443556 25306380576196868756681 := by
  unfold tailWord_443556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8088908190539920089439261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10785210920719893452585681 8088908190539920089439261)
  ·
    refine ⟨3033340571452470033539723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8088908190539920089439261 3033340571452470033539723)
    ·
      refine ⟨4550010857178705050309585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3033340571452470033539723 4550010857178705050309585)
      ·
        refine ⟨3412508142884028787732189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4550010857178705050309585 3412508142884028787732189)
        ·
          refine ⟨1279690553581510795399571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3412508142884028787732189 1279690553581510795399571)
          ·
            refine ⟨1919535830372266193099357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279690553581510795399571 1919535830372266193099357)
            ·
              refine ⟨719825936389599822412259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1919535830372266193099357 719825936389599822412259)
              ·
                refine ⟨1079738904584399733618389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719825936389599822412259 1079738904584399733618389)
                ·
                  refine ⟨25306380576196868756681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1079738904584399733618389 25306380576196868756681)
                  ·
                    rfl

theorem cell23_443556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_443556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443556 prefixEnd_443556 := by exact prefixLift 443556
  have htrace : WordTrace (prefixWord ++ tailWord_443556) baseStart_443556 baseEnd_443556 := by
    simpa [prefixWord, tailWord_443556, baseEnd_443556] using wordTrace_append hprefix tailTrace_443556
  have hstable : (prefixWord ++ tailWord_443556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443556).length < 2 ^ (prefixWord ++ tailWord_443556).sum := by decide
  have hdescent : baseEnd_443556 < baseStart_443556 := by decide
  rcases family_descends (prefixWord ++ tailWord_443556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443576 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 4, 5, 2]
def baseStart_443576 : Nat := 118140960795 + 443576 * 2 ^ 59
def prefixEnd_443576 : Nat := 4983230072969 + 3 ^ 40 * 443576 * 2
def baseEnd_443576 : Nat := 227767694798861740560037

theorem tailTrace_443576 : CollatzResearch.WordTrace tailWord_443576 prefixEnd_443576 227767694798861740560037 := by
  unfold tailWord_443576
  simp only [CollatzResearch.WordTrace]
  refine ⟨8089272920503691797303291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10785697227338255729737721 8089272920503691797303291)
  ·
    refine ⟨12133909380755537695954937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8089272920503691797303291 12133909380755537695954937)
    ·
      refine ⟨9100432035566653271966203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12133909380755537695954937 9100432035566653271966203)
      ·
        refine ⟨13650648053349979907949305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9100432035566653271966203 13650648053349979907949305)
        ·
          refine ⟨10237986040012484930961979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13650648053349979907949305 10237986040012484930961979)
          ·
            refine ⟨15356979060018727396442969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10237986040012484930961979 15356979060018727396442969)
            ·
              refine ⟨11517734295014045547332227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15356979060018727396442969 11517734295014045547332227)
              ·
                refine ⟨17276601442521068320998341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11517734295014045547332227 17276601442521068320998341)
                ·
                  refine ⟨3239362770472700310187189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17276601442521068320998341 3239362770472700310187189)
                  ·
                    refine ⟨303690259731815654080049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3239362770472700310187189 303690259731815654080049)
                    ·
                      refine ⟨227767694798861740560037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 303690259731815654080049 227767694798861740560037)
                      ·
                        rfl

theorem cell23_443576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 5, 2].length) (baseStart_443576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443576 prefixEnd_443576 := by exact prefixLift 443576
  have htrace : WordTrace (prefixWord ++ tailWord_443576) baseStart_443576 baseEnd_443576 := by
    simpa [prefixWord, tailWord_443576, baseEnd_443576] using wordTrace_append hprefix tailTrace_443576
  have hstable : (prefixWord ++ tailWord_443576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443576).length < 2 ^ (prefixWord ++ tailWord_443576).sum := by decide
  have hdescent : baseEnd_443576 < baseStart_443576 := by decide
  rcases family_descends (prefixWord ++ tailWord_443576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443609 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 1, 5, 5]
def baseStart_443609 : Nat := 118140960795 + 443609 * 2 ^ 59
def prefixEnd_443609 : Nat := 4983230072969 + 3 ^ 40 * 443609 * 2
def baseEnd_443609 : Nat := 227784639660460111447385

theorem tailTrace_443609 : CollatzResearch.WordTrace tailWord_443609 prefixEnd_443609 227784639660460111447385 := by
  unfold tailWord_443609
  simp only [CollatzResearch.WordTrace]
  refine ⟨16179749449887830230557881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10786499633258553487038587 16179749449887830230557881)
  ·
    refine ⟨12134812087415872672918411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16179749449887830230557881 12134812087415872672918411)
    ·
      refine ⟨18202218131123809009377617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12134812087415872672918411 18202218131123809009377617)
      ·
        refine ⟨13651663598342856757033213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18202218131123809009377617 13651663598342856757033213)
        ·
          refine ⟨5119373849378571283887455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13651663598342856757033213 5119373849378571283887455)
          ·
            refine ⟨7679060774067856925831183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5119373849378571283887455 7679060774067856925831183)
            ·
              refine ⟨11518591161101785388746775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7679060774067856925831183 11518591161101785388746775)
              ·
                refine ⟨17277886741652678083120163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11518591161101785388746775 17277886741652678083120163)
                ·
                  refine ⟨25916830112479017124680245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17277886741652678083120163 25916830112479017124680245)
                  ·
                    refine ⟨2429702823044907855438773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25916830112479017124680245 2429702823044907855438773)
                    ·
                      refine ⟨227784639660460111447385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2429702823044907855438773 227784639660460111447385)
                      ·
                        rfl

theorem cell23_443609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_443609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443609 prefixEnd_443609 := by exact prefixLift 443609
  have htrace : WordTrace (prefixWord ++ tailWord_443609) baseStart_443609 baseEnd_443609 := by
    simpa [prefixWord, tailWord_443609, baseEnd_443609] using wordTrace_append hprefix tailTrace_443609
  have hstable : (prefixWord ++ tailWord_443609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443609).length < 2 ^ (prefixWord ++ tailWord_443609).sum := by decide
  have hdescent : baseEnd_443609 < baseStart_443609 := by decide
  rcases family_descends (prefixWord ++ tailWord_443609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443676 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 5, 5]
def baseStart_443676 : Nat := 118140960795 + 443676 * 2 ^ 59
def prefixEnd_443676 : Nat := 4983230072969 + 3 ^ 40 * 443676 * 2
def baseEnd_443676 : Nat := 75939680954770449769859

theorem tailTrace_443676 : CollatzResearch.WordTrace tailWord_443676 prefixEnd_443676 75939680954770449769859 := by
  unfold tailWord_443676
  simp only [CollatzResearch.WordTrace]
  refine ⟨8091096570322550336623441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10788128760430067115497921 8091096570322550336623441)
  ·
    refine ⟨6068322427741912752467581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8091096570322550336623441 6068322427741912752467581)
    ·
      refine ⟨2275620910403217282175343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6068322427741912752467581 2275620910403217282175343)
      ·
        refine ⟨3413431365604825923263015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2275620910403217282175343 3413431365604825923263015)
        ·
          refine ⟨5120147048407238884894523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3413431365604825923263015 5120147048407238884894523)
          ·
            refine ⟨7680220572610858327341785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5120147048407238884894523 7680220572610858327341785)
            ·
              refine ⟨5760165429458143745506339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7680220572610858327341785 5760165429458143745506339)
              ·
                refine ⟨8640248144187215618259509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5760165429458143745506339 8640248144187215618259509)
                ·
                  refine ⟨810023263517551464211829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8640248144187215618259509 810023263517551464211829)
                  ·
                    refine ⟨75939680954770449769859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 810023263517551464211829 75939680954770449769859)
                    ·
                      rfl

theorem cell23_443676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_443676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443676 prefixEnd_443676 := by exact prefixLift 443676
  have htrace : WordTrace (prefixWord ++ tailWord_443676) baseStart_443676 baseEnd_443676 := by
    simpa [prefixWord, tailWord_443676, baseEnd_443676] using wordTrace_append hprefix tailTrace_443676
  have hstable : (prefixWord ++ tailWord_443676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443676).length < 2 ^ (prefixWord ++ tailWord_443676).sum := by decide
  have hdescent : baseEnd_443676 < baseStart_443676 := by decide
  rcases family_descends (prefixWord ++ tailWord_443676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443680 : List Nat := [2, 1, 1, 5, 3, 1, 3, 1, 6]
def baseStart_443680 : Nat := 118140960795 + 443680 * 2 ^ 59
def prefixEnd_443680 : Nat := 4983230072969 + 3 ^ 40 * 443680 * 2
def baseEnd_443680 : Nat := 25313455198547703739951

theorem tailTrace_443680 : CollatzResearch.WordTrace tailWord_443680 prefixEnd_443680 25313455198547703739951 := by
  unfold tailWord_443680
  simp only [CollatzResearch.WordTrace]
  refine ⟨8091169516315304678196247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10788226021753739570928329 8091169516315304678196247)
  ·
    refine ⟨12136754274472957017294371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8091169516315304678196247 12136754274472957017294371)
    ·
      refine ⟨18205131411709435525941557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12136754274472957017294371 18205131411709435525941557)
      ·
        refine ⟨1706731069847759580557021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18205131411709435525941557 1706731069847759580557021)
        ·
          refine ⟨640024151192909842708883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1706731069847759580557021 640024151192909842708883)
          ·
            refine ⟨960036226789364764063325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640024151192909842708883 960036226789364764063325)
            ·
              refine ⟨360013585046011786523747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960036226789364764063325 360013585046011786523747)
              ·
                refine ⟨540020377569017679785621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360013585046011786523747 540020377569017679785621)
                ·
                  refine ⟨25313455198547703739951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 540020377569017679785621 25313455198547703739951)
                  ·
                    rfl

theorem cell23_443680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 6].length) (baseStart_443680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443680 prefixEnd_443680 := by exact prefixLift 443680
  have htrace : WordTrace (prefixWord ++ tailWord_443680) baseStart_443680 baseEnd_443680 := by
    simpa [prefixWord, tailWord_443680, baseEnd_443680] using wordTrace_append hprefix tailTrace_443680
  have hstable : (prefixWord ++ tailWord_443680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443680).length < 2 ^ (prefixWord ++ tailWord_443680).sum := by decide
  have hdescent : baseEnd_443680 < baseStart_443680 := by decide
  rcases family_descends (prefixWord ++ tailWord_443680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443683 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 1, 5, 2]
def baseStart_443683 : Nat := 118140960795 + 443683 * 2 ^ 59
def prefixEnd_443683 : Nat := 4983230072969 + 3 ^ 40 * 443683 * 2
def baseEnd_443683 : Nat := 227822637228892821922045

theorem tailTrace_443683 : CollatzResearch.WordTrace tailWord_443683 prefixEnd_443683 227822637228892821922045 := by
  unfold tailWord_443683
  simp only [CollatzResearch.WordTrace]
  refine ⟨16182448451619740868751703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10788298967746493912501135 16182448451619740868751703)
  ·
    refine ⟨24273672677429611303127555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16182448451619740868751703 24273672677429611303127555)
    ·
      refine ⟨36410509016144416954691333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24273672677429611303127555 36410509016144416954691333)
      ·
        refine ⟨6826970440527078179004625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36410509016144416954691333 6826970440527078179004625)
        ·
          refine ⟨5120227830395308634253469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6826970440527078179004625 5120227830395308634253469)
          ·
            refine ⟨1920085436398240737845051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5120227830395308634253469 1920085436398240737845051)
            ·
              refine ⟨2880128154597361106767577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1920085436398240737845051 2880128154597361106767577)
              ·
                refine ⟨2160096115948020830075683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2880128154597361106767577 2160096115948020830075683)
                ·
                  refine ⟨3240144173922031245113525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160096115948020830075683 3240144173922031245113525)
                  ·
                    refine ⟨303763516305190429229393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3240144173922031245113525 303763516305190429229393)
                    ·
                      refine ⟨227822637228892821922045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 303763516305190429229393 227822637228892821922045)
                      ·
                        rfl

theorem cell23_443683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_443683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443683 prefixEnd_443683 := by exact prefixLift 443683
  have htrace : WordTrace (prefixWord ++ tailWord_443683) baseStart_443683 baseEnd_443683 := by
    simpa [prefixWord, tailWord_443683, baseEnd_443683] using wordTrace_append hprefix tailTrace_443683
  have hstable : (prefixWord ++ tailWord_443683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443683).length < 2 ^ (prefixWord ++ tailWord_443683).sum := by decide
  have hdescent : baseEnd_443683 < baseStart_443683 := by decide
  rcases family_descends (prefixWord ++ tailWord_443683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443700 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_443700 : Nat := 118140960795 + 443700 * 2 ^ 59
def prefixEnd_443700 : Nat := 4983230072969 + 3 ^ 40 * 443700 * 2
def baseEnd_443700 : Nat := 227831366400019255409467

theorem tailTrace_443700 : CollatzResearch.WordTrace tailWord_443700 prefixEnd_443700 227831366400019255409467 := by
  unfold tailWord_443700
  simp only [CollatzResearch.WordTrace]
  refine ⟨8091534246279076386060277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10788712328372101848080369 8091534246279076386060277)
  ·
    refine ⟨758581335588663411193151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8091534246279076386060277 758581335588663411193151)
    ·
      refine ⟨1137872003382995116789727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 758581335588663411193151 1137872003382995116789727)
      ·
        refine ⟨1706808005074492675184591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137872003382995116789727 1706808005074492675184591)
        ·
          refine ⟨2560212007611739012776887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1706808005074492675184591 2560212007611739012776887)
          ·
            refine ⟨3840318011417608519165331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2560212007611739012776887 3840318011417608519165331)
            ·
              refine ⟨5760477017126412778747997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3840318011417608519165331 5760477017126412778747997)
              ·
                refine ⟨2160178881422404792030499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5760477017126412778747997 2160178881422404792030499)
                ·
                  refine ⟨3240268322133607188045749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160178881422404792030499 3240268322133607188045749)
                  ·
                    refine ⟨303775155200025673879289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3240268322133607188045749 303775155200025673879289)
                    ·
                      refine ⟨227831366400019255409467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 303775155200025673879289 227831366400019255409467)
                      ·
                        rfl

theorem cell23_443700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_443700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443700 prefixEnd_443700 := by exact prefixLift 443700
  have htrace : WordTrace (prefixWord ++ tailWord_443700) baseStart_443700 baseEnd_443700 := by
    simpa [prefixWord, tailWord_443700, baseEnd_443700] using wordTrace_append hprefix tailTrace_443700
  have hstable : (prefixWord ++ tailWord_443700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443700).length < 2 ^ (prefixWord ++ tailWord_443700).sum := by decide
  have hdescent : baseEnd_443700 < baseStart_443700 := by decide
  rcases family_descends (prefixWord ++ tailWord_443700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443706 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 3, 6]
def baseStart_443706 : Nat := 118140960795 + 443706 * 2 ^ 59
def prefixEnd_443706 : Nat := 4983230072969 + 3 ^ 40 * 443706 * 2
def baseEnd_443706 : Nat := 75944815761315410644813

theorem tailTrace_443706 : CollatzResearch.WordTrace tailWord_443706 prefixEnd_443706 75944815761315410644813 := by
  unfold tailWord_443706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4045821832634103949209743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10788858220357610531225981 4045821832634103949209743)
  ·
    refine ⟨6068732748951155923814615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4045821832634103949209743 6068732748951155923814615)
    ·
      refine ⟨9103099123426733885721923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6068732748951155923814615 9103099123426733885721923)
      ·
        refine ⟨13654648685140100828582885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9103099123426733885721923 13654648685140100828582885)
        ·
          refine ⟨2560246628463768905359291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13654648685140100828582885 2560246628463768905359291)
          ·
            refine ⟨3840369942695653358038937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2560246628463768905359291 3840369942695653358038937)
            ·
              refine ⟨2880277457021740018529203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3840369942695653358038937 2880277457021740018529203)
              ·
                refine ⟨4320416185532610027793805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2880277457021740018529203 4320416185532610027793805)
                ·
                  refine ⟨1620156069574728760422677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4320416185532610027793805 1620156069574728760422677)
                  ·
                    refine ⟨75944815761315410644813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1620156069574728760422677 75944815761315410644813)
                    ·
                      rfl

theorem cell23_443706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_443706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443706 prefixEnd_443706 := by exact prefixLift 443706
  have htrace : WordTrace (prefixWord ++ tailWord_443706) baseStart_443706 baseEnd_443706 := by
    simpa [prefixWord, tailWord_443706, baseEnd_443706] using wordTrace_append hprefix tailTrace_443706
  have hstable : (prefixWord ++ tailWord_443706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443706).length < 2 ^ (prefixWord ++ tailWord_443706).sum := by decide
  have hdescent : baseEnd_443706 < baseStart_443706 := by decide
  rcases family_descends (prefixWord ++ tailWord_443706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443718 : List Nat := [6, 1, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_443718 : Nat := 118140960795 + 443718 * 2 ^ 59
def prefixEnd_443718 : Nat := 4983230072969 + 3 ^ 40 * 443718 * 2
def baseEnd_443718 : Nat := 75946869683933394994795

theorem tailTrace_443718 : CollatzResearch.WordTrace tailWord_443718 prefixEnd_443718 75946869683933394994795 := by
  unfold tailWord_443718
  simp only [CollatzResearch.WordTrace]
  refine ⟨505741406452904432696119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10789150004328627897517205 505741406452904432696119)
  ·
    refine ⟨758612109679356649044179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 505741406452904432696119 758612109679356649044179)
    ·
      refine ⟨1137918164519034973566269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 758612109679356649044179 1137918164519034973566269)
      ·
        refine ⟨426719311694638115087351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1137918164519034973566269 426719311694638115087351)
        ·
          refine ⟨640078967541957172631027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426719311694638115087351 640078967541957172631027)
          ·
            refine ⟨960118451312935758946541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640078967541957172631027 960118451312935758946541)
            ·
              refine ⟨360044419242350909604953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960118451312935758946541 360044419242350909604953)
              ·
                refine ⟨270033314431763182203715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360044419242350909604953 270033314431763182203715)
                ·
                  refine ⟨405049971647644773305573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270033314431763182203715 405049971647644773305573)
                  ·
                    refine ⟨75946869683933394994795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 405049971647644773305573 75946869683933394994795)
                    ·
                      rfl

theorem cell23_443718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_443718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443718 prefixEnd_443718 := by exact prefixLift 443718
  have htrace : WordTrace (prefixWord ++ tailWord_443718) baseStart_443718 baseEnd_443718 := by
    simpa [prefixWord, tailWord_443718, baseEnd_443718] using wordTrace_append hprefix tailTrace_443718
  have hstable : (prefixWord ++ tailWord_443718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443718).length < 2 ^ (prefixWord ++ tailWord_443718).sum := by decide
  have hdescent : baseEnd_443718 < baseStart_443718 := by decide
  rcases family_descends (prefixWord ++ tailWord_443718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443724 : List Nat := [2, 2, 1, 3, 2, 3, 3, 2, 1, 1, 3]
def baseStart_443724 : Nat := 118140960795 + 443724 * 2 ^ 59
def prefixEnd_443724 : Nat := 4983230072969 + 3 ^ 40 * 443724 * 2
def baseEnd_443724 : Nat := 227843689935727161509357

theorem tailTrace_443724 : CollatzResearch.WordTrace tailWord_443724 prefixEnd_443724 227843689935727161509357 := by
  unfold tailWord_443724
  simp only [CollatzResearch.WordTrace]
  refine ⟨8091971922235602435497113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10789295896314136580662817 8091971922235602435497113)
  ·
    refine ⟨6068978941676701826622835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8091971922235602435497113 6068978941676701826622835)
    ·
      refine ⟨9103468412515052739934253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6068978941676701826622835 9103468412515052739934253)
      ·
        refine ⟨3413800654693144777475345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9103468412515052739934253 3413800654693144777475345)
        ·
          refine ⟨2560350491019858583106509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3413800654693144777475345 2560350491019858583106509)
          ·
            refine ⟨960131434132446968664941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2560350491019858583106509 960131434132446968664941)
            ·
              refine ⟨360049287799667613249353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960131434132446968664941 360049287799667613249353)
              ·
                refine ⟨270036965849750709937015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360049287799667613249353 270036965849750709937015)
                ·
                  refine ⟨405055448774626064905523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270036965849750709937015 405055448774626064905523)
                  ·
                    refine ⟨607583173161939097358285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 405055448774626064905523 607583173161939097358285)
                    ·
                      refine ⟨227843689935727161509357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 607583173161939097358285 227843689935727161509357)
                      ·
                        rfl

theorem cell23_443724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_443724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443724 prefixEnd_443724 := by exact prefixLift 443724
  have htrace : WordTrace (prefixWord ++ tailWord_443724) baseStart_443724 baseEnd_443724 := by
    simpa [prefixWord, tailWord_443724, baseEnd_443724] using wordTrace_append hprefix tailTrace_443724
  have hstable : (prefixWord ++ tailWord_443724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443724).length < 2 ^ (prefixWord ++ tailWord_443724).sum := by decide
  have hdescent : baseEnd_443724 < baseStart_443724 := by decide
  rcases family_descends (prefixWord ++ tailWord_443724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443726 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_443726 : Nat := 118140960795 + 443726 * 2 ^ 59
def prefixEnd_443726 : Nat := 4983230072969 + 3 ^ 40 * 443726 * 2
def baseEnd_443726 : Nat := 227844716897036153684347

theorem tailTrace_443726 : CollatzResearch.WordTrace tailWord_443726 prefixEnd_443726 227844716897036153684347 := by
  unfold tailWord_443726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023002098807994901570879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10789344526975972808378021 2023002098807994901570879)
  ·
    refine ⟨3034503148211992352356319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2023002098807994901570879 3034503148211992352356319)
    ·
      refine ⟨4551754722317988528534479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3034503148211992352356319 4551754722317988528534479)
      ·
        refine ⟨6827632083476982792801719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4551754722317988528534479 6827632083476982792801719)
        ·
          refine ⟨10241448125215474189202579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6827632083476982792801719 10241448125215474189202579)
          ·
            refine ⟨15362172187823211283803869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10241448125215474189202579 15362172187823211283803869)
            ·
              refine ⟨5760814570433704231426451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15362172187823211283803869 5760814570433704231426451)
              ·
                refine ⟨8641221855650556347139677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5760814570433704231426451 8641221855650556347139677)
                ·
                  refine ⟨3240458195868958630177379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8641221855650556347139677 3240458195868958630177379)
                  ·
                    refine ⟨4860687293803437945266069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3240458195868958630177379 4860687293803437945266069)
                    ·
                      refine ⟨227844716897036153684347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4860687293803437945266069 227844716897036153684347)
                      ·
                        rfl

theorem cell23_443726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_443726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443726 prefixEnd_443726 := by exact prefixLift 443726
  have htrace : WordTrace (prefixWord ++ tailWord_443726) baseStart_443726 baseEnd_443726 := by
    simpa [prefixWord, tailWord_443726, baseEnd_443726] using wordTrace_append hprefix tailTrace_443726
  have hstable : (prefixWord ++ tailWord_443726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443726).length < 2 ^ (prefixWord ++ tailWord_443726).sum := by decide
  have hdescent : baseEnd_443726 < baseStart_443726 := by decide
  rcases family_descends (prefixWord ++ tailWord_443726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443733 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_443733 : Nat := 118140960795 + 443733 * 2 ^ 59
def prefixEnd_443733 : Nat := 4983230072969 + 3 ^ 40 * 443733 * 2
def baseEnd_443733 : Nat := 227848311261617626296815

theorem tailTrace_443733 : CollatzResearch.WordTrace tailWord_443733 prefixEnd_443733 227848311261617626296815 := by
  unfold tailWord_443733
  simp only [CollatzResearch.WordTrace]
  refine ⟨16184272101438599408071853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10789514734292399605381235 16184272101438599408071853)
  ·
    refine ⟨6069102038039474778026945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16184272101438599408071853 6069102038039474778026945)
    ·
      refine ⟨4551826528529606083520209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6069102038039474778026945 4551826528529606083520209)
      ·
        refine ⟨3413869896397204562640157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4551826528529606083520209 3413869896397204562640157)
        ·
          refine ⟨1280201211148951710990059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3413869896397204562640157 1280201211148951710990059)
          ·
            refine ⟨1920301816723427566485089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280201211148951710990059 1920301816723427566485089)
            ·
              refine ⟨1440226362542570674863817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1920301816723427566485089 1440226362542570674863817)
              ·
                refine ⟨1080169771906928006147863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1440226362542570674863817 1080169771906928006147863)
                ·
                  refine ⟨1620254657860392009221795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1080169771906928006147863 1620254657860392009221795)
                  ·
                    refine ⟨2430381986790588013832693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1620254657860392009221795 2430381986790588013832693)
                    ·
                      refine ⟨227848311261617626296815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2430381986790588013832693 227848311261617626296815)
                      ·
                        rfl

theorem cell23_443733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_443733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443733 prefixEnd_443733 := by exact prefixLift 443733
  have htrace : WordTrace (prefixWord ++ tailWord_443733) baseStart_443733 baseEnd_443733 := by
    simpa [prefixWord, tailWord_443733, baseEnd_443733] using wordTrace_append hprefix tailTrace_443733
  have hstable : (prefixWord ++ tailWord_443733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443733).length < 2 ^ (prefixWord ++ tailWord_443733).sum := by decide
  have hdescent : baseEnd_443733 < baseStart_443733 := by decide
  rcases family_descends (prefixWord ++ tailWord_443733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443736 : List Nat := [2, 1, 2, 2, 1, 1, 6, 8]
def baseStart_443736 : Nat := 118140960795 + 443736 * 2 ^ 59
def prefixEnd_443736 : Nat := 4983230072969 + 3 ^ 40 * 443736 * 2
def baseEnd_443736 : Nat := 8438883396428930168863

theorem tailTrace_443736 : CollatzResearch.WordTrace tailWord_443736 prefixEnd_443736 8438883396428930168863 := by
  unfold tailWord_443736
  simp only [CollatzResearch.WordTrace]
  refine ⟨8092190760213865460215531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10789587680285153946954041 8092190760213865460215531)
  ·
    refine ⟨12138286140320798190323297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8092190760213865460215531 12138286140320798190323297)
    ·
      refine ⟨9103714605240598642742473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12138286140320798190323297 9103714605240598642742473)
      ·
        refine ⟨6827785953930448982056855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9103714605240598642742473 6827785953930448982056855)
        ·
          refine ⟨10241678930895673473085283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6827785953930448982056855 10241678930895673473085283)
          ·
            refine ⟨15362518396343510209627925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10241678930895673473085283 15362518396343510209627925)
            ·
              refine ⟨720118049828602041076309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15362518396343510209627925 720118049828602041076309)
              ·
                refine ⟨8438883396428930168863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 720118049828602041076309 8438883396428930168863)
                ·
                  rfl

theorem cell23_443736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 8].length) (baseStart_443736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443736 prefixEnd_443736 := by exact prefixLift 443736
  have htrace : WordTrace (prefixWord ++ tailWord_443736) baseStart_443736 baseEnd_443736 := by
    simpa [prefixWord, tailWord_443736, baseEnd_443736] using wordTrace_append hprefix tailTrace_443736
  have hstable : (prefixWord ++ tailWord_443736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443736).length < 2 ^ (prefixWord ++ tailWord_443736).sum := by decide
  have hdescent : baseEnd_443736 < baseStart_443736 := by decide
  rcases family_descends (prefixWord ++ tailWord_443736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443776 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 5]
def baseStart_443776 : Nat := 118140960795 + 443776 * 2 ^ 59
def prefixEnd_443776 : Nat := 4983230072969 + 3 ^ 40 * 443776 * 2
def baseEnd_443776 : Nat := 227870390929760958059117

theorem tailTrace_443776 : CollatzResearch.WordTrace tailWord_443776 prefixEnd_443776 227870390929760958059117 := by
  unfold tailWord_443776
  simp only [CollatzResearch.WordTrace]
  refine ⟨8092920220141408875943591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10790560293521878501258121 8092920220141408875943591)
  ·
    refine ⟨12139380330212113313915387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8092920220141408875943591 12139380330212113313915387)
    ·
      refine ⟨18209070495318169970873081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12139380330212113313915387 18209070495318169970873081)
      ·
        refine ⟨13656802871488627478154811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18209070495318169970873081 13656802871488627478154811)
        ·
          refine ⟨20485204307232941217232217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13656802871488627478154811 20485204307232941217232217)
          ·
            refine ⟨15363903230424705912924163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20485204307232941217232217 15363903230424705912924163)
            ·
              refine ⟨23045854845637058869386245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15363903230424705912924163 23045854845637058869386245)
              ·
                refine ⟨4321097783556948538009921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23045854845637058869386245 4321097783556948538009921)
                ·
                  refine ⟨3240823337667711403507441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4321097783556948538009921 3240823337667711403507441)
                  ·
                    refine ⟨2430617503250783552630581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3240823337667711403507441 2430617503250783552630581)
                    ·
                      refine ⟨227870390929760958059117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2430617503250783552630581 227870390929760958059117)
                      ·
                        rfl

theorem cell23_443776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_443776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443776 prefixEnd_443776 := by exact prefixLift 443776
  have htrace : WordTrace (prefixWord ++ tailWord_443776) baseStart_443776 baseEnd_443776 := by
    simpa [prefixWord, tailWord_443776, baseEnd_443776] using wordTrace_append hprefix tailTrace_443776
  have hstable : (prefixWord ++ tailWord_443776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443776).length < 2 ^ (prefixWord ++ tailWord_443776).sum := by decide
  have hdescent : baseEnd_443776 < baseStart_443776 := by decide
  rcases family_descends (prefixWord ++ tailWord_443776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443820 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 1, 4, 2]
def baseStart_443820 : Nat := 118140960795 + 443820 * 2 ^ 59
def prefixEnd_443820 : Nat := 4983230072969 + 3 ^ 40 * 443820 * 2
def baseEnd_443820 : Nat := 227892984078558785908915

theorem tailTrace_443820 : CollatzResearch.WordTrace tailWord_443820 prefixEnd_443820 227892984078558785908915 := by
  unfold tailWord_443820
  simp only [CollatzResearch.WordTrace]
  refine ⟨8093722626061706633244457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10791630168082275510992609 8093722626061706633244457)
  ·
    refine ⟨6070291969546279974933343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8093722626061706633244457 6070291969546279974933343)
    ·
      refine ⟨9105437954319419962400015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6070291969546279974933343 9105437954319419962400015)
      ·
        refine ⟨13658156931479129943600023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9105437954319419962400015 13658156931479129943600023)
        ·
          refine ⟨20487235397218694915400035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13658156931479129943600023 20487235397218694915400035)
          ·
            refine ⟨30730853095828042373100053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20487235397218694915400035 30730853095828042373100053)
            ·
              refine ⟨1440508738866939486239065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30730853095828042373100053 1440508738866939486239065)
              ·
                refine ⟨1080381554150204614679299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1440508738866939486239065 1080381554150204614679299)
                ·
                  refine ⟨1620572331225306922018949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1080381554150204614679299 1620572331225306922018949)
                  ·
                    refine ⟨303857312104745047878553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1620572331225306922018949 303857312104745047878553)
                    ·
                      refine ⟨227892984078558785908915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 303857312104745047878553 227892984078558785908915)
                      ·
                        rfl

theorem cell23_443820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 4, 2].length) (baseStart_443820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443820 prefixEnd_443820 := by exact prefixLift 443820
  have htrace : WordTrace (prefixWord ++ tailWord_443820) baseStart_443820 baseEnd_443820 := by
    simpa [prefixWord, tailWord_443820, baseEnd_443820] using wordTrace_append hprefix tailTrace_443820
  have hstable : (prefixWord ++ tailWord_443820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443820).length < 2 ^ (prefixWord ++ tailWord_443820).sum := by decide
  have hdescent : baseEnd_443820 < baseStart_443820 := by decide
  rcases family_descends (prefixWord ++ tailWord_443820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443837 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 4, 2, 2]
def baseStart_443837 : Nat := 118140960795 + 443837 * 2 ^ 59
def prefixEnd_443837 : Nat := 4983230072969 + 3 ^ 40 * 443837 * 2
def baseEnd_443837 : Nat := 227901713249685219396337

theorem tailTrace_443837 : CollatzResearch.WordTrace tailWord_443837 prefixEnd_443837 227901713249685219396337 := by
  unfold tailWord_443837
  simp only [CollatzResearch.WordTrace]
  refine ⟨16188065293061825169857765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10792043528707883446571843 16188065293061825169857765)
  ·
    refine ⟨3035262242449092219348331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16188065293061825169857765 3035262242449092219348331)
    ·
      refine ⟨4552893363673638329022497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3035262242449092219348331 4552893363673638329022497)
      ·
        refine ⟨3414670022755228746766873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4552893363673638329022497 3414670022755228746766873)
        ·
          refine ⟨2561002517066421560075155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3414670022755228746766873 2561002517066421560075155)
          ·
            refine ⟨3841503775599632340112733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2561002517066421560075155 3841503775599632340112733)
            ·
              refine ⟨1440563915849862127542275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3841503775599632340112733 1440563915849862127542275)
              ·
                refine ⟨2160845873774793191313413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440563915849862127542275 2160845873774793191313413)
                ·
                  refine ⟨405158601332773723371265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2160845873774793191313413 405158601332773723371265)
                  ·
                    refine ⟨303868950999580292528449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 405158601332773723371265 303868950999580292528449)
                    ·
                      refine ⟨227901713249685219396337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 303868950999580292528449 227901713249685219396337)
                      ·
                        rfl

theorem cell23_443837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_443837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443837 prefixEnd_443837 := by exact prefixLift 443837
  have htrace : WordTrace (prefixWord ++ tailWord_443837) baseStart_443837 baseEnd_443837 := by
    simpa [prefixWord, tailWord_443837, baseEnd_443837] using wordTrace_append hprefix tailTrace_443837
  have hstable : (prefixWord ++ tailWord_443837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443837).length < 2 ^ (prefixWord ++ tailWord_443837).sum := by decide
  have hdescent : baseEnd_443837 < baseStart_443837 := by decide
  rcases family_descends (prefixWord ++ tailWord_443837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443873 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 1, 7]
def baseStart_443873 : Nat := 118140960795 + 443873 * 2 ^ 59
def prefixEnd_443873 : Nat := 4983230072969 + 3 ^ 40 * 443873 * 2
def baseEnd_443873 : Nat := 75973399517749026182057

theorem tailTrace_443873 : CollatzResearch.WordTrace tailWord_443873 prefixEnd_443873 75973399517749026182057 := by
  unfold tailWord_443873
  simp only [CollatzResearch.WordTrace]
  refine ⟨16189378320931403318168273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10792918880620935545445515 16189378320931403318168273)
  ·
    refine ⟨12142033740698552488626205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16189378320931403318168273 12142033740698552488626205)
    ·
      refine ⟨4553262652761957183234827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12142033740698552488626205 4553262652761957183234827)
      ·
        refine ⟨6829893979142935774852241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4553262652761957183234827 6829893979142935774852241)
        ·
          refine ⟨5122420484357201831139181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6829893979142935774852241 5122420484357201831139181)
          ·
            refine ⟨1920907681633950686677193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5122420484357201831139181 1920907681633950686677193)
            ·
              refine ⟨1440680761225463015007895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1920907681633950686677193 1440680761225463015007895)
              ·
                refine ⟨2161021141838194522511843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440680761225463015007895 2161021141838194522511843)
                ·
                  refine ⟨3241531712757291783767765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161021141838194522511843 3241531712757291783767765)
                  ·
                    refine ⟨75973399517749026182057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3241531712757291783767765 75973399517749026182057)
                    ·
                      rfl

theorem cell23_443873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_443873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443873 prefixEnd_443873 := by exact prefixLift 443873
  have htrace : WordTrace (prefixWord ++ tailWord_443873) baseStart_443873 baseEnd_443873 := by
    simpa [prefixWord, tailWord_443873, baseEnd_443873] using wordTrace_append hprefix tailTrace_443873
  have hstable : (prefixWord ++ tailWord_443873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443873).length < 2 ^ (prefixWord ++ tailWord_443873).sum := by decide
  have hdescent : baseEnd_443873 < baseStart_443873 := by decide
  rcases family_descends (prefixWord ++ tailWord_443873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443877 : List Nat := [1, 3, 1, 5, 1, 1, 3, 3, 5]
def baseStart_443877 : Nat := 118140960795 + 443877 * 2 ^ 59
def prefixEnd_443877 : Nat := 4983230072969 + 3 ^ 40 * 443877 * 2
def baseEnd_443877 : Nat := 25324694719540562544017

theorem tailTrace_443877 : CollatzResearch.WordTrace tailWord_443877 prefixEnd_443877 25324694719540562544017 := by
  unfold tailWord_443877
  simp only [CollatzResearch.WordTrace]
  refine ⟨16189524212916912001313885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10793016141944608000875923 16189524212916912001313885)
  ·
    refine ⟨6071071579843842000492707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16189524212916912001313885 6071071579843842000492707)
    ·
      refine ⟨9106607369765763000739061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6071071579843842000492707 9106607369765763000739061)
      ·
        refine ⟨853744440915540281319287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9106607369765763000739061 853744440915540281319287)
        ·
          refine ⟨1280616661373310421978931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853744440915540281319287 1280616661373310421978931)
          ·
            refine ⟨1920924992059965632968397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280616661373310421978931 1920924992059965632968397)
            ·
              refine ⟨720346872022487112363149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1920924992059965632968397 720346872022487112363149)
              ·
                refine ⟨270130077008432667136181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 720346872022487112363149 270130077008432667136181)
                ·
                  refine ⟨25324694719540562544017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270130077008432667136181 25324694719540562544017)
                  ·
                    rfl

theorem cell23_443877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 5].length) (baseStart_443877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443877 prefixEnd_443877 := by exact prefixLift 443877
  have htrace : WordTrace (prefixWord ++ tailWord_443877) baseStart_443877 baseEnd_443877 := by
    simpa [prefixWord, tailWord_443877, baseEnd_443877] using wordTrace_append hprefix tailTrace_443877
  have hstable : (prefixWord ++ tailWord_443877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443877).length < 2 ^ (prefixWord ++ tailWord_443877).sum := by decide
  have hdescent : baseEnd_443877 < baseStart_443877 := by decide
  rcases family_descends (prefixWord ++ tailWord_443877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443890 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_443890 : Nat := 118140960795 + 443890 * 2 ^ 59
def prefixEnd_443890 : Nat := 4983230072969 + 3 ^ 40 * 443890 * 2
def baseEnd_443890 : Nat := 75976309241457837344531

theorem tailTrace_443890 : CollatzResearch.WordTrace tailWord_443890 prefixEnd_443890 75976309241457837344531 := by
  unfold tailWord_443890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4047499590467453805384281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10793332241246543481024749 4047499590467453805384281)
  ·
    refine ⟨3035624692850590354038211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4047499590467453805384281 3035624692850590354038211)
    ·
      refine ⟨4553437039275885531057317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3035624692850590354038211 4553437039275885531057317)
      ·
        refine ⟨853769444864228537073247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4553437039275885531057317 853769444864228537073247)
        ·
          refine ⟨1280654167296342805609871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853769444864228537073247 1280654167296342805609871)
          ·
            refine ⟨1920981250944514208414807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280654167296342805609871 1920981250944514208414807)
            ·
              refine ⟨2881471876416771312622211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1920981250944514208414807 2881471876416771312622211)
              ·
                refine ⟨4322207814625156968933317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2881471876416771312622211 4322207814625156968933317)
                ·
                  refine ⟨810413965242216931674997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4322207814625156968933317 810413965242216931674997)
                  ·
                    refine ⟨75976309241457837344531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 810413965242216931674997 75976309241457837344531)
                    ·
                      rfl

theorem cell23_443890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_443890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443890 prefixEnd_443890 := by exact prefixLift 443890
  have htrace : WordTrace (prefixWord ++ tailWord_443890) baseStart_443890 baseEnd_443890 := by
    simpa [prefixWord, tailWord_443890, baseEnd_443890] using wordTrace_append hprefix tailTrace_443890
  have hstable : (prefixWord ++ tailWord_443890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443890).length < 2 ^ (prefixWord ++ tailWord_443890).sum := by decide
  have hdescent : baseEnd_443890 < baseStart_443890 := by decide
  rcases family_descends (prefixWord ++ tailWord_443890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443894 : List Nat := [5, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_443894 : Nat := 118140960795 + 443894 * 2 ^ 59
def prefixEnd_443894 : Nat := 4983230072969 + 3 ^ 40 * 443894 * 2
def baseEnd_443894 : Nat := 25325664627443499598175

theorem tailTrace_443894 : CollatzResearch.WordTrace tailWord_443894 prefixEnd_443894 25325664627443499598175 := by
  unfold tailWord_443894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1011884015865957744042671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10793429502570215936455157 1011884015865957744042671)
  ·
    refine ⟨1517826023798936616064007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1011884015865957744042671 1517826023798936616064007)
    ·
      refine ⟨2276739035698404924096011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1517826023798936616064007 2276739035698404924096011)
      ·
        refine ⟨3415108553547607386144017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2276739035698404924096011 3415108553547607386144017)
        ·
          refine ⟨2561331415160705539608013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3415108553547607386144017 2561331415160705539608013)
          ·
            refine ⟨960499280685264577353005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2561331415160705539608013 960499280685264577353005)
            ·
              refine ⟨360187230256974216507377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960499280685264577353005 360187230256974216507377)
              ·
                refine ⟨270140422692730662380533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360187230256974216507377 270140422692730662380533)
                ·
                  refine ⟨25325664627443499598175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270140422692730662380533 25325664627443499598175)
                  ·
                    rfl

theorem cell23_443894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_443894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443894 prefixEnd_443894 := by exact prefixLift 443894
  have htrace : WordTrace (prefixWord ++ tailWord_443894) baseStart_443894 baseEnd_443894 := by
    simpa [prefixWord, tailWord_443894, baseEnd_443894] using wordTrace_append hprefix tailTrace_443894
  have hstable : (prefixWord ++ tailWord_443894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443894).length < 2 ^ (prefixWord ++ tailWord_443894).sum := by decide
  have hdescent : baseEnd_443894 < baseStart_443894 := by decide
  rcases family_descends (prefixWord ++ tailWord_443894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443924 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_443924 : Nat := 118140960795 + 443924 * 2 ^ 59
def prefixEnd_443924 : Nat := 4983230072969 + 3 ^ 40 * 443924 * 2
def baseEnd_443924 : Nat := 75982128688875459669479

theorem tailTrace_443924 : CollatzResearch.WordTrace tailWord_443924 prefixEnd_443924 75982128688875459669479 := by
  unfold tailWord_443924
  simp only [CollatzResearch.WordTrace]
  refine ⟨8095619221873319514137413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10794158962497759352183217 8095619221873319514137413)
  ·
    refine ⟨1517928604101247408900765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8095619221873319514137413 1517928604101247408900765)
    ·
      refine ⟨569223226537967778337787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1517928604101247408900765 569223226537967778337787)
      ·
        refine ⟨853834839806951667506681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569223226537967778337787 853834839806951667506681)
        ·
          refine ⟨640376129855213750630011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853834839806951667506681 640376129855213750630011)
          ·
            refine ⟨960564194782820625945017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640376129855213750630011 960564194782820625945017)
            ·
              refine ⟨720423146087115469458763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960564194782820625945017 720423146087115469458763)
              ·
                refine ⟨1080634719130673204188145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720423146087115469458763 1080634719130673204188145)
                ·
                  refine ⟨810476039348004903141109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1080634719130673204188145 810476039348004903141109)
                  ·
                    refine ⟨75982128688875459669479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 810476039348004903141109 75982128688875459669479)
                    ·
                      rfl

theorem cell23_443924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_443924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443924 prefixEnd_443924 := by exact prefixLift 443924
  have htrace : WordTrace (prefixWord ++ tailWord_443924) baseStart_443924 baseEnd_443924 := by
    simpa [prefixWord, tailWord_443924, baseEnd_443924] using wordTrace_append hprefix tailTrace_443924
  have hstable : (prefixWord ++ tailWord_443924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443924).length < 2 ^ (prefixWord ++ tailWord_443924).sum := by decide
  have hdescent : baseEnd_443924 < baseStart_443924 := by decide
  rcases family_descends (prefixWord ++ tailWord_443924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443953 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_443953 : Nat := 118140960795 + 443953 * 2 ^ 59
def prefixEnd_443953 : Nat := 4983230072969 + 3 ^ 40 * 443953 * 2
def baseEnd_443953 : Nat := 227961277005606765545803

theorem tailTrace_443953 : CollatzResearch.WordTrace tailWord_443953 prefixEnd_443953 227961277005606765545803 := by
  unfold tailWord_443953
  simp only [CollatzResearch.WordTrace]
  refine ⟨16192296160641576981080513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10794864107094384654053675 16192296160641576981080513)
  ·
    refine ⟨12144222120481182735810385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16192296160641576981080513 12144222120481182735810385)
    ·
      refine ⟨9108166590360887051857789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12144222120481182735810385 9108166590360887051857789)
      ·
        refine ⟨3415562471385332644446671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9108166590360887051857789 3415562471385332644446671)
        ·
          refine ⟨5123343707077998966670007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3415562471385332644446671 5123343707077998966670007)
          ·
            refine ⟨7685015560616998450005011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5123343707077998966670007 7685015560616998450005011)
            ·
              refine ⟨11527523340925497675007517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7685015560616998450005011 11527523340925497675007517)
              ·
                refine ⟨4322821252847061628127819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11527523340925497675007517 4322821252847061628127819)
                ·
                  refine ⟨6484231879270592442191729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4322821252847061628127819 6484231879270592442191729)
                  ·
                    refine ⟨4863173909452944331643797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6484231879270592442191729 4863173909452944331643797)
                    ·
                      refine ⟨227961277005606765545803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4863173909452944331643797 227961277005606765545803)
                      ·
                        rfl

theorem cell23_443953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_443953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443953 prefixEnd_443953 := by exact prefixLift 443953
  have htrace : WordTrace (prefixWord ++ tailWord_443953) baseStart_443953 baseEnd_443953 := by
    simpa [prefixWord, tailWord_443953, baseEnd_443953] using wordTrace_append hprefix tailTrace_443953
  have hstable : (prefixWord ++ tailWord_443953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443953).length < 2 ^ (prefixWord ++ tailWord_443953).sum := by decide
  have hdescent : baseEnd_443953 < baseStart_443953 := by decide
  rcases family_descends (prefixWord ++ tailWord_443953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443973 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_443973 : Nat := 118140960795 + 443973 * 2 ^ 59
def prefixEnd_443973 : Nat := 4983230072969 + 3 ^ 40 * 443973 * 2
def baseEnd_443973 : Nat := 227971546618696687295711

theorem tailTrace_443973 : CollatzResearch.WordTrace tailWord_443973 prefixEnd_443973 227971546618696687295711 := by
  unfold tailWord_443973
  simp only [CollatzResearch.WordTrace]
  refine ⟨16193025620569120396808573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10795350413712746931205715 16193025620569120396808573)
  ·
    refine ⟨6072384607713420148803215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16193025620569120396808573 6072384607713420148803215)
    ·
      refine ⟨9108576911570130223204823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6072384607713420148803215 9108576911570130223204823)
      ·
        refine ⟨13662865367355195334807235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9108576911570130223204823 13662865367355195334807235)
        ·
          refine ⟨20494298051032793002210853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13662865367355195334807235 20494298051032793002210853)
          ·
            refine ⟨3842680884568648687914535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20494298051032793002210853 3842680884568648687914535)
            ·
              refine ⟨5764021326852973031871803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3842680884568648687914535 5764021326852973031871803)
              ·
                refine ⟨8646031990279459547807705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5764021326852973031871803 8646031990279459547807705)
                ·
                  refine ⟨6484523992709594660855779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8646031990279459547807705 6484523992709594660855779)
                  ·
                    refine ⟨9726785989064391991283669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6484523992709594660855779 9726785989064391991283669)
                    ·
                      refine ⟨227971546618696687295711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9726785989064391991283669 227971546618696687295711)
                      ·
                        rfl

theorem cell23_443973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_443973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443973 prefixEnd_443973 := by exact prefixLift 443973
  have htrace : WordTrace (prefixWord ++ tailWord_443973) baseStart_443973 baseEnd_443973 := by
    simpa [prefixWord, tailWord_443973, baseEnd_443973] using wordTrace_append hprefix tailTrace_443973
  have hstable : (prefixWord ++ tailWord_443973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443973).length < 2 ^ (prefixWord ++ tailWord_443973).sum := by decide
  have hdescent : baseEnd_443973 < baseStart_443973 := by decide
  rcases family_descends (prefixWord ++ tailWord_443973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443980 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 3, 5]
def baseStart_443980 : Nat := 118140960795 + 443980 * 2 ^ 59
def prefixEnd_443980 : Nat := 4983230072969 + 3 ^ 40 * 443980 * 2
def baseEnd_443980 : Nat := 75991713661092719969393

theorem tailTrace_443980 : CollatzResearch.WordTrace tailWord_443980 prefixEnd_443980 75991713661092719969393 := by
  unfold tailWord_443980
  simp only [CollatzResearch.WordTrace]
  refine ⟨8096640465771880296156697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10795520621029173728208929 8096640465771880296156697)
  ·
    refine ⟨6072480349328910222117523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8096640465771880296156697 6072480349328910222117523)
    ·
      refine ⟨9108720523993365333176285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6072480349328910222117523 9108720523993365333176285)
      ·
        refine ⟨3415770196497511999941107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9108720523993365333176285 3415770196497511999941107)
        ·
          refine ⟨5123655294746267999911661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3415770196497511999941107 5123655294746267999911661)
          ·
            refine ⟨1921370735529850499966873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5123655294746267999911661 1921370735529850499966873)
            ·
              refine ⟨1441028051647387874975155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1921370735529850499966873 1441028051647387874975155)
              ·
                refine ⟨2161542077471081812462733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441028051647387874975155 2161542077471081812462733)
                ·
                  refine ⟨810578279051655679673525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2161542077471081812462733 810578279051655679673525)
                  ·
                    refine ⟨75991713661092719969393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 810578279051655679673525 75991713661092719969393)
                    ·
                      rfl

theorem cell23_443980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_443980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443980 prefixEnd_443980 := by exact prefixLift 443980
  have htrace : WordTrace (prefixWord ++ tailWord_443980) baseStart_443980 baseEnd_443980 := by
    simpa [prefixWord, tailWord_443980, baseEnd_443980] using wordTrace_append hprefix tailTrace_443980
  have hstable : (prefixWord ++ tailWord_443980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443980).length < 2 ^ (prefixWord ++ tailWord_443980).sum := by decide
  have hdescent : baseEnd_443980 < baseStart_443980 := by decide
  rcases family_descends (prefixWord ++ tailWord_443980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443981 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_443981 : Nat := 118140960795 + 443981 * 2 ^ 59
def prefixEnd_443981 : Nat := 4983230072969 + 3 ^ 40 * 443981 * 2
def baseEnd_443981 : Nat := 227975654463932655995675

theorem tailTrace_443981 : CollatzResearch.WordTrace tailWord_443981 prefixEnd_443981 227975654463932655995675 := by
  unfold tailWord_443981
  simp only [CollatzResearch.WordTrace]
  refine ⟨16193317404540137763099797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10795544936360091842066531 16193317404540137763099797)
  ·
    refine ⟨759061753337818957645303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16193317404540137763099797 759061753337818957645303)
    ·
      refine ⟨1138592630006728436467955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 759061753337818957645303 1138592630006728436467955)
      ·
        refine ⟨1707888945010092654701933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1138592630006728436467955 1707888945010092654701933)
        ·
          refine ⟨640458354378784745513225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1707888945010092654701933 640458354378784745513225)
          ·
            refine ⟨480343765784088559134919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640458354378784745513225 480343765784088559134919)
            ·
              refine ⟨720515648676132838702379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480343765784088559134919 720515648676132838702379)
              ·
                refine ⟨1080773473014199258053569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720515648676132838702379 1080773473014199258053569)
                ·
                  refine ⟨810580104760649443540177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1080773473014199258053569 810580104760649443540177)
                  ·
                    refine ⟨607935078570487082655133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 810580104760649443540177 607935078570487082655133)
                    ·
                      refine ⟨227975654463932655995675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 607935078570487082655133 227975654463932655995675)
                      ·
                        rfl

theorem cell23_443981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_443981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_443981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_443981 prefixEnd_443981 := by exact prefixLift 443981
  have htrace : WordTrace (prefixWord ++ tailWord_443981) baseStart_443981 baseEnd_443981 := by
    simpa [prefixWord, tailWord_443981, baseEnd_443981] using wordTrace_append hprefix tailTrace_443981
  have hstable : (prefixWord ++ tailWord_443981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443981).length < 2 ^ (prefixWord ++ tailWord_443981).sum := by decide
  have hdescent : baseEnd_443981 < baseStart_443981 := by decide
  rcases family_descends (prefixWord ++ tailWord_443981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444023 : List Nat := [1, 1, 3, 1, 1, 3, 1, 12]
def baseStart_444023 : Nat := 118140960795 + 444023 * 2 ^ 59
def prefixEnd_444023 : Nat := 4983230072969 + 3 ^ 40 * 444023 * 2
def baseEnd_444023 : Nat := 8444341505608203395203

theorem tailTrace_444023 : CollatzResearch.WordTrace tailWord_444023 prefixEnd_444023 8444341505608203395203 := by
  unfold tailWord_444023
  simp only [CollatzResearch.WordTrace]
  refine ⟨16194849270387978936128723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10796566180258652624085815 16194849270387978936128723)
  ·
    refine ⟨24292273905581968404193085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16194849270387978936128723 24292273905581968404193085)
    ·
      refine ⟨9109602714593238151572407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24292273905581968404193085 9109602714593238151572407)
      ·
        refine ⟨13664404071889857227358611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9109602714593238151572407 13664404071889857227358611)
        ·
          refine ⟨20496606107834785841037917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13664404071889857227358611 20496606107834785841037917)
          ·
            refine ⟨7686227290438044690389219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20496606107834785841037917 7686227290438044690389219)
            ·
              refine ⟨11529340935657067035583829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7686227290438044690389219 11529340935657067035583829)
              ·
                refine ⟨8444341505608203395203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 11529340935657067035583829 8444341505608203395203)
                ·
                  rfl

theorem cell23_444023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 12].length) (baseStart_444023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444023 prefixEnd_444023 := by exact prefixLift 444023
  have htrace : WordTrace (prefixWord ++ tailWord_444023) baseStart_444023 baseEnd_444023 := by
    simpa [prefixWord, tailWord_444023, baseEnd_444023] using wordTrace_append hprefix tailTrace_444023
  have hstable : (prefixWord ++ tailWord_444023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444023).length < 2 ^ (prefixWord ++ tailWord_444023).sum := by decide
  have hdescent : baseEnd_444023 < baseStart_444023 := by decide
  rcases family_descends (prefixWord ++ tailWord_444023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444067 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 4, 1, 3]
def baseStart_444067 : Nat := 118140960795 + 444067 * 2 ^ 59
def prefixEnd_444067 : Nat := 4983230072969 + 3 ^ 40 * 444067 * 2
def baseEnd_444067 : Nat := 228019813800219319520279

theorem tailTrace_444067 : CollatzResearch.WordTrace tailWord_444067 prefixEnd_444067 228019813800219319520279 := by
  unfold tailWord_444067
  simp only [CollatzResearch.WordTrace]
  refine ⟨16196454082228574450730455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10797636054819049633820303 16196454082228574450730455)
  ·
    refine ⟨24294681123342861676095683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16196454082228574450730455 24294681123342861676095683)
    ·
      refine ⟨36442021685014292514143525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24294681123342861676095683 36442021685014292514143525)
      ·
        refine ⟨6832879065940179846401911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36442021685014292514143525 6832879065940179846401911)
        ·
          refine ⟨10249318598910269769602867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6832879065940179846401911 10249318598910269769602867)
          ·
            refine ⟨15373977898365404654404301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10249318598910269769602867 15373977898365404654404301)
            ·
              refine ⟨5765241711887026745401613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15373977898365404654404301 5765241711887026745401613)
              ·
                refine ⟨2161965641957635029525605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5765241711887026745401613 2161965641957635029525605)
                ·
                  refine ⟨405368557867056568036051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2161965641957635029525605 405368557867056568036051)
                  ·
                    refine ⟨608052836800584852054077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 405368557867056568036051 608052836800584852054077)
                    ·
                      refine ⟨228019813800219319520279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 608052836800584852054077 228019813800219319520279)
                      ·
                        rfl

theorem cell23_444067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_444067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444067 prefixEnd_444067 := by exact prefixLift 444067
  have htrace : WordTrace (prefixWord ++ tailWord_444067) baseStart_444067 baseEnd_444067 := by
    simpa [prefixWord, tailWord_444067, baseEnd_444067] using wordTrace_append hprefix tailTrace_444067
  have hstable : (prefixWord ++ tailWord_444067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444067).length < 2 ^ (prefixWord ++ tailWord_444067).sum := by decide
  have hdescent : baseEnd_444067 < baseStart_444067 := by decide
  rcases family_descends (prefixWord ++ tailWord_444067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444098 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_444098 : Nat := 118140960795 + 444098 * 2 ^ 59
def prefixEnd_444098 : Nat := 4983230072969 + 3 ^ 40 * 444098 * 2
def baseEnd_444098 : Nat := 228035731700508698232637

theorem tailTrace_444098 : CollatzResearch.WordTrace tailWord_444098 prefixEnd_444098 228035731700508698232637 := by
  unfold tailWord_444098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4049396186279066686277237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10798389830077511163405965 4049396186279066686277237)
  ·
    refine ⟨379630892463662501838491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4049396186279066686277237 379630892463662501838491)
    ·
      refine ⟨569446338695493752757737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379630892463662501838491 569446338695493752757737)
      ·
        refine ⟨427084754021620314568303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569446338695493752757737 427084754021620314568303)
        ·
          refine ⟨640627131032430471852455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427084754021620314568303 640627131032430471852455)
          ·
            refine ⟨960940696548645707778683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640627131032430471852455 960940696548645707778683)
            ·
              refine ⟨1441411044822968561668025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960940696548645707778683 1441411044822968561668025)
              ·
                refine ⟨1081058283617226421251019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1441411044822968561668025 1081058283617226421251019)
                ·
                  refine ⟨1621587425425839631876529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081058283617226421251019 1621587425425839631876529)
                  ·
                    refine ⟨1216190569069379723907397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1621587425425839631876529 1216190569069379723907397)
                    ·
                      refine ⟨228035731700508698232637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1216190569069379723907397 228035731700508698232637)
                      ·
                        rfl

theorem cell23_444098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_444098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444098 prefixEnd_444098 := by exact prefixLift 444098
  have htrace : WordTrace (prefixWord ++ tailWord_444098) baseStart_444098 baseEnd_444098 := by
    simpa [prefixWord, tailWord_444098, baseEnd_444098] using wordTrace_append hprefix tailTrace_444098
  have hstable : (prefixWord ++ tailWord_444098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444098).length < 2 ^ (prefixWord ++ tailWord_444098).sum := by decide
  have hdescent : baseEnd_444098 < baseStart_444098 := by decide
  rcases family_descends (prefixWord ++ tailWord_444098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444141 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_444141 : Nat := 118140960795 + 444141 * 2 ^ 59
def prefixEnd_444141 : Nat := 4983230072969 + 3 ^ 40 * 444141 * 2
def baseEnd_444141 : Nat := 228057811368652029994939

theorem tailTrace_444141 : CollatzResearch.WordTrace tailWord_444141 prefixEnd_444141 228057811368652029994939 := by
  unfold tailWord_444141
  simp only [CollatzResearch.WordTrace]
  refine ⟨16199153083960485088924277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10799435389306990059282851 16199153083960485088924277)
  ·
    refine ⟨1518670601621295477086651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16199153083960485088924277 1518670601621295477086651)
    ·
      refine ⟨2278005902431943215629977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1518670601621295477086651 2278005902431943215629977)
      ·
        refine ⟨1708504426823957411722483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2278005902431943215629977 1708504426823957411722483)
        ·
          refine ⟨2562756640235936117583725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708504426823957411722483 2562756640235936117583725)
          ·
            refine ⟨961033740088476044093897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2562756640235936117583725 961033740088476044093897)
            ·
              refine ⟨720775305066357033070423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961033740088476044093897 720775305066357033070423)
              ·
                refine ⟨1081162957599535549605635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720775305066357033070423 1081162957599535549605635)
                ·
                  refine ⟨1621744436399303324408453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081162957599535549605635 1621744436399303324408453)
                  ·
                    refine ⟨304077081824869373326585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1621744436399303324408453 304077081824869373326585)
                    ·
                      refine ⟨228057811368652029994939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 304077081824869373326585 228057811368652029994939)
                      ·
                        rfl

theorem cell23_444141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_444141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444141 prefixEnd_444141 := by exact prefixLift 444141
  have htrace : WordTrace (prefixWord ++ tailWord_444141) baseStart_444141 baseEnd_444141 := by
    simpa [prefixWord, tailWord_444141, baseEnd_444141] using wordTrace_append hprefix tailTrace_444141
  have hstable : (prefixWord ++ tailWord_444141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444141).length < 2 ^ (prefixWord ++ tailWord_444141).sum := by decide
  have hdescent : baseEnd_444141 < baseStart_444141 := by decide
  rcases family_descends (prefixWord ++ tailWord_444141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444160 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 1, 7]
def baseStart_444160 : Nat := 118140960795 + 444160 * 2 ^ 59
def prefixEnd_444160 : Nat := 4983230072969 + 3 ^ 40 * 444160 * 2
def baseEnd_444160 : Nat := 76022522500362485219117

theorem tailTrace_444160 : CollatzResearch.WordTrace tailWord_444160 prefixEnd_444160 76022522500362485219117 := by
  unfold tailWord_444160
  simp only [CollatzResearch.WordTrace]
  refine ⟨8099923035445825666932967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10799897380594434222577289 8099923035445825666932967)
  ·
    refine ⟨12149884553168738500399451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8099923035445825666932967 12149884553168738500399451)
    ·
      refine ⟨18224826829753107750599177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12149884553168738500399451 18224826829753107750599177)
      ·
        refine ⟨13668620122314830812949383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18224826829753107750599177 13668620122314830812949383)
        ·
          refine ⟨20502930183472246219424075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13668620122314830812949383 20502930183472246219424075)
          ·
            refine ⟨30754395275208369329136113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20502930183472246219424075 30754395275208369329136113)
            ·
              refine ⟨23065796456406276996852085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30754395275208369329136113 23065796456406276996852085)
              ·
                refine ⟨2162418417788088468454883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23065796456406276996852085 2162418417788088468454883)
                ·
                  refine ⟨3243627626682132702682325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162418417788088468454883 3243627626682132702682325)
                  ·
                    refine ⟨76022522500362485219117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3243627626682132702682325 76022522500362485219117)
                    ·
                      rfl

theorem cell23_444160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 7].length) (baseStart_444160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444160 prefixEnd_444160 := by exact prefixLift 444160
  have htrace : WordTrace (prefixWord ++ tailWord_444160) baseStart_444160 baseEnd_444160 := by
    simpa [prefixWord, tailWord_444160, baseEnd_444160] using wordTrace_append hprefix tailTrace_444160
  have hstable : (prefixWord ++ tailWord_444160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444160).length < 2 ^ (prefixWord ++ tailWord_444160).sum := by decide
  have hdescent : baseEnd_444160 < baseStart_444160 := by decide
  rcases family_descends (prefixWord ++ tailWord_444160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444164 : List Nat := [2, 3, 2, 2, 1, 2, 1, 5, 5]
def baseStart_444164 : Nat := 118140960795 + 444164 * 2 ^ 59
def prefixEnd_444164 : Nat := 4983230072969 + 3 ^ 40 * 444164 * 2
def baseEnd_444164 : Nat := 25341069047078382223037

theorem tailTrace_444164 : CollatzResearch.WordTrace tailWord_444164 prefixEnd_444164 25341069047078382223037 := by
  unfold tailWord_444164
  simp only [CollatzResearch.WordTrace]
  refine ⟨8099995981438580008505773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10799994641918106678007697 8099995981438580008505773)
  ·
    refine ⟨3037498493039467503189665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8099995981438580008505773 3037498493039467503189665)
    ·
      refine ⟨2278123869779600627392249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3037498493039467503189665 2278123869779600627392249)
      ·
        refine ⟨1708592902334700470544187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2278123869779600627392249 1708592902334700470544187)
        ·
          refine ⟨2562889353502050705816281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708592902334700470544187 2562889353502050705816281)
          ·
            refine ⟨1922167015126538029362211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2562889353502050705816281 1922167015126538029362211)
            ·
              refine ⟨2883250522689807044043317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1922167015126538029362211 2883250522689807044043317)
              ·
                refine ⟨270304736502169410379061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2883250522689807044043317 270304736502169410379061)
                ·
                  refine ⟨25341069047078382223037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270304736502169410379061 25341069047078382223037)
                  ·
                    rfl

theorem cell23_444164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_444164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444164 prefixEnd_444164 := by exact prefixLift 444164
  have htrace : WordTrace (prefixWord ++ tailWord_444164) baseStart_444164 baseEnd_444164 := by
    simpa [prefixWord, tailWord_444164, baseEnd_444164] using wordTrace_append hprefix tailTrace_444164
  have hstable : (prefixWord ++ tailWord_444164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444164).length < 2 ^ (prefixWord ++ tailWord_444164).sum := by decide
  have hdescent : baseEnd_444164 < baseStart_444164 := by decide
  rcases family_descends (prefixWord ++ tailWord_444164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444197 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_444197 : Nat := 118140960795 + 444197 * 2 ^ 59
def prefixEnd_444197 : Nat := 4983230072969 + 3 ^ 40 * 444197 * 2
def baseEnd_444197 : Nat := 228086566285303810894681

theorem tailTrace_444197 : CollatzResearch.WordTrace tailWord_444197 prefixEnd_444197 228086566285303810894681 := by
  unfold tailWord_444197
  simp only [CollatzResearch.WordTrace]
  refine ⟨16201195571757606652962845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10800797047838404435308563 16201195571757606652962845)
  ·
    refine ⟨6075448339409102494861067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16201195571757606652962845 6075448339409102494861067)
    ·
      refine ⟨9113172509113653742291601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6075448339409102494861067 9113172509113653742291601)
      ·
        refine ⟨6834879381835240306718701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9113172509113653742291601 6834879381835240306718701)
        ·
          refine ⟨2563079768188215115019513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6834879381835240306718701 2563079768188215115019513)
          ·
            refine ⟨1922309826141161336264635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2563079768188215115019513 1922309826141161336264635)
            ·
              refine ⟨2883464739211742004396953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1922309826141161336264635 2883464739211742004396953)
              ·
                refine ⟨2162598554408806503297715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2883464739211742004396953 2162598554408806503297715)
                ·
                  refine ⟨3243897831613209754946573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162598554408806503297715 3243897831613209754946573)
                  ·
                    refine ⟨1216461686854953658104965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3243897831613209754946573 1216461686854953658104965)
                    ·
                      refine ⟨228086566285303810894681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1216461686854953658104965 228086566285303810894681)
                      ·
                        rfl

theorem cell23_444197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_444197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444197 prefixEnd_444197 := by exact prefixLift 444197
  have htrace : WordTrace (prefixWord ++ tailWord_444197) baseStart_444197 baseEnd_444197 := by
    simpa [prefixWord, tailWord_444197, baseEnd_444197] using wordTrace_append hprefix tailTrace_444197
  have hstable : (prefixWord ++ tailWord_444197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444197).length < 2 ^ (prefixWord ++ tailWord_444197).sum := by decide
  have hdescent : baseEnd_444197 < baseStart_444197 := by decide
  rcases family_descends (prefixWord ++ tailWord_444197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444234 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_444234 : Nat := 118140960795 + 444234 * 2 ^ 59
def prefixEnd_444234 : Nat := 4983230072969 + 3 ^ 40 * 444234 * 2
def baseEnd_444234 : Nat := 228105565069520166132011

theorem tailTrace_444234 : CollatzResearch.WordTrace tailWord_444234 prefixEnd_444234 228105565069520166132011 := by
  unfold tailWord_444234
  simp only [CollatzResearch.WordTrace]
  refine ⟨4050636268155890493014939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10801696715082374648039837 4050636268155890493014939)
  ·
    refine ⟨6075954402233835739522409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4050636268155890493014939 6075954402233835739522409)
    ·
      refine ⟨4556965801675376804641807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6075954402233835739522409 4556965801675376804641807)
      ·
        refine ⟨6835448702513065206962711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4556965801675376804641807 6835448702513065206962711)
        ·
          refine ⟨10253173053769597810444067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6835448702513065206962711 10253173053769597810444067)
          ·
            refine ⟨15379759580654396715666101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10253173053769597810444067 15379759580654396715666101)
            ·
              refine ⟨1441852460686349692093697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15379759580654396715666101 1441852460686349692093697)
              ·
                refine ⟨1081389345514762269070273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1441852460686349692093697 1081389345514762269070273)
                ·
                  refine ⟨811042009136071701802705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1081389345514762269070273 811042009136071701802705)
                  ·
                    refine ⟨608281506852053776352029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 811042009136071701802705 608281506852053776352029)
                    ·
                      refine ⟨228105565069520166132011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 608281506852053776352029 228105565069520166132011)
                      ·
                        rfl

theorem cell23_444234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_444234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444234 prefixEnd_444234 := by exact prefixLift 444234
  have htrace : WordTrace (prefixWord ++ tailWord_444234) baseStart_444234 baseEnd_444234 := by
    simpa [prefixWord, tailWord_444234, baseEnd_444234] using wordTrace_append hprefix tailTrace_444234
  have hstable : (prefixWord ++ tailWord_444234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444234).length < 2 ^ (prefixWord ++ tailWord_444234).sum := by decide
  have hdescent : baseEnd_444234 < baseStart_444234 := by decide
  rcases family_descends (prefixWord ++ tailWord_444234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444241 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 3, 4]
def baseStart_444241 : Nat := 118140960795 + 444241 * 2 ^ 59
def prefixEnd_444241 : Nat := 4983230072969 + 3 ^ 40 * 444241 * 2
def baseEnd_444241 : Nat := 76036386478033879581493

theorem tailTrace_444241 : CollatzResearch.WordTrace tailWord_444241 prefixEnd_444241 76036386478033879581493 := by
  unfold tailWord_444241
  simp only [CollatzResearch.WordTrace]
  refine ⟨16202800383598202167564577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10801866922398801445043051 16202800383598202167564577)
  ·
    refine ⟨12152100287698651625673433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16202800383598202167564577 12152100287698651625673433)
    ·
      refine ⟨9114075215773988719255075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12152100287698651625673433 9114075215773988719255075)
      ·
        refine ⟨13671112823660983078882613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9114075215773988719255075 13671112823660983078882613)
        ·
          refine ⟨1281666827218217163645245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13671112823660983078882613 1281666827218217163645245)
          ·
            refine ⟨480625060206831436366967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1281666827218217163645245 480625060206831436366967)
            ·
              refine ⟨720937590310247154550451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480625060206831436366967 720937590310247154550451)
              ·
                refine ⟨1081406385465370731825677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720937590310247154550451 1081406385465370731825677)
                ·
                  refine ⟨405527394549514024434629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081406385465370731825677 405527394549514024434629)
                  ·
                    refine ⟨76036386478033879581493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 405527394549514024434629 76036386478033879581493)
                    ·
                      rfl

theorem cell23_444241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_444241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444241 prefixEnd_444241 := by exact prefixLift 444241
  have htrace : WordTrace (prefixWord ++ tailWord_444241) baseStart_444241 baseEnd_444241 := by
    simpa [prefixWord, tailWord_444241, baseEnd_444241] using wordTrace_append hprefix tailTrace_444241
  have hstable : (prefixWord ++ tailWord_444241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444241).length < 2 ^ (prefixWord ++ tailWord_444241).sum := by decide
  have hdescent : baseEnd_444241 < baseStart_444241 := by decide
  rcases family_descends (prefixWord ++ tailWord_444241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444291 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 2, 3, 2]
def baseStart_444291 : Nat := 118140960795 + 444291 * 2 ^ 59
def prefixEnd_444291 : Nat := 4983230072969 + 3 ^ 40 * 444291 * 2
def baseEnd_444291 : Nat := 228134833466826443119249

theorem tailTrace_444291 : CollatzResearch.WordTrace tailWord_444291 prefixEnd_444291 228134833466826443119249 := by
  unfold tailWord_444291
  simp only [CollatzResearch.WordTrace]
  refine ⟨16204624033417060706884727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10803082688944707137923151 16204624033417060706884727)
  ·
    refine ⟨24306936050125591060327091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16204624033417060706884727 24306936050125591060327091)
    ·
      refine ⟨36460404075188386590490637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24306936050125591060327091 36460404075188386590490637)
      ·
        refine ⟨13672651528195644971433989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36460404075188386590490637 13672651528195644971433989)
        ·
          refine ⟨2563622161536683432143873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13672651528195644971433989 2563622161536683432143873)
          ·
            refine ⟨1922716621152512574107905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2563622161536683432143873 1922716621152512574107905)
            ·
              refine ⟨1442037465864384430580929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1922716621152512574107905 1442037465864384430580929)
              ·
                refine ⟨1081528099398288322935697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1442037465864384430580929 1081528099398288322935697)
                ·
                  refine ⟨811146074548716242201773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1081528099398288322935697 811146074548716242201773)
                  ·
                    refine ⟨304179777955768590825665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 811146074548716242201773 304179777955768590825665)
                    ·
                      refine ⟨228134833466826443119249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 304179777955768590825665 228134833466826443119249)
                      ·
                        rfl

theorem cell23_444291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 3, 2].length) (baseStart_444291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444291 prefixEnd_444291 := by exact prefixLift 444291
  have htrace : WordTrace (prefixWord ++ tailWord_444291) baseStart_444291 baseEnd_444291 := by
    simpa [prefixWord, tailWord_444291, baseEnd_444291] using wordTrace_append hprefix tailTrace_444291
  have hstable : (prefixWord ++ tailWord_444291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444291).length < 2 ^ (prefixWord ++ tailWord_444291).sum := by decide
  have hdescent : baseEnd_444291 < baseStart_444291 := by decide
  rcases family_descends (prefixWord ++ tailWord_444291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444297 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 3, 6]
def baseStart_444297 : Nat := 118140960795 + 444297 * 2 ^ 59
def prefixEnd_444297 : Nat := 4983230072969 + 3 ^ 40 * 444297 * 2
def baseEnd_444297 : Nat := 76045971450251139881407

theorem tailTrace_444297 : CollatzResearch.WordTrace tailWord_444297 prefixEnd_444297 76045971450251139881407 := by
  unfold tailWord_444297
  simp only [CollatzResearch.WordTrace]
  refine ⟨16204842871395323731603145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10803228580930215821068763 16204842871395323731603145)
  ·
    refine ⟨12153632153546492798702359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16204842871395323731603145 12153632153546492798702359)
    ·
      refine ⟨18230448230319739198053539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12153632153546492798702359 18230448230319739198053539)
      ·
        refine ⟨27345672345479608797080309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18230448230319739198053539 27345672345479608797080309)
        ·
          refine ⟨2563656782388713324726279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27345672345479608797080309 2563656782388713324726279)
          ·
            refine ⟨3845485173583069987089419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2563656782388713324726279 3845485173583069987089419)
            ·
              refine ⟨5768227760374604980634129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3845485173583069987089419 5768227760374604980634129)
              ·
                refine ⟨4326170820280953735475597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5768227760374604980634129 4326170820280953735475597)
                ·
                  refine ⟨1622314057605357650803349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4326170820280953735475597 1622314057605357650803349)
                  ·
                    refine ⟨76045971450251139881407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1622314057605357650803349 76045971450251139881407)
                    ·
                      rfl

theorem cell23_444297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 6].length) (baseStart_444297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444297 prefixEnd_444297 := by exact prefixLift 444297
  have htrace : WordTrace (prefixWord ++ tailWord_444297) baseStart_444297 baseEnd_444297 := by
    simpa [prefixWord, tailWord_444297, baseEnd_444297] using wordTrace_append hprefix tailTrace_444297
  have hstable : (prefixWord ++ tailWord_444297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444297).length < 2 ^ (prefixWord ++ tailWord_444297).sum := by decide
  have hdescent : baseEnd_444297 < baseStart_444297 := by decide
  rcases family_descends (prefixWord ++ tailWord_444297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444314 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 1, 6]
def baseStart_444314 : Nat := 118140960795 + 444314 * 2 ^ 59
def prefixEnd_444314 : Nat := 4983230072969 + 3 ^ 40 * 444314 * 2
def baseEnd_444314 : Nat := 76048881173959951043881

theorem tailTrace_444314 : CollatzResearch.WordTrace tailWord_444314 prefixEnd_444314 76048881173959951043881 := by
  unfold tailWord_444314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4051365728083433908742999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10803641941555823756647997 4051365728083433908742999)
  ·
    refine ⟨6077048592125150863114499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4051365728083433908742999 6077048592125150863114499)
    ·
      refine ⟨9115572888187726294671749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6077048592125150863114499 9115572888187726294671749)
      ·
        refine ⟨1709169916535198680250953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9115572888187726294671749 1709169916535198680250953)
        ·
          refine ⟨1281877437401399010188215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1709169916535198680250953 1281877437401399010188215)
          ·
            refine ⟨1922816156102098515282323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281877437401399010188215 1922816156102098515282323)
            ·
              refine ⟨2884224234153147772923485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1922816156102098515282323 2884224234153147772923485)
              ·
                refine ⟨1081584087807430414846307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2884224234153147772923485 1081584087807430414846307)
                ·
                  refine ⟨1622376131711145622269461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081584087807430414846307 1622376131711145622269461)
                  ·
                    refine ⟨76048881173959951043881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1622376131711145622269461 76048881173959951043881)
                    ·
                      rfl

theorem cell23_444314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_444314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444314 prefixEnd_444314 := by exact prefixLift 444314
  have htrace : WordTrace (prefixWord ++ tailWord_444314) baseStart_444314 baseEnd_444314 := by
    simpa [prefixWord, tailWord_444314, baseEnd_444314] using wordTrace_append hprefix tailTrace_444314
  have hstable : (prefixWord ++ tailWord_444314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444314).length < 2 ^ (prefixWord ++ tailWord_444314).sum := by decide
  have hdescent : baseEnd_444314 < baseStart_444314 := by decide
  rcases family_descends (prefixWord ++ tailWord_444314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444348 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 4, 4]
def baseStart_444348 : Nat := 118140960795 + 444348 * 2 ^ 59
def prefixEnd_444348 : Nat := 4983230072969 + 3 ^ 40 * 444348 * 2
def baseEnd_444348 : Nat := 76054700621377573368829

theorem tailTrace_444348 : CollatzResearch.WordTrace tailWord_444348 prefixEnd_444348 76054700621377573368829 := by
  unfold tailWord_444348
  simp only [CollatzResearch.WordTrace]
  refine ⟨8103351497105279720854849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10804468662807039627806465 8103351497105279720854849)
  ·
    refine ⟨6077513622828959790641137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8103351497105279720854849 6077513622828959790641137)
    ·
      refine ⟨4558135217121719842980853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6077513622828959790641137 4558135217121719842980853)
      ·
        refine ⟨427325176605161235279455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4558135217121719842980853 427325176605161235279455)
        ·
          refine ⟨640987764907741852919183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427325176605161235279455 640987764907741852919183)
          ·
            refine ⟨961481647361612779378775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640987764907741852919183 961481647361612779378775)
            ·
              refine ⟨1442222471042419169068163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961481647361612779378775 1442222471042419169068163)
              ·
                refine ⟨2163333706563628753602245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442222471042419169068163 2163333706563628753602245)
                ·
                  refine ⟨405625069980680391300421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2163333706563628753602245 405625069980680391300421)
                  ·
                    refine ⟨76054700621377573368829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 405625069980680391300421 76054700621377573368829)
                    ·
                      rfl

theorem cell23_444348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_444348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444348 prefixEnd_444348 := by exact prefixLift 444348
  have htrace : WordTrace (prefixWord ++ tailWord_444348) baseStart_444348 baseEnd_444348 := by
    simpa [prefixWord, tailWord_444348, baseEnd_444348] using wordTrace_append hprefix tailTrace_444348
  have hstable : (prefixWord ++ tailWord_444348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444348).length < 2 ^ (prefixWord ++ tailWord_444348).sum := by decide
  have hdescent : baseEnd_444348 < baseStart_444348 := by decide
  rcases family_descends (prefixWord ++ tailWord_444348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444357 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 2, 7]
def baseStart_444357 : Nat := 118140960795 + 444357 * 2 ^ 59
def prefixEnd_444357 : Nat := 4983230072969 + 3 ^ 40 * 444357 * 2
def baseEnd_444357 : Nat := 76056241063341061631315

theorem tailTrace_444357 : CollatzResearch.WordTrace tailWord_444357 prefixEnd_444357 76056241063341061631315 := by
  unfold tailWord_444357
  simp only [CollatzResearch.WordTrace]
  refine ⟨16207031251177953978787325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10804687500785302652524883 16207031251177953978787325)
  ·
    refine ⟨6077636719191732742045247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16207031251177953978787325 6077636719191732742045247)
    ·
      refine ⟨9116455078787599113067871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6077636719191732742045247 9116455078787599113067871)
      ·
        refine ⟨13674682618181398669601807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9116455078787599113067871 13674682618181398669601807)
        ·
          refine ⟨20512023927272098004402711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13674682618181398669601807 20512023927272098004402711)
          ·
            refine ⟨30768035890908147006604067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20512023927272098004402711 30768035890908147006604067)
            ·
              refine ⟨46152053836362220509906101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30768035890908147006604067 46152053836362220509906101)
              ·
                refine ⟨4326755047158958172803697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46152053836362220509906101 4326755047158958172803697)
                ·
                  refine ⟨3245066285369218629602773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4326755047158958172803697 3245066285369218629602773)
                  ·
                    refine ⟨76056241063341061631315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3245066285369218629602773 76056241063341061631315)
                    ·
                      rfl

theorem cell23_444357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_444357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444357 prefixEnd_444357 := by exact prefixLift 444357
  have htrace : WordTrace (prefixWord ++ tailWord_444357) baseStart_444357 baseEnd_444357 := by
    simpa [prefixWord, tailWord_444357, baseEnd_444357] using wordTrace_append hprefix tailTrace_444357
  have hstable : (prefixWord ++ tailWord_444357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444357).length < 2 ^ (prefixWord ++ tailWord_444357).sum := by decide
  have hdescent : baseEnd_444357 < baseStart_444357 := by decide
  rcases family_descends (prefixWord ++ tailWord_444357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444378 : List Nat := [3, 1, 1, 2, 6, 1, 2, 7]
def baseStart_444378 : Nat := 118140960795 + 444378 * 2 ^ 59
def prefixEnd_444378 : Nat := 4983230072969 + 3 ^ 40 * 444378 * 2
def baseEnd_444378 : Nat := 8451092825324726027087

theorem tailTrace_444378 : CollatzResearch.WordTrace tailWord_444378 prefixEnd_444378 8451092825324726027087 := by
  unfold tailWord_444378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4051949296025468641325447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10805198122734583043534525 4051949296025468641325447)
  ·
    refine ⟨6077923944038202961988171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4051949296025468641325447 6077923944038202961988171)
    ·
      refine ⟨9116885916057304442982257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6077923944038202961988171 9116885916057304442982257)
      ·
        refine ⟨6837664437042978332236693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9116885916057304442982257 6837664437042978332236693)
        ·
          refine ⟨320515520486389609323595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6837664437042978332236693 320515520486389609323595)
          ·
            refine ⟨480773280729584413985393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320515520486389609323595 480773280729584413985393)
            ·
              refine ⟨360579960547188310489045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480773280729584413985393 360579960547188310489045)
              ·
                refine ⟨8451092825324726027087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 360579960547188310489045 8451092825324726027087)
                ·
                  rfl

theorem cell23_444378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 7].length) (baseStart_444378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444378 prefixEnd_444378 := by exact prefixLift 444378
  have htrace : WordTrace (prefixWord ++ tailWord_444378) baseStart_444378 baseEnd_444378 := by
    simpa [prefixWord, tailWord_444378, baseEnd_444378] using wordTrace_append hprefix tailTrace_444378
  have hstable : (prefixWord ++ tailWord_444378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444378).length < 2 ^ (prefixWord ++ tailWord_444378).sum := by decide
  have hdescent : baseEnd_444378 < baseStart_444378 := by decide
  rcases family_descends (prefixWord ++ tailWord_444378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444424 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_444424 : Nat := 118140960795 + 444424 * 2 ^ 59
def prefixEnd_444424 : Nat := 4983230072969 + 3 ^ 40 * 444424 * 2
def baseEnd_444424 : Nat := 228203126393874422756137

theorem tailTrace_444424 : CollatzResearch.WordTrace tailWord_444424 prefixEnd_444424 228203126393874422756137 := by
  unfold tailWord_444424
  simp only [CollatzResearch.WordTrace]
  refine ⟨8104737470967612210738163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10806316627956816280984217 8104737470967612210738163)
  ·
    refine ⟨12157106206451418316107245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8104737470967612210738163 12157106206451418316107245)
    ·
      refine ⟨4558914827419281868540217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12157106206451418316107245 4558914827419281868540217)
      ·
        refine ⟨3419186120564461401405163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4558914827419281868540217 3419186120564461401405163)
        ·
          refine ⟨5128779180846692102107745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3419186120564461401405163 5128779180846692102107745)
          ·
            refine ⟨3846584385635019076580809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5128779180846692102107745 3846584385635019076580809)
            ·
              refine ⟨2884938289226264307435607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3846584385635019076580809 2884938289226264307435607)
              ·
                refine ⟨4327407433839396461153411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2884938289226264307435607 4327407433839396461153411)
                ·
                  refine ⟨6491111150759094691730117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327407433839396461153411 6491111150759094691730117)
                  ·
                    refine ⟨1217083340767330254699397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6491111150759094691730117 1217083340767330254699397)
                    ·
                      refine ⟨228203126393874422756137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1217083340767330254699397 228203126393874422756137)
                      ·
                        rfl

theorem cell23_444424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_444424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444424 prefixEnd_444424 := by exact prefixLift 444424
  have htrace : WordTrace (prefixWord ++ tailWord_444424) baseStart_444424 baseEnd_444424 := by
    simpa [prefixWord, tailWord_444424, baseEnd_444424] using wordTrace_append hprefix tailTrace_444424
  have hstable : (prefixWord ++ tailWord_444424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444424).length < 2 ^ (prefixWord ++ tailWord_444424).sum := by decide
  have hdescent : baseEnd_444424 < baseStart_444424 := by decide
  rcases family_descends (prefixWord ++ tailWord_444424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444451 : List Nat := [1, 1, 1, 4, 3, 1, 2, 5, 5]
def baseStart_444451 : Nat := 118140960795 + 444451 * 2 ^ 59
def prefixEnd_444451 : Nat := 4983230072969 + 3 ^ 40 * 444451 * 2
def baseEnd_444451 : Nat := 25357443374616201902057

theorem tailTrace_444451 : CollatzResearch.WordTrace tailWord_444451 prefixEnd_444451 25357443374616201902057 := by
  unfold tailWord_444451
  simp only [CollatzResearch.WordTrace]
  refine ⟨16210459712837408032709207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10806973141891605355139471 16210459712837408032709207)
  ·
    refine ⟨24315689569256112049063811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16210459712837408032709207 24315689569256112049063811)
    ·
      refine ⟨36473534353884168073595717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24315689569256112049063811 36473534353884168073595717)
      ·
        refine ⟨6838787691353281513799197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36473534353884168073595717 6838787691353281513799197)
        ·
          refine ⟨2564545384257480567674699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6838787691353281513799197 2564545384257480567674699)
          ·
            refine ⟨3846818076386220851512049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2564545384257480567674699 3846818076386220851512049)
            ·
              refine ⟨2885113557289665638634037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3846818076386220851512049 2885113557289665638634037)
              ·
                refine ⟨270479395995906153621941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2885113557289665638634037 270479395995906153621941)
                ·
                  refine ⟨25357443374616201902057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270479395995906153621941 25357443374616201902057)
                  ·
                    rfl

theorem cell23_444451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 5].length) (baseStart_444451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444451 prefixEnd_444451 := by exact prefixLift 444451
  have htrace : WordTrace (prefixWord ++ tailWord_444451) baseStart_444451 baseEnd_444451 := by
    simpa [prefixWord, tailWord_444451, baseEnd_444451] using wordTrace_append hprefix tailTrace_444451
  have hstable : (prefixWord ++ tailWord_444451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444451).length < 2 ^ (prefixWord ++ tailWord_444451).sum := by decide
  have hdescent : baseEnd_444451 < baseStart_444451 := by decide
  rcases family_descends (prefixWord ++ tailWord_444451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444462 : List Nat := [4, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_444462 : Nat := 118140960795 + 444462 * 2 ^ 59
def prefixEnd_444462 : Nat := 4983230072969 + 3 ^ 40 * 444462 * 2
def baseEnd_444462 : Nat := 228222638658745274080963

theorem tailTrace_444462 : CollatzResearch.WordTrace tailWord_444462 prefixEnd_444462 228222638658745274080963 := by
  unfold tailWord_444462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2026357614474694613919955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10807240610531704607573093 2026357614474694613919955)
  ·
    refine ⟨3039536421712041920879933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2026357614474694613919955 3039536421712041920879933)
    ·
      refine ⟨1139826158142015720329975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3039536421712041920879933 1139826158142015720329975)
      ·
        refine ⟨1709739237213023580494963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139826158142015720329975 1709739237213023580494963)
        ·
          refine ⟨2564608855819535370742445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1709739237213023580494963 2564608855819535370742445)
          ·
            refine ⟨961728320932325764028417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2564608855819535370742445 961728320932325764028417)
            ·
              refine ⟨721296240699244323021313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961728320932325764028417 721296240699244323021313)
              ·
                refine ⟨540972180524433242265985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721296240699244323021313 540972180524433242265985)
                ·
                  refine ⟨405729135393324931699489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540972180524433242265985 405729135393324931699489)
                  ·
                    refine ⟨304296851544993698774617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 405729135393324931699489 304296851544993698774617)
                    ·
                      refine ⟨228222638658745274080963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 304296851544993698774617 228222638658745274080963)
                      ·
                        rfl

theorem cell23_444462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_444462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444462 prefixEnd_444462 := by exact prefixLift 444462
  have htrace : WordTrace (prefixWord ++ tailWord_444462) baseStart_444462 baseEnd_444462 := by
    simpa [prefixWord, tailWord_444462, baseEnd_444462] using wordTrace_append hprefix tailTrace_444462
  have hstable : (prefixWord ++ tailWord_444462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444462).length < 2 ^ (prefixWord ++ tailWord_444462).sum := by decide
  have hdescent : baseEnd_444462 < baseStart_444462 := by decide
  rcases family_descends (prefixWord ++ tailWord_444462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444471 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 2, 5, 2]
def baseStart_444471 : Nat := 118140960795 + 444471 * 2 ^ 59
def prefixEnd_444471 : Nat := 4983230072969 + 3 ^ 40 * 444471 * 2
def baseEnd_444471 : Nat := 228227259984635738868421

theorem tailTrace_444471 : CollatzResearch.WordTrace tailWord_444471 prefixEnd_444471 228227259984635738868421 := by
  unfold tailWord_444471
  simp only [CollatzResearch.WordTrace]
  refine ⟨16211189172764951448437267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10807459448509967632291511 16211189172764951448437267)
  ·
    refine ⟨24316783759147427172655901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16211189172764951448437267 24316783759147427172655901)
    ·
      refine ⟨9118793909680285189745963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24316783759147427172655901 9118793909680285189745963)
      ·
        refine ⟨13678190864520427784618945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9118793909680285189745963 13678190864520427784618945)
        ·
          refine ⟨10258643148390320838464209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13678190864520427784618945 10258643148390320838464209)
          ·
            refine ⟨7693982361292740628848157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10258643148390320838464209 7693982361292740628848157)
            ·
              refine ⟨2885243385484777735818059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7693982361292740628848157 2885243385484777735818059)
              ·
                refine ⟨4327865078227166603727089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885243385484777735818059 4327865078227166603727089)
                ·
                  refine ⟨3245898808670374952795317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4327865078227166603727089 3245898808670374952795317)
                  ·
                    refine ⟨304303013312847651824561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3245898808670374952795317 304303013312847651824561)
                    ·
                      refine ⟨228227259984635738868421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 304303013312847651824561 228227259984635738868421)
                      ·
                        rfl

theorem cell23_444471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 5, 2].length) (baseStart_444471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444471 prefixEnd_444471 := by exact prefixLift 444471
  have htrace : WordTrace (prefixWord ++ tailWord_444471) baseStart_444471 baseEnd_444471 := by
    simpa [prefixWord, tailWord_444471, baseEnd_444471] using wordTrace_append hprefix tailTrace_444471
  have hstable : (prefixWord ++ tailWord_444471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444471).length < 2 ^ (prefixWord ++ tailWord_444471).sum := by decide
  have hdescent : baseEnd_444471 < baseStart_444471 := by decide
  rcases family_descends (prefixWord ++ tailWord_444471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444501 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_444501 : Nat := 118140960795 + 444501 * 2 ^ 59
def prefixEnd_444501 : Nat := 4983230072969 + 3 ^ 40 * 444501 * 2
def baseEnd_444501 : Nat := 228242664404270621493283

theorem tailTrace_444501 : CollatzResearch.WordTrace tailWord_444501 prefixEnd_444501 228242664404270621493283 := by
  unfold tailWord_444501
  simp only [CollatzResearch.WordTrace]
  refine ⟨16212283362656266572029357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10808188908437511048019571 16212283362656266572029357)
  ·
    refine ⟨6079606260996099964511009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16212283362656266572029357 6079606260996099964511009)
    ·
      refine ⟨4559704695747074973383257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6079606260996099964511009 4559704695747074973383257)
      ·
        refine ⟨3419778521810306230037443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4559704695747074973383257 3419778521810306230037443)
        ·
          refine ⟨5129667782715459345056165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3419778521810306230037443 5129667782715459345056165)
          ·
            refine ⟨961812709259148627198031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5129667782715459345056165 961812709259148627198031)
            ·
              refine ⟨1442719063888722940797047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961812709259148627198031 1442719063888722940797047)
              ·
                refine ⟨2164078595833084411195571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442719063888722940797047 2164078595833084411195571)
                ·
                  refine ⟨3246117893749626616793357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164078595833084411195571 3246117893749626616793357)
                  ·
                    refine ⟨1217294210156109981297509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3246117893749626616793357 1217294210156109981297509)
                    ·
                      refine ⟨228242664404270621493283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1217294210156109981297509 228242664404270621493283)
                      ·
                        rfl

theorem cell23_444501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_444501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444501 prefixEnd_444501 := by exact prefixLift 444501
  have htrace : WordTrace (prefixWord ++ tailWord_444501) baseStart_444501 baseEnd_444501 := by
    simpa [prefixWord, tailWord_444501, baseEnd_444501] using wordTrace_append hprefix tailTrace_444501
  have hstable : (prefixWord ++ tailWord_444501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444501).length < 2 ^ (prefixWord ++ tailWord_444501).sum := by decide
  have hdescent : baseEnd_444501 < baseStart_444501 := by decide
  rcases family_descends (prefixWord ++ tailWord_444501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444502 : List Nat := [5, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_444502 : Nat := 118140960795 + 444502 * 2 ^ 59
def prefixEnd_444502 : Nat := 4983230072969 + 3 ^ 40 * 444502 * 2
def baseEnd_444502 : Nat := 25360353098325013064531

theorem tailTrace_444502 : CollatzResearch.WordTrace tailWord_444502 prefixEnd_444502 25360353098325013064531 := by
  unfold tailWord_444502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013269989728290233925985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10808213223768429161877173 1013269989728290233925985)
  ·
    refine ⟨759952492296217675444489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1013269989728290233925985 759952492296217675444489)
    ·
      refine ⟨569964369222163256583367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 759952492296217675444489 569964369222163256583367)
      ·
        refine ⟨854946553833244884875051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569964369222163256583367 854946553833244884875051)
        ·
          refine ⟨1282419830749867327312577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854946553833244884875051 1282419830749867327312577)
          ·
            refine ⟨961814873062400495484433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1282419830749867327312577 961814873062400495484433)
            ·
              refine ⟨721361154796800371613325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961814873062400495484433 721361154796800371613325)
              ·
                refine ⟨270510433048800139354997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 721361154796800371613325 270510433048800139354997)
                ·
                  refine ⟨25360353098325013064531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270510433048800139354997 25360353098325013064531)
                  ·
                    rfl

theorem cell23_444502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_444502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444502 prefixEnd_444502 := by exact prefixLift 444502
  have htrace : WordTrace (prefixWord ++ tailWord_444502) baseStart_444502 baseEnd_444502 := by
    simpa [prefixWord, tailWord_444502, baseEnd_444502] using wordTrace_append hprefix tailTrace_444502
  have hstable : (prefixWord ++ tailWord_444502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444502).length < 2 ^ (prefixWord ++ tailWord_444502).sum := by decide
  have hdescent : baseEnd_444502 < baseStart_444502 := by decide
  rcases family_descends (prefixWord ++ tailWord_444502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444521 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 4, 2, 3]
def baseStart_444521 : Nat := 118140960795 + 444521 * 2 ^ 59
def prefixEnd_444521 : Nat := 4983230072969 + 3 ^ 40 * 444521 * 2
def baseEnd_444521 : Nat := 228252934017360543243191

theorem tailTrace_444521 : CollatzResearch.WordTrace tailWord_444521 prefixEnd_444521 228252934017360543243191 := by
  unfold tailWord_444521
  simp only [CollatzResearch.WordTrace]
  refine ⟨16213012822583809987757417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10808675215055873325171611 16213012822583809987757417)
  ·
    refine ⟨12159759616937857490818063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16213012822583809987757417 12159759616937857490818063)
    ·
      refine ⟨18239639425406786236227095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12159759616937857490818063 18239639425406786236227095)
      ·
        refine ⟨27359459138110179354340643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18239639425406786236227095 27359459138110179354340643)
        ·
          refine ⟨41039188707165269031510965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27359459138110179354340643 41039188707165269031510965)
          ·
            refine ⟨3847423941296743971704153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41039188707165269031510965 3847423941296743971704153)
            ·
              refine ⟨2885567955972557978778115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3847423941296743971704153 2885567955972557978778115)
              ·
                refine ⟨4328351933958836968167173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885567955972557978778115 4328351933958836968167173)
                ·
                  refine ⟨811565987617281931531345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4328351933958836968167173 811565987617281931531345)
                  ·
                    refine ⟨608674490712961448648509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 811565987617281931531345 608674490712961448648509)
                    ·
                      refine ⟨228252934017360543243191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 608674490712961448648509 228252934017360543243191)
                      ·
                        rfl

theorem cell23_444521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 2, 3].length) (baseStart_444521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444521 prefixEnd_444521 := by exact prefixLift 444521
  have htrace : WordTrace (prefixWord ++ tailWord_444521) baseStart_444521 baseEnd_444521 := by
    simpa [prefixWord, tailWord_444521, baseEnd_444521] using wordTrace_append hprefix tailTrace_444521
  have hstable : (prefixWord ++ tailWord_444521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444521).length < 2 ^ (prefixWord ++ tailWord_444521).sum := by decide
  have hdescent : baseEnd_444521 < baseStart_444521 := by decide
  rcases family_descends (prefixWord ++ tailWord_444521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444528 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 3, 4]
def baseStart_444528 : Nat := 118140960795 + 444528 * 2 ^ 59
def prefixEnd_444528 : Nat := 4983230072969 + 3 ^ 40 * 444528 * 2
def baseEnd_444528 : Nat := 76085509460647338618553

theorem tailTrace_444528 : CollatzResearch.WordTrace tailWord_444528 prefixEnd_444528 76085509460647338618553 := by
  unfold tailWord_444528
  simp only [CollatzResearch.WordTrace]
  refine ⟨8106634066779225091631119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10808845422372300122174825 8106634066779225091631119)
  ·
    refine ⟨12159951100168837637446679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8106634066779225091631119 12159951100168837637446679)
    ·
      refine ⟨18239926650253256456170019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12159951100168837637446679 18239926650253256456170019)
      ·
        refine ⟨27359889975379884684255029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18239926650253256456170019 27359889975379884684255029)
        ·
          refine ⟨2564989685191864189148909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27359889975379884684255029 2564989685191864189148909)
          ·
            refine ⟨961871131946949070930841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2564989685191864189148909 961871131946949070930841)
            ·
              refine ⟨721403348960211803198131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961871131946949070930841 721403348960211803198131)
              ·
                refine ⟨1082105023440317704797197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721403348960211803198131 1082105023440317704797197)
                ·
                  refine ⟨405789383790119139298949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082105023440317704797197 405789383790119139298949)
                  ·
                    refine ⟨76085509460647338618553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 405789383790119139298949 76085509460647338618553)
                    ·
                      rfl

theorem cell23_444528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 3, 4].length) (baseStart_444528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444528 prefixEnd_444528 := by exact prefixLift 444528
  have htrace : WordTrace (prefixWord ++ tailWord_444528) baseStart_444528 baseEnd_444528 := by
    simpa [prefixWord, tailWord_444528, baseEnd_444528] using wordTrace_append hprefix tailTrace_444528
  have hstable : (prefixWord ++ tailWord_444528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444528).length < 2 ^ (prefixWord ++ tailWord_444528).sum := by decide
  have hdescent : baseEnd_444528 < baseStart_444528 := by decide
  rcases family_descends (prefixWord ++ tailWord_444528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444544 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 6]
def baseStart_444544 : Nat := 118140960795 + 444544 * 2 ^ 59
def prefixEnd_444544 : Nat := 4983230072969 + 3 ^ 40 * 444544 * 2
def baseEnd_444544 : Nat := 228264744072413953255585

theorem tailTrace_444544 : CollatzResearch.WordTrace tailWord_444544 prefixEnd_444544 228264744072413953255585 := by
  unfold tailWord_444544
  simp only [CollatzResearch.WordTrace]
  refine ⟨8106925850750242457922343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10809234467666989943896457 8106925850750242457922343)
  ·
    refine ⟨12160388776125363686883515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8106925850750242457922343 12160388776125363686883515)
    ·
      refine ⟨18240583164188045530325273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12160388776125363686883515 18240583164188045530325273)
      ·
        refine ⟨13680437373141034147743955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18240583164188045530325273 13680437373141034147743955)
        ·
          refine ⟨20520656059711551221615933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13680437373141034147743955 20520656059711551221615933)
          ·
            refine ⟨7695246022391831708105975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20520656059711551221615933 7695246022391831708105975)
            ·
              refine ⟨11542869033587747562158963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7695246022391831708105975 11542869033587747562158963)
              ·
                refine ⟨17314303550381621343238445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11542869033587747562158963 17314303550381621343238445)
                ·
                  refine ⟨6492863831393108003714417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17314303550381621343238445 6492863831393108003714417)
                  ·
                    refine ⟨4869647873544831002785813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6492863831393108003714417 4869647873544831002785813)
                    ·
                      refine ⟨228264744072413953255585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4869647873544831002785813 228264744072413953255585)
                      ·
                        rfl

theorem cell23_444544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_444544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444544 prefixEnd_444544 := by exact prefixLift 444544
  have htrace : WordTrace (prefixWord ++ tailWord_444544) baseStart_444544 baseEnd_444544 := by
    simpa [prefixWord, tailWord_444544, baseEnd_444544] using wordTrace_append hprefix tailTrace_444544
  have hstable : (prefixWord ++ tailWord_444544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444544).length < 2 ^ (prefixWord ++ tailWord_444544).sum := by decide
  have hdescent : baseEnd_444544 < baseStart_444544 := by decide
  rcases family_descends (prefixWord ++ tailWord_444544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444571 : List Nat := [1, 1, 1, 1, 1, 1, 2, 9, 1, 5]
def baseStart_444571 : Nat := 118140960795 + 444571 * 2 ^ 59
def prefixEnd_444571 : Nat := 4983230072969 + 3 ^ 40 * 444571 * 2
def baseEnd_444571 : Nat := 76092869350028449205987

theorem tailTrace_444571 : CollatzResearch.WordTrace tailWord_444571 prefixEnd_444571 76092869350028449205987 := by
  unfold tailWord_444571
  simp only [CollatzResearch.WordTrace]
  refine ⟨16214836472402668527077567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10809890981601779018051711 16214836472402668527077567)
  ·
    refine ⟨24322254708604002790616351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16214836472402668527077567 24322254708604002790616351)
    ·
      refine ⟨36483382062906004185924527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24322254708604002790616351 36483382062906004185924527)
      ·
        refine ⟨54725073094359006278886791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36483382062906004185924527 54725073094359006278886791)
        ·
          refine ⟨82087609641538509418330187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54725073094359006278886791 82087609641538509418330187)
          ·
            refine ⟨123131414462307764127495281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82087609641538509418330187 123131414462307764127495281)
            ·
              refine ⟨92348560846730823095621461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123131414462307764127495281 92348560846730823095621461)
              ·
                refine ⟨541104848711313416575907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 92348560846730823095621461 541104848711313416575907)
                ·
                  refine ⟨811657273066970124863861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541104848711313416575907 811657273066970124863861)
                  ·
                    refine ⟨76092869350028449205987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 811657273066970124863861 76092869350028449205987)
                    ·
                      rfl

theorem cell23_444571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 5].length) (baseStart_444571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444571 prefixEnd_444571 := by exact prefixLift 444571
  have htrace : WordTrace (prefixWord ++ tailWord_444571) baseStart_444571 baseEnd_444571 := by
    simpa [prefixWord, tailWord_444571, baseEnd_444571] using wordTrace_append hprefix tailTrace_444571
  have hstable : (prefixWord ++ tailWord_444571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444571).length < 2 ^ (prefixWord ++ tailWord_444571).sum := by decide
  have hdescent : baseEnd_444571 < baseStart_444571 := by decide
  rcases family_descends (prefixWord ++ tailWord_444571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444591 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 4]
def baseStart_444591 : Nat := 118140960795 + 444591 * 2 ^ 59
def prefixEnd_444591 : Nat := 4983230072969 + 3 ^ 40 * 444591 * 2
def baseEnd_444591 : Nat := 228288877663175269367869

theorem tailTrace_444591 : CollatzResearch.WordTrace tailWord_444591 prefixEnd_444591 228288877663175269367869 := by
  unfold tailWord_444591
  simp only [CollatzResearch.WordTrace]
  refine ⟨16215565932330211942805627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10810377288220141295203751 16215565932330211942805627)
  ·
    refine ⟨24323348898495317914208441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16215565932330211942805627 24323348898495317914208441)
    ·
      refine ⟨18242511673871488435656331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24323348898495317914208441 18242511673871488435656331)
      ·
        refine ⟨27363767510807232653484497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18242511673871488435656331 27363767510807232653484497)
        ·
          refine ⟨20522825633105424490113373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27363767510807232653484497 20522825633105424490113373)
          ·
            refine ⟨7696059612414534183792515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20522825633105424490113373 7696059612414534183792515)
            ·
              refine ⟨11544089418621801275688773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7696059612414534183792515 11544089418621801275688773)
              ·
                refine ⟨2164516765991587739191645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11544089418621801275688773 2164516765991587739191645)
                ·
                  refine ⟨811693787246845402196867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2164516765991587739191645 811693787246845402196867)
                  ·
                    refine ⟨1217540680870268103295301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 811693787246845402196867 1217540680870268103295301)
                    ·
                      refine ⟨228288877663175269367869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1217540680870268103295301 228288877663175269367869)
                      ·
                        rfl

theorem cell23_444591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_444591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444591 prefixEnd_444591 := by exact prefixLift 444591
  have htrace : WordTrace (prefixWord ++ tailWord_444591) baseStart_444591 baseEnd_444591 := by
    simpa [prefixWord, tailWord_444591, baseEnd_444591] using wordTrace_append hprefix tailTrace_444591
  have hstable : (prefixWord ++ tailWord_444591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444591).length < 2 ^ (prefixWord ++ tailWord_444591).sum := by decide
  have hdescent : baseEnd_444591 < baseStart_444591 := by decide
  rcases family_descends (prefixWord ++ tailWord_444591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444601 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 1, 6]
def baseStart_444601 : Nat := 118140960795 + 444601 * 2 ^ 59
def prefixEnd_444601 : Nat := 4983230072969 + 3 ^ 40 * 444601 * 2
def baseEnd_444601 : Nat := 76098004156573410080941

theorem tailTrace_444601 : CollatzResearch.WordTrace tailWord_444601 prefixEnd_444601 76098004156573410080941 := by
  unfold tailWord_444601
  simp only [CollatzResearch.WordTrace]
  refine ⟨16215930662293983650669657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10810620441529322433779771 16215930662293983650669657)
  ·
    refine ⟨12161947996720487738002243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16215930662293983650669657 12161947996720487738002243)
    ·
      refine ⟨18242921995080731607003365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12161947996720487738002243 18242921995080731607003365)
      ·
        refine ⟨3420547874077637176313131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18242921995080731607003365 3420547874077637176313131)
        ·
          refine ⟨5130821811116455764469697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3420547874077637176313131 5130821811116455764469697)
          ·
            refine ⟨3848116358337341823352273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5130821811116455764469697 3848116358337341823352273)
            ·
              refine ⟨2886087268753006367514205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3848116358337341823352273 2886087268753006367514205)
              ·
                refine ⟨1082282725782377387817827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2886087268753006367514205 1082282725782377387817827)
                ·
                  refine ⟨1623424088673566081726741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1082282725782377387817827 1623424088673566081726741)
                  ·
                    refine ⟨76098004156573410080941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1623424088673566081726741 76098004156573410080941)
                    ·
                      rfl

theorem cell23_444601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 6].length) (baseStart_444601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444601 prefixEnd_444601 := by exact prefixLift 444601
  have htrace : WordTrace (prefixWord ++ tailWord_444601) baseStart_444601 baseEnd_444601 := by
    simpa [prefixWord, tailWord_444601, baseEnd_444601] using wordTrace_append hprefix tailTrace_444601
  have hstable : (prefixWord ++ tailWord_444601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444601).length < 2 ^ (prefixWord ++ tailWord_444601).sum := by decide
  have hdescent : baseEnd_444601 < baseStart_444601 := by decide
  rcases family_descends (prefixWord ++ tailWord_444601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444608 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 4]
def baseStart_444608 : Nat := 118140960795 + 444608 * 2 ^ 59
def prefixEnd_444608 : Nat := 4983230072969 + 3 ^ 40 * 444608 * 2
def baseEnd_444608 : Nat := 228297606834301702855291

theorem tailTrace_444608 : CollatzResearch.WordTrace tailWord_444608 prefixEnd_444608 228297606834301702855291 := by
  unfold tailWord_444608
  simp only [CollatzResearch.WordTrace]
  refine ⟨8108092986634311923087239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10810790648845749230782985 8108092986634311923087239)
  ·
    refine ⟨12162139479951467884630859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8108092986634311923087239 12162139479951467884630859)
    ·
      refine ⟨18243209219927201826946289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12162139479951467884630859 18243209219927201826946289)
      ·
        refine ⟨13682406914945401370209717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18243209219927201826946289 13682406914945401370209717)
        ·
          refine ⟨1282725648276131378457161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13682406914945401370209717 1282725648276131378457161)
          ·
            refine ⟨962044236207098533842871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1282725648276131378457161 962044236207098533842871)
            ·
              refine ⟨1443066354310647800764307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962044236207098533842871 1443066354310647800764307)
              ·
                refine ⟨2164599531465971701146461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443066354310647800764307 2164599531465971701146461)
                ·
                  refine ⟨811724824299739387929923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2164599531465971701146461 811724824299739387929923)
                  ·
                    refine ⟨1217587236449609081894885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 811724824299739387929923 1217587236449609081894885)
                    ·
                      refine ⟨228297606834301702855291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1217587236449609081894885 228297606834301702855291)
                      ·
                        rfl

theorem cell23_444608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_444608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444608 prefixEnd_444608 := by exact prefixLift 444608
  have htrace : WordTrace (prefixWord ++ tailWord_444608) baseStart_444608 baseEnd_444608 := by
    simpa [prefixWord, tailWord_444608, baseEnd_444608] using wordTrace_append hprefix tailTrace_444608
  have hstable : (prefixWord ++ tailWord_444608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444608).length < 2 ^ (prefixWord ++ tailWord_444608).sum := by decide
  have hdescent : baseEnd_444608 < baseStart_444608 := by decide
  rcases family_descends (prefixWord ++ tailWord_444608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444612 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_444612 : Nat := 118140960795 + 444612 * 2 ^ 59
def prefixEnd_444612 : Nat := 4983230072969 + 3 ^ 40 * 444612 * 2
def baseEnd_444612 : Nat := 228299660756919687205273

theorem tailTrace_444612 : CollatzResearch.WordTrace tailWord_444612 prefixEnd_444612 228299660756919687205273 := by
  unfold tailWord_444612
  simp only [CollatzResearch.WordTrace]
  refine ⟨8108165932627066264660045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10810887910169421686213393 8108165932627066264660045)
  ·
    refine ⟨3040562224735149849247517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8108165932627066264660045 3040562224735149849247517)
    ·
      refine ⟨1140210834275681193467819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3040562224735149849247517 1140210834275681193467819)
      ·
        refine ⟨1710316251413521790201729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1140210834275681193467819 1710316251413521790201729)
        ·
          refine ⟨1282737188560141342651297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1710316251413521790201729 1282737188560141342651297)
          ·
            refine ⟨962052891420106006988473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1282737188560141342651297 962052891420106006988473)
            ·
              refine ⟨721539668565079505241355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962052891420106006988473 721539668565079505241355)
              ·
                refine ⟨1082309502847619257862033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721539668565079505241355 1082309502847619257862033)
                ·
                  refine ⟨811732127135714443396525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1082309502847619257862033 811732127135714443396525)
                  ·
                    refine ⟨304399547675892916273697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 811732127135714443396525 304399547675892916273697)
                    ·
                      refine ⟨228299660756919687205273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 304399547675892916273697 228299660756919687205273)
                      ·
                        rfl

theorem cell23_444612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_444612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444612 prefixEnd_444612 := by exact prefixLift 444612
  have htrace : WordTrace (prefixWord ++ tailWord_444612) baseStart_444612 baseEnd_444612 := by
    simpa [prefixWord, tailWord_444612, baseEnd_444612] using wordTrace_append hprefix tailTrace_444612
  have hstable : (prefixWord ++ tailWord_444612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444612).length < 2 ^ (prefixWord ++ tailWord_444612).sum := by decide
  have hdescent : baseEnd_444612 < baseStart_444612 := by decide
  rcases family_descends (prefixWord ++ tailWord_444612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444636 : List Nat := [2, 2, 5, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_444636 : Nat := 118140960795 + 444636 * 2 ^ 59
def prefixEnd_444636 : Nat := 4983230072969 + 3 ^ 40 * 444636 * 2
def baseEnd_444636 : Nat := 228311984292627593305163

theorem tailTrace_444636 : CollatzResearch.WordTrace tailWord_444636 prefixEnd_444636 228311984292627593305163 := by
  unfold tailWord_444636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8108603608583592314096881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10811471478111456418795841 8108603608583592314096881)
  ·
    refine ⟨6081452706437694235572661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8108603608583592314096881 6081452706437694235572661)
    ·
      refine ⟨570136191228533834584937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6081452706437694235572661 570136191228533834584937)
      ·
        refine ⟨427602143421400375938703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570136191228533834584937 427602143421400375938703)
        ·
          refine ⟨641403215132100563908055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427602143421400375938703 641403215132100563908055)
          ·
            refine ⟨962104822698150845862083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641403215132100563908055 962104822698150845862083)
            ·
              refine ⟨1443157234047226268793125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962104822698150845862083 1443157234047226268793125)
              ·
                refine ⟨270591981383854925398711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1443157234047226268793125 270591981383854925398711)
                ·
                  refine ⟨405887972075782388098067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270591981383854925398711 405887972075782388098067)
                  ·
                    refine ⟨608831958113673582147101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 405887972075782388098067 608831958113673582147101)
                    ·
                      refine ⟨228311984292627593305163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 608831958113673582147101 228311984292627593305163)
                      ·
                        rfl

theorem cell23_444636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_444636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444636 prefixEnd_444636 := by exact prefixLift 444636
  have htrace : WordTrace (prefixWord ++ tailWord_444636) baseStart_444636 baseEnd_444636 := by
    simpa [prefixWord, tailWord_444636, baseEnd_444636] using wordTrace_append hprefix tailTrace_444636
  have hstable : (prefixWord ++ tailWord_444636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444636).length < 2 ^ (prefixWord ++ tailWord_444636).sum := by decide
  have hdescent : baseEnd_444636 < baseStart_444636 := by decide
  rcases family_descends (prefixWord ++ tailWord_444636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444648 : List Nat := [2, 1, 4, 1, 2, 4, 1, 8]
def baseStart_444648 : Nat := 118140960795 + 444648 * 2 ^ 59
def prefixEnd_444648 : Nat := 4983230072969 + 3 ^ 40 * 444648 * 2
def baseEnd_444648 : Nat := 8456227631869686902041

theorem tailTrace_444648 : CollatzResearch.WordTrace tailWord_444648 prefixEnd_444648 8456227631869686902041 := by
  unfold tailWord_444648
  simp only [CollatzResearch.WordTrace]
  refine ⟨8108822446561855338815299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10811763262082473785087065 8108822446561855338815299)
  ·
    refine ⟨12163233669842783008222949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8108822446561855338815299 12163233669842783008222949)
    ·
      refine ⟨2280606313095521814041803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12163233669842783008222949 2280606313095521814041803)
      ·
        refine ⟨3420909469643282721062705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2280606313095521814041803 3420909469643282721062705)
        ·
          refine ⟨2565682102232462040797029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3420909469643282721062705 2565682102232462040797029)
          ·
            refine ⟨481065394168586632649443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2565682102232462040797029 481065394168586632649443)
            ·
              refine ⟨721598091252879948974165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481065394168586632649443 721598091252879948974165)
              ·
                refine ⟨8456227631869686902041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 721598091252879948974165 8456227631869686902041)
                ·
                  rfl

theorem cell23_444648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 8].length) (baseStart_444648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444648 prefixEnd_444648 := by exact prefixLift 444648
  have htrace : WordTrace (prefixWord ++ tailWord_444648) baseStart_444648 baseEnd_444648 := by
    simpa [prefixWord, tailWord_444648, baseEnd_444648] using wordTrace_append hprefix tailTrace_444648
  have hstable : (prefixWord ++ tailWord_444648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444648).length < 2 ^ (prefixWord ++ tailWord_444648).sum := by decide
  have hdescent : baseEnd_444648 < baseStart_444648 := by decide
  rcases family_descends (prefixWord ++ tailWord_444648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444671 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 5]
def baseStart_444671 : Nat := 118140960795 + 444671 * 2 ^ 59
def prefixEnd_444671 : Nat := 4983230072969 + 3 ^ 40 * 444671 * 2
def baseEnd_444671 : Nat := 228329956115534956367501

theorem tailTrace_444671 : CollatzResearch.WordTrace tailWord_444671 prefixEnd_444671 228329956115534956367501 := by
  unfold tailWord_444671
  simp only [CollatzResearch.WordTrace]
  refine ⟨16218483772040385605717867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10812322514693590403811911 16218483772040385605717867)
  ·
    refine ⟨24327725658060578408576801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16218483772040385605717867 24327725658060578408576801)
    ·
      refine ⟨18245794243545433806432601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24327725658060578408576801 18245794243545433806432601)
      ·
        refine ⟨13684345682659075354824451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18245794243545433806432601 13684345682659075354824451)
        ·
          refine ⟨20526518523988613032236677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13684345682659075354824451 20526518523988613032236677)
          ·
            refine ⟨3848722223247864943544377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20526518523988613032236677 3848722223247864943544377)
            ·
              refine ⟨2886541667435898707658283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3848722223247864943544377 2886541667435898707658283)
              ·
                refine ⟨4329812501153848061487425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886541667435898707658283 4329812501153848061487425)
                ·
                  refine ⟨3247359375865386046115569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4329812501153848061487425 3247359375865386046115569)
                  ·
                    refine ⟨2435519531899039534586677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3247359375865386046115569 2435519531899039534586677)
                    ·
                      refine ⟨228329956115534956367501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2435519531899039534586677 228329956115534956367501)
                      ·
                        rfl

theorem cell23_444671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_444671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444671 prefixEnd_444671 := by exact prefixLift 444671
  have htrace : WordTrace (prefixWord ++ tailWord_444671) baseStart_444671 baseEnd_444671 := by
    simpa [prefixWord, tailWord_444671, baseEnd_444671] using wordTrace_append hprefix tailTrace_444671
  have hstable : (prefixWord ++ tailWord_444671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444671).length < 2 ^ (prefixWord ++ tailWord_444671).sum := by decide
  have hdescent : baseEnd_444671 < baseStart_444671 := by decide
  rcases family_descends (prefixWord ++ tailWord_444671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444676 : List Nat := [2, 3, 2, 2, 3, 1, 2, 3, 1, 2, 2]
def baseStart_444676 : Nat := 118140960795 + 444676 * 2 ^ 59
def prefixEnd_444676 : Nat := 4983230072969 + 3 ^ 40 * 444676 * 2
def baseEnd_444676 : Nat := 228332523518807436804979

theorem tailTrace_444676 : CollatzResearch.WordTrace tailWord_444676 prefixEnd_444676 228332523518807436804979 := by
  unfold tailWord_444676
  simp only [CollatzResearch.WordTrace]
  refine ⟨8109333068511135729824941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10812444091348180973099921 8109333068511135729824941)
  ·
    refine ⟨3040999900691675898684353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8109333068511135729824941 3040999900691675898684353)
    ·
      refine ⟨2280749925518756924013265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3040999900691675898684353 2280749925518756924013265)
      ·
        refine ⟨1710562444139067693009949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2280749925518756924013265 1710562444139067693009949)
        ·
          refine ⟨641460916552150384878731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1710562444139067693009949 641460916552150384878731)
          ·
            refine ⟨962191374828225577318097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641460916552150384878731 962191374828225577318097)
            ·
              refine ⟨721643531121169182988573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962191374828225577318097 721643531121169182988573)
              ·
                refine ⟨270616324170438443620715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 721643531121169182988573 270616324170438443620715)
                ·
                  refine ⟨405924486255657665431073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270616324170438443620715 405924486255657665431073)
                  ·
                    refine ⟨304443364691743249073305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 405924486255657665431073 304443364691743249073305)
                    ·
                      refine ⟨228332523518807436804979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 304443364691743249073305 228332523518807436804979)
                      ·
                        rfl

theorem cell23_444676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_444676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444676 prefixEnd_444676 := by exact prefixLift 444676
  have htrace : WordTrace (prefixWord ++ tailWord_444676) baseStart_444676 baseEnd_444676 := by
    simpa [prefixWord, tailWord_444676, baseEnd_444676] using wordTrace_append hprefix tailTrace_444676
  have hstable : (prefixWord ++ tailWord_444676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444676).length < 2 ^ (prefixWord ++ tailWord_444676).sum := by decide
  have hdescent : baseEnd_444676 < baseStart_444676 := by decide
  rcases family_descends (prefixWord ++ tailWord_444676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444708 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_444708 : Nat := 118140960795 + 444708 * 2 ^ 59
def prefixEnd_444708 : Nat := 4983230072969 + 3 ^ 40 * 444708 * 2
def baseEnd_444708 : Nat := 76116318299917103868277

theorem tailTrace_444708 : CollatzResearch.WordTrace tailWord_444708 prefixEnd_444708 76116318299917103868277 := by
  unfold tailWord_444708
  simp only [CollatzResearch.WordTrace]
  refine ⟨8109916636453170462407389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10813222181937560616543185 8109916636453170462407389)
  ·
    refine ⟨3041218738669938923402771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8109916636453170462407389 3041218738669938923402771)
    ·
      refine ⟨4561828108004908385104157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3041218738669938923402771 4561828108004908385104157)
      ·
        refine ⟨1710685540501840644414059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4561828108004908385104157 1710685540501840644414059)
        ·
          refine ⟨2566028310752760966621089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1710685540501840644414059 2566028310752760966621089)
          ·
            refine ⟨1924521233064570724965817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2566028310752760966621089 1924521233064570724965817)
            ·
              refine ⟨1443390924798428043724363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1924521233064570724965817 1443390924798428043724363)
              ·
                refine ⟨2165086387197642065586545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443390924798428043724363 2165086387197642065586545)
                ·
                  refine ⟨1623814790398231549189909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2165086387197642065586545 1623814790398231549189909)
                  ·
                    refine ⟨76116318299917103868277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1623814790398231549189909 76116318299917103868277)
                    ·
                      rfl

theorem cell23_444708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_444708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444708 prefixEnd_444708 := by exact prefixLift 444708
  have htrace : WordTrace (prefixWord ++ tailWord_444708) baseStart_444708 baseEnd_444708 := by
    simpa [prefixWord, tailWord_444708, baseEnd_444708] using wordTrace_append hprefix tailTrace_444708
  have hstable : (prefixWord ++ tailWord_444708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444708).length < 2 ^ (prefixWord ++ tailWord_444708).sum := by decide
  have hdescent : baseEnd_444708 < baseStart_444708 := by decide
  rcases family_descends (prefixWord ++ tailWord_444708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444709 : List Nat := [1, 3, 1, 2, 5, 1, 3, 1, 2, 1, 3]
def baseStart_444709 : Nat := 118140960795 + 444709 * 2 ^ 59
def prefixEnd_444709 : Nat := 4983230072969 + 3 ^ 40 * 444709 * 2
def baseEnd_444709 : Nat := 228349468380405807692327

theorem tailTrace_444709 : CollatzResearch.WordTrace tailWord_444709 prefixEnd_444709 228349468380405807692327 := by
  unfold tailWord_444709
  simp only [CollatzResearch.WordTrace]
  refine ⟨16219869745902718095601181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10813246497268478730400787 16219869745902718095601181)
  ·
    refine ⟨6082451154713519285850443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16219869745902718095601181 6082451154713519285850443)
    ·
      refine ⟨9123676732070278928775665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6082451154713519285850443 9123676732070278928775665)
      ·
        refine ⟨6842757549052709196581749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9123676732070278928775665 6842757549052709196581749)
        ·
          refine ⟨641508520223691487179539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6842757549052709196581749 641508520223691487179539)
          ·
            refine ⟨962262780335537230769309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641508520223691487179539 962262780335537230769309)
            ·
              refine ⟨360848542625826461538491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 962262780335537230769309 360848542625826461538491)
              ·
                refine ⟨541272813938739692307737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360848542625826461538491 541272813938739692307737)
                ·
                  refine ⟨405954610454054769230803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541272813938739692307737 405954610454054769230803)
                  ·
                    refine ⟨608931915681082153846205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 405954610454054769230803 608931915681082153846205)
                    ·
                      refine ⟨228349468380405807692327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 608931915681082153846205 228349468380405807692327)
                      ·
                        rfl

theorem cell23_444709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_444709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444709 prefixEnd_444709 := by exact prefixLift 444709
  have htrace : WordTrace (prefixWord ++ tailWord_444709) baseStart_444709 baseEnd_444709 := by
    simpa [prefixWord, tailWord_444709, baseEnd_444709] using wordTrace_append hprefix tailTrace_444709
  have hstable : (prefixWord ++ tailWord_444709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444709).length < 2 ^ (prefixWord ++ tailWord_444709).sum := by decide
  have hdescent : baseEnd_444709 < baseStart_444709 := by decide
  rcases family_descends (prefixWord ++ tailWord_444709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444741 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_444741 : Nat := 118140960795 + 444741 * 2 ^ 59
def prefixEnd_444741 : Nat := 4983230072969 + 3 ^ 40 * 444741 * 2
def baseEnd_444741 : Nat := 228365899761349682492179

theorem tailTrace_444741 : CollatzResearch.WordTrace tailWord_444741 prefixEnd_444741 228365899761349682492179 := by
  unfold tailWord_444741
  simp only [CollatzResearch.WordTrace]
  refine ⟨16221036881786787560766077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10814024587857858373844051 16221036881786787560766077)
  ·
    refine ⟨6082888830670045335287279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16221036881786787560766077 6082888830670045335287279)
    ·
      refine ⟨9124333246005068002930919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6082888830670045335287279 9124333246005068002930919)
      ·
        refine ⟨13686499869007602004396379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9124333246005068002930919 13686499869007602004396379)
        ·
          refine ⟨20529749803511403006594569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13686499869007602004396379 20529749803511403006594569)
          ·
            refine ⟨15397312352633552254945927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20529749803511403006594569 15397312352633552254945927)
            ·
              refine ⟨23095968528950328382418891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15397312352633552254945927 23095968528950328382418891)
              ·
                refine ⟨34643952793425492573628337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23095968528950328382418891 34643952793425492573628337)
                ·
                  refine ⟨25982964595069119430221253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34643952793425492573628337 25982964595069119430221253)
                  ·
                    refine ⟨4871805861575459893166485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25982964595069119430221253 4871805861575459893166485)
                    ·
                      refine ⟨228365899761349682492179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4871805861575459893166485 228365899761349682492179)
                      ·
                        rfl

theorem cell23_444741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_444741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444741 prefixEnd_444741 := by exact prefixLift 444741
  have htrace : WordTrace (prefixWord ++ tailWord_444741) baseStart_444741 baseEnd_444741 := by
    simpa [prefixWord, tailWord_444741, baseEnd_444741] using wordTrace_append hprefix tailTrace_444741
  have hstable : (prefixWord ++ tailWord_444741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444741).length < 2 ^ (prefixWord ++ tailWord_444741).sum := by decide
  have hdescent : baseEnd_444741 < baseStart_444741 := by decide
  rcases family_descends (prefixWord ++ tailWord_444741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444751 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 3, 7]
def baseStart_444751 : Nat := 118140960795 + 444751 * 2 ^ 59
def prefixEnd_444751 : Nat := 4983230072969 + 3 ^ 40 * 444751 * 2
def baseEnd_444751 : Nat := 76123678189298214455711

theorem tailTrace_444751 : CollatzResearch.WordTrace tailWord_444751 prefixEnd_444751 76123678189298214455711 := by
  unfold tailWord_444751
  simp only [CollatzResearch.WordTrace]
  refine ⟨16221401611750559268630107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10814267741167039512420071 16221401611750559268630107)
  ·
    refine ⟨24332102417625838902945161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16221401611750559268630107 24332102417625838902945161)
    ·
      refine ⟨18249076813219379177208871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24332102417625838902945161 18249076813219379177208871)
      ·
        refine ⟨27373615219829068765813307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18249076813219379177208871 27373615219829068765813307)
        ·
          refine ⟨41060422829743603148719961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27373615219829068765813307 41060422829743603148719961)
          ·
            refine ⟨30795317122307702361539971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41060422829743603148719961 30795317122307702361539971)
            ·
              refine ⟨46192975683461553542309957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30795317122307702361539971 46192975683461553542309957)
              ·
                refine ⟨8661182940649041289183117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46192975683461553542309957 8661182940649041289183117)
                ·
                  refine ⟨3247943602743390483443669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8661182940649041289183117 3247943602743390483443669)
                  ·
                    refine ⟨76123678189298214455711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3247943602743390483443669 76123678189298214455711)
                    ·
                      rfl

theorem cell23_444751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_444751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444751 prefixEnd_444751 := by exact prefixLift 444751
  have htrace : WordTrace (prefixWord ++ tailWord_444751) baseStart_444751 baseEnd_444751 := by
    simpa [prefixWord, tailWord_444751, baseEnd_444751] using wordTrace_append hprefix tailTrace_444751
  have hstable : (prefixWord ++ tailWord_444751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444751).length < 2 ^ (prefixWord ++ tailWord_444751).sum := by decide
  have hdescent : baseEnd_444751 < baseStart_444751 := by decide
  rcases family_descends (prefixWord ++ tailWord_444751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444805 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 2, 4, 2]
def baseStart_444805 : Nat := 118140960795 + 444805 * 2 ^ 59
def prefixEnd_444805 : Nat := 4983230072969 + 3 ^ 40 * 444805 * 2
def baseEnd_444805 : Nat := 228398762523237432091885

theorem tailTrace_444805 : CollatzResearch.WordTrace tailWord_444805 prefixEnd_444805 228398762523237432091885 := by
  unfold tailWord_444805
  simp only [CollatzResearch.WordTrace]
  refine ⟨16223371153554926491095869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10815580769036617660730579 16223371153554926491095869)
  ·
    refine ⟨6083764182583097434160951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16223371153554926491095869 6083764182583097434160951)
    ·
      refine ⟨9125646273874646151241427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6083764182583097434160951 9125646273874646151241427)
      ·
        refine ⟨13688469410811969226862141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9125646273874646151241427 13688469410811969226862141)
        ·
          refine ⟨5133176029054488460073303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13688469410811969226862141 5133176029054488460073303)
          ·
            refine ⟨7699764043581732690109955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5133176029054488460073303 7699764043581732690109955)
            ·
              refine ⟨11549646065372599035164933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7699764043581732690109955 11549646065372599035164933)
              ·
                refine ⟨2165558637257362319093425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11549646065372599035164933 2165558637257362319093425)
                ·
                  refine ⟨1624168977943021739320069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2165558637257362319093425 1624168977943021739320069)
                  ·
                    refine ⟨304531683364316576122513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1624168977943021739320069 304531683364316576122513)
                    ·
                      refine ⟨228398762523237432091885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 304531683364316576122513 228398762523237432091885)
                      ·
                        rfl

theorem cell23_444805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 4, 2].length) (baseStart_444805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444805 prefixEnd_444805 := by exact prefixLift 444805
  have htrace : WordTrace (prefixWord ++ tailWord_444805) baseStart_444805 baseEnd_444805 := by
    simpa [prefixWord, tailWord_444805, baseEnd_444805] using wordTrace_append hprefix tailTrace_444805
  have hstable : (prefixWord ++ tailWord_444805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444805).length < 2 ^ (prefixWord ++ tailWord_444805).sum := by decide
  have hdescent : baseEnd_444805 < baseStart_444805 := by decide
  rcases family_descends (prefixWord ++ tailWord_444805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444808 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_444808 : Nat := 118140960795 + 444808 * 2 ^ 59
def prefixEnd_444808 : Nat := 4983230072969 + 3 ^ 40 * 444808 * 2
def baseEnd_444808 : Nat := 228400302965200920354371

theorem tailTrace_444808 : CollatzResearch.WordTrace tailWord_444808 prefixEnd_444808 228400302965200920354371 := by
  unfold tailWord_444808
  simp only [CollatzResearch.WordTrace]
  refine ⟨8111740286272029001727539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10815653715029372002303385 8111740286272029001727539)
  ·
    refine ⟨12167610429408043502591309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8111740286272029001727539 12167610429408043502591309)
    ·
      refine ⟨4562853911028016313471741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12167610429408043502591309 4562853911028016313471741)
      ·
        refine ⟨1711070216635506117551903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4562853911028016313471741 1711070216635506117551903)
        ·
          refine ⟨2566605324953259176327855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1711070216635506117551903 2566605324953259176327855)
          ·
            refine ⟨3849907987429888764491783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566605324953259176327855 3849907987429888764491783)
            ·
              refine ⟨5774861981144833146737675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3849907987429888764491783 5774861981144833146737675)
              ·
                refine ⟨8662292971717249720106513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5774861981144833146737675 8662292971717249720106513)
                ·
                  refine ⟨6496719728787937290079885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8662292971717249720106513 6496719728787937290079885)
                  ·
                    refine ⟨2436269898295476483779957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6496719728787937290079885 2436269898295476483779957)
                    ·
                      refine ⟨228400302965200920354371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2436269898295476483779957 228400302965200920354371)
                      ·
                        rfl

theorem cell23_444808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_444808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444808 prefixEnd_444808 := by exact prefixLift 444808
  have htrace : WordTrace (prefixWord ++ tailWord_444808) baseStart_444808 baseEnd_444808 := by
    simpa [prefixWord, tailWord_444808, baseEnd_444808] using wordTrace_append hprefix tailTrace_444808
  have hstable : (prefixWord ++ tailWord_444808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444808).length < 2 ^ (prefixWord ++ tailWord_444808).sum := by decide
  have hdescent : baseEnd_444808 < baseStart_444808 := by decide
  rcases family_descends (prefixWord ++ tailWord_444808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444849 : List Nat := [1, 2, 2, 4, 1, 3, 2, 3, 1, 4]
def baseStart_444849 : Nat := 118140960795 + 444849 * 2 ^ 59
def prefixEnd_444849 : Nat := 4983230072969 + 3 ^ 40 * 444849 * 2
def baseEnd_444849 : Nat := 76140451890678419980561

theorem tailTrace_444849 : CollatzResearch.WordTrace tailWord_444849 prefixEnd_444849 76140451890678419980561 := by
  unfold tailWord_444849
  simp only [CollatzResearch.WordTrace]
  refine ⟨16224975965395522005697601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10816650643597014670465067 16224975965395522005697601)
  ·
    refine ⟨12168731974046641504273201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16224975965395522005697601 12168731974046641504273201)
    ·
      refine ⟨9126548980534981128204901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12168731974046641504273201 9126548980534981128204901)
      ·
        refine ⟨1711227933850308961538419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9126548980534981128204901 1711227933850308961538419)
        ·
          refine ⟨2566841900775463442307629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1711227933850308961538419 2566841900775463442307629)
          ·
            refine ⟨962565712790798790865361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2566841900775463442307629 962565712790798790865361)
            ·
              refine ⟨721924284593099093149021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962565712790798790865361 721924284593099093149021)
              ·
                refine ⟨270721606722412159930883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 721924284593099093149021 270721606722412159930883)
                ·
                  refine ⟨406082410083618239896325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270721606722412159930883 406082410083618239896325)
                  ·
                    refine ⟨76140451890678419980561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 406082410083618239896325 76140451890678419980561)
                    ·
                      rfl

theorem cell23_444849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_444849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444849 prefixEnd_444849 := by exact prefixLift 444849
  have htrace : WordTrace (prefixWord ++ tailWord_444849) baseStart_444849 baseEnd_444849 := by
    simpa [prefixWord, tailWord_444849, baseEnd_444849] using wordTrace_append hprefix tailTrace_444849
  have hstable : (prefixWord ++ tailWord_444849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444849).length < 2 ^ (prefixWord ++ tailWord_444849).sum := by decide
  have hdescent : baseEnd_444849 < baseStart_444849 := by decide
  rcases family_descends (prefixWord ++ tailWord_444849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444872 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 3, 1, 3]
def baseStart_444872 : Nat := 118140960795 + 444872 * 2 ^ 59
def prefixEnd_444872 : Nat := 4983230072969 + 3 ^ 40 * 444872 * 2
def baseEnd_444872 : Nat := 228433165727088669954077

theorem tailTrace_444872 : CollatzResearch.WordTrace tailWord_444872 prefixEnd_444872 228433165727088669954077 := by
  unfold tailWord_444872
  simp only [CollatzResearch.WordTrace]
  refine ⟨8112907422156098466892435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10817209896208131289189913 8112907422156098466892435)
  ·
    refine ⟨12169361133234147700338653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8112907422156098466892435 12169361133234147700338653)
    ·
      refine ⟨4563510424962805387626995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12169361133234147700338653 4563510424962805387626995)
      ·
        refine ⟨6845265637444208081440493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4563510424962805387626995 6845265637444208081440493)
        ·
          refine ⟨2566974614041578030540185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6845265637444208081440493 2566974614041578030540185)
          ·
            refine ⟨1925230960531183522905139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2566974614041578030540185 1925230960531183522905139)
            ·
              refine ⟨2887846440796775284357709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925230960531183522905139 2887846440796775284357709)
              ·
                refine ⟨1082942415298790731634141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2887846440796775284357709 1082942415298790731634141)
                ·
                  refine ⟨406103405737046524362803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082942415298790731634141 406103405737046524362803)
                  ·
                    refine ⟨609155108605569786544205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 406103405737046524362803 609155108605569786544205)
                    ·
                      refine ⟨228433165727088669954077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 609155108605569786544205 228433165727088669954077)
                      ·
                        rfl

theorem cell23_444872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_444872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444872 prefixEnd_444872 := by exact prefixLift 444872
  have htrace : WordTrace (prefixWord ++ tailWord_444872) baseStart_444872 baseEnd_444872 := by
    simpa [prefixWord, tailWord_444872, baseEnd_444872] using wordTrace_append hprefix tailTrace_444872
  have hstable : (prefixWord ++ tailWord_444872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444872).length < 2 ^ (prefixWord ++ tailWord_444872).sum := by decide
  have hdescent : baseEnd_444872 < baseStart_444872 := by decide
  rcases family_descends (prefixWord ++ tailWord_444872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444906 : List Nat := [3, 1, 3, 1, 3, 1, 3, 3, 1, 1, 3]
def baseStart_444906 : Nat := 118140960795 + 444906 * 2 ^ 59
def prefixEnd_444906 : Nat := 4983230072969 + 3 ^ 40 * 444906 * 2
def baseEnd_444906 : Nat := 228450624069341536928921

theorem tailTrace_444906 : CollatzResearch.WordTrace tailWord_444906 prefixEnd_444906 228450624069341536928921 := by
  unfold tailWord_444906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4056763731547255185130643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10818036617459347160348381 4056763731547255185130643)
  ·
    refine ⟨6085145597320882777695965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4056763731547255185130643 6085145597320882777695965)
    ·
      refine ⟨2281929598995331041635987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6085145597320882777695965 2281929598995331041635987)
      ·
        refine ⟨3422894398492996562453981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2281929598995331041635987 3422894398492996562453981)
        ·
          refine ⟨1283585399434873710920243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3422894398492996562453981 1283585399434873710920243)
          ·
            refine ⟨1925378099152310566380365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283585399434873710920243 1925378099152310566380365)
            ·
              refine ⟨722016787182116462392637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1925378099152310566380365 722016787182116462392637)
              ·
                refine ⟨270756295193293673397239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 722016787182116462392637 270756295193293673397239)
                ·
                  refine ⟨406134442789940510095859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270756295193293673397239 406134442789940510095859)
                  ·
                    refine ⟨609201664184910765143789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 406134442789940510095859 609201664184910765143789)
                    ·
                      refine ⟨228450624069341536928921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 609201664184910765143789 228450624069341536928921)
                      ·
                        rfl

theorem cell23_444906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_444906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444906 prefixEnd_444906 := by exact prefixLift 444906
  have htrace : WordTrace (prefixWord ++ tailWord_444906) baseStart_444906 baseEnd_444906 := by
    simpa [prefixWord, tailWord_444906, baseEnd_444906] using wordTrace_append hprefix tailTrace_444906
  have hstable : (prefixWord ++ tailWord_444906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444906).length < 2 ^ (prefixWord ++ tailWord_444906).sum := by decide
  have hdescent : baseEnd_444906 < baseStart_444906 := by decide
  rcases family_descends (prefixWord ++ tailWord_444906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444915 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 5]
def baseStart_444915 : Nat := 118140960795 + 444915 * 2 ^ 59
def prefixEnd_444915 : Nat := 4983230072969 + 3 ^ 40 * 444915 * 2
def baseEnd_444915 : Nat := 228455245395232001716379

theorem tailTrace_444915 : CollatzResearch.WordTrace tailWord_444915 prefixEnd_444915 228455245395232001716379 := by
  unfold tailWord_444915
  simp only [CollatzResearch.WordTrace]
  refine ⟨16227383183156415277600199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10818255455437610185066799 16227383183156415277600199)
  ·
    refine ⟨24341074774734622916400299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16227383183156415277600199 24341074774734622916400299)
    ·
      refine ⟨36511612162101934374600449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24341074774734622916400299 36511612162101934374600449)
      ·
        refine ⟨27383709121576450780950337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36511612162101934374600449 27383709121576450780950337)
        ·
          refine ⟨20537781841182338085712753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27383709121576450780950337 20537781841182338085712753)
          ·
            refine ⟨15403336380886753564284565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20537781841182338085712753 15403336380886753564284565)
            ·
              refine ⟨722031392854066573325839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15403336380886753564284565 722031392854066573325839)
              ·
                refine ⟨1083047089281099859988759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722031392854066573325839 1083047089281099859988759)
                ·
                  refine ⟨1624570633921649789983139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083047089281099859988759 1624570633921649789983139)
                  ·
                    refine ⟨2436855950882474684974709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1624570633921649789983139 2436855950882474684974709)
                    ·
                      refine ⟨228455245395232001716379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2436855950882474684974709 228455245395232001716379)
                      ·
                        rfl

theorem cell23_444915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 5].length) (baseStart_444915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444915 prefixEnd_444915 := by exact prefixLift 444915
  have htrace : WordTrace (prefixWord ++ tailWord_444915) baseStart_444915 baseEnd_444915 := by
    simpa [prefixWord, tailWord_444915, baseEnd_444915] using wordTrace_append hprefix tailTrace_444915
  have hstable : (prefixWord ++ tailWord_444915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444915).length < 2 ^ (prefixWord ++ tailWord_444915).sum := by decide
  have hdescent : baseEnd_444915 < baseStart_444915 := by decide
  rcases family_descends (prefixWord ++ tailWord_444915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444932 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_444932 : Nat := 118140960795 + 444932 * 2 ^ 59
def prefixEnd_444932 : Nat := 4983230072969 + 3 ^ 40 * 444932 * 2
def baseEnd_444932 : Nat := 228463974566358435203801

theorem tailTrace_444932 : CollatzResearch.WordTrace tailWord_444932 prefixEnd_444932 228463974566358435203801 := by
  unfold tailWord_444932
  simp only [CollatzResearch.WordTrace]
  refine ⟨8114001612047413590484525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10818668816063218120646033 8114001612047413590484525)
  ·
    refine ⟨3042750604517780096431697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8114001612047413590484525 3042750604517780096431697)
    ·
      refine ⟨2282062953388335072323773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3042750604517780096431697 2282062953388335072323773)
      ·
        refine ⟨855773607520625652121415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2282062953388335072323773 855773607520625652121415)
        ·
          refine ⟨1283660411280938478182123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855773607520625652121415 1283660411280938478182123)
          ·
            refine ⟨1925490616921407717273185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283660411280938478182123 1925490616921407717273185)
            ·
              refine ⟨1444117962691055787954889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1925490616921407717273185 1444117962691055787954889)
              ·
                refine ⟨1083088472018291840966167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1444117962691055787954889 1083088472018291840966167)
                ·
                  refine ⟨1624632708027437761449251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083088472018291840966167 1624632708027437761449251)
                  ·
                    refine ⟨2436949062041156642173877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1624632708027437761449251 2436949062041156642173877)
                    ·
                      refine ⟨228463974566358435203801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2436949062041156642173877 228463974566358435203801)
                      ·
                        rfl

theorem cell23_444932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_444932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444932 prefixEnd_444932 := by exact prefixLift 444932
  have htrace : WordTrace (prefixWord ++ tailWord_444932) baseStart_444932 baseEnd_444932 := by
    simpa [prefixWord, tailWord_444932, baseEnd_444932] using wordTrace_append hprefix tailTrace_444932
  have hstable : (prefixWord ++ tailWord_444932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444932).length < 2 ^ (prefixWord ++ tailWord_444932).sum := by decide
  have hdescent : baseEnd_444932 < baseStart_444932 := by decide
  rcases family_descends (prefixWord ++ tailWord_444932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444939 : List Nat := [1, 1, 1, 1, 7, 1, 4, 1, 2, 4]
def baseStart_444939 : Nat := 118140960795 + 444939 * 2 ^ 59
def prefixEnd_444939 : Nat := 4983230072969 + 3 ^ 40 * 444939 * 2
def baseEnd_444939 : Nat := 76155856310313302605423

theorem tailTrace_444939 : CollatzResearch.WordTrace tailWord_444939 prefixEnd_444939 76155856310313302605423 := by
  unfold tailWord_444939
  simp only [CollatzResearch.WordTrace]
  refine ⟨16228258535069467376473871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10818839023379644917649247 16228258535069467376473871)
  ·
    refine ⟨24342387802604201064710807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16228258535069467376473871 24342387802604201064710807)
    ·
      refine ⟨36513581703906301597066211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24342387802604201064710807 36513581703906301597066211)
      ·
        refine ⟨54770372555859452395599317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36513581703906301597066211 54770372555859452395599317)
        ·
          refine ⟨1283680606777955915521859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 54770372555859452395599317 1283680606777955915521859)
          ·
            refine ⟨1925520910166933873282789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283680606777955915521859 1925520910166933873282789)
            ·
              refine ⟨361035170656300101240523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1925520910166933873282789 361035170656300101240523)
              ·
                refine ⟨541552755984450151860785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361035170656300101240523 541552755984450151860785)
                ·
                  refine ⟨406164566988337613895589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541552755984450151860785 406164566988337613895589)
                  ·
                    refine ⟨76155856310313302605423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 406164566988337613895589 76155856310313302605423)
                    ·
                      rfl

theorem cell23_444939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 2, 4].length) (baseStart_444939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444939 prefixEnd_444939 := by exact prefixLift 444939
  have htrace : WordTrace (prefixWord ++ tailWord_444939) baseStart_444939 baseEnd_444939 := by
    simpa [prefixWord, tailWord_444939, baseEnd_444939] using wordTrace_append hprefix tailTrace_444939
  have hstable : (prefixWord ++ tailWord_444939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444939).length < 2 ^ (prefixWord ++ tailWord_444939).sum := by decide
  have hdescent : baseEnd_444939 < baseStart_444939 := by decide
  rcases family_descends (prefixWord ++ tailWord_444939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444979 : List Nat := [1, 1, 1, 2, 4, 2, 4, 2, 2, 1, 3]
def baseStart_444979 : Nat := 118140960795 + 444979 * 2 ^ 59
def prefixEnd_444979 : Nat := 4983230072969 + 3 ^ 40 * 444979 * 2
def baseEnd_444979 : Nat := 228488108157119751316085

theorem tailTrace_444979 : CollatzResearch.WordTrace tailWord_444979 prefixEnd_444979 228488108157119751316085 := by
  unfold tailWord_444979
  simp only [CollatzResearch.WordTrace]
  refine ⟨16229717454924554207929991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10819811636616369471953327 16229717454924554207929991)
  ·
    refine ⟨24344576182386831311894987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16229717454924554207929991 24344576182386831311894987)
    ·
      refine ⟨36516864273580246967842481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24344576182386831311894987 36516864273580246967842481)
      ·
        refine ⟨27387648205185185225881861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36516864273580246967842481 27387648205185185225881861)
        ·
          refine ⟨5135184038472222229852849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27387648205185185225881861 5135184038472222229852849)
          ·
            refine ⟨3851388028854166672389637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5135184038472222229852849 3851388028854166672389637)
            ·
              refine ⟨722135255410156251073057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3851388028854166672389637 722135255410156251073057)
              ·
                refine ⟨541601441557617188304793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 722135255410156251073057 541601441557617188304793)
                ·
                  refine ⟨406201081168212891228595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541601441557617188304793 406201081168212891228595)
                  ·
                    refine ⟨609301621752319336842893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 406201081168212891228595 609301621752319336842893)
                    ·
                      refine ⟨228488108157119751316085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 609301621752319336842893 228488108157119751316085)
                      ·
                        rfl

theorem cell23_444979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 1, 3].length) (baseStart_444979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444979 prefixEnd_444979 := by exact prefixLift 444979
  have htrace : WordTrace (prefixWord ++ tailWord_444979) baseStart_444979 baseEnd_444979 := by
    simpa [prefixWord, tailWord_444979, baseEnd_444979] using wordTrace_append hprefix tailTrace_444979
  have hstable : (prefixWord ++ tailWord_444979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444979).length < 2 ^ (prefixWord ++ tailWord_444979).sum := by decide
  have hdescent : baseEnd_444979 < baseStart_444979 := by decide
  rcases family_descends (prefixWord ++ tailWord_444979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444982 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_444982 : Nat := 118140960795 + 444982 * 2 ^ 59
def prefixEnd_444982 : Nat := 4983230072969 + 3 ^ 40 * 444982 * 2
def baseEnd_444982 : Nat := 76163216199694413192857

theorem tailTrace_444982 : CollatzResearch.WordTrace tailWord_444982 prefixEnd_444982 76163216199694413192857 := by
  unfold tailWord_444982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1014364179619605357518075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10819884582609123813526133 1014364179619605357518075)
  ·
    refine ⟨1521546269429408036277113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1014364179619605357518075 1521546269429408036277113)
    ·
      refine ⟨1141159702072056027207835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1521546269429408036277113 1141159702072056027207835)
      ·
        refine ⟨1711739553108084040811753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1141159702072056027207835 1711739553108084040811753)
        ·
          refine ⟨1283804664831063030608815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1711739553108084040811753 1283804664831063030608815)
          ·
            refine ⟨1925706997246594545913223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283804664831063030608815 1925706997246594545913223)
            ·
              refine ⟨2888560495869891818869835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925706997246594545913223 2888560495869891818869835)
              ·
                refine ⟨4332840743804837728304753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888560495869891818869835 4332840743804837728304753)
                ·
                  refine ⟨3249630557853628296228565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4332840743804837728304753 3249630557853628296228565)
                  ·
                    refine ⟨76163216199694413192857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3249630557853628296228565 76163216199694413192857)
                    ·
                      rfl

theorem cell23_444982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_444982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444982 prefixEnd_444982 := by exact prefixLift 444982
  have htrace : WordTrace (prefixWord ++ tailWord_444982) baseStart_444982 baseEnd_444982 := by
    simpa [prefixWord, tailWord_444982, baseEnd_444982] using wordTrace_append hprefix tailTrace_444982
  have hstable : (prefixWord ++ tailWord_444982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444982).length < 2 ^ (prefixWord ++ tailWord_444982).sum := by decide
  have hdescent : baseEnd_444982 < baseStart_444982 := by decide
  rcases family_descends (prefixWord ++ tailWord_444982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444985 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 1, 5, 4]
def baseStart_444985 : Nat := 118140960795 + 444985 * 2 ^ 59
def prefixEnd_444985 : Nat := 4983230072969 + 3 ^ 40 * 444985 * 2
def baseEnd_444985 : Nat := 228491189041046727841057

theorem tailTrace_444985 : CollatzResearch.WordTrace tailWord_444985 prefixEnd_444985 228491189041046727841057 := by
  unfold tailWord_444985
  simp only [CollatzResearch.WordTrace]
  refine ⟨16229936292902817232648409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10819957528601878155098939 16229936292902817232648409)
  ·
    refine ⟨12172452219677112924486307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16229936292902817232648409 12172452219677112924486307)
    ·
      refine ⟨18258678329515669386729461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12172452219677112924486307 18258678329515669386729461)
      ·
        refine ⟨1711751093392094005005887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18258678329515669386729461 1711751093392094005005887)
        ·
          refine ⟨2567626640088141007508831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1711751093392094005005887 2567626640088141007508831)
          ·
            refine ⟨3851439960132211511263247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567626640088141007508831 3851439960132211511263247)
            ·
              refine ⟨5777159940198317266894871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851439960132211511263247 5777159940198317266894871)
              ·
                refine ⟨8665739910297475900342307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5777159940198317266894871 8665739910297475900342307)
                ·
                  refine ⟨12998609865446213850513461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8665739910297475900342307 12998609865446213850513461)
                  ·
                    refine ⟨1218619674885582548485637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12998609865446213850513461 1218619674885582548485637)
                    ·
                      refine ⟨228491189041046727841057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1218619674885582548485637 228491189041046727841057)
                      ·
                        rfl

theorem cell23_444985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_444985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444985 prefixEnd_444985 := by exact prefixLift 444985
  have htrace : WordTrace (prefixWord ++ tailWord_444985) baseStart_444985 baseEnd_444985 := by
    simpa [prefixWord, tailWord_444985, baseEnd_444985] using wordTrace_append hprefix tailTrace_444985
  have hstable : (prefixWord ++ tailWord_444985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444985).length < 2 ^ (prefixWord ++ tailWord_444985).sum := by decide
  have hdescent : baseEnd_444985 < baseStart_444985 := by decide
  rcases family_descends (prefixWord ++ tailWord_444985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444989 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 3, 3, 2]
def baseStart_444989 : Nat := 118140960795 + 444989 * 2 ^ 59
def prefixEnd_444989 : Nat := 4983230072969 + 3 ^ 40 * 444989 * 2
def baseEnd_444989 : Nat := 228493242963664712191039

theorem tailTrace_444989 : CollatzResearch.WordTrace tailWord_444989 prefixEnd_444989 228493242963664712191039 := by
  unfold tailWord_444989
  simp only [CollatzResearch.WordTrace]
  refine ⟨16230082184888325915794021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10820054789925550610529347 16230082184888325915794021)
  ·
    refine ⟨3043140409666561109211379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16230082184888325915794021 3043140409666561109211379)
    ·
      refine ⟨4564710614499841663817069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3043140409666561109211379 4564710614499841663817069)
      ·
        refine ⟨1711766480437440623931401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4564710614499841663817069 1711766480437440623931401)
        ·
          refine ⟨1283824860328080467948551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1711766480437440623931401 1283824860328080467948551)
          ·
            refine ⟨1925737290492120701922827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283824860328080467948551 1925737290492120701922827)
            ·
              refine ⟨2888605935738181052884241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925737290492120701922827 2888605935738181052884241)
              ·
                refine ⟨2166454451803635789663181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2888605935738181052884241 2166454451803635789663181)
                ·
                  refine ⟨812420419426363421123693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2166454451803635789663181 812420419426363421123693)
                  ·
                    refine ⟨304657657284886282921385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 812420419426363421123693 304657657284886282921385)
                    ·
                      refine ⟨228493242963664712191039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 304657657284886282921385 228493242963664712191039)
                      ·
                        rfl

theorem cell23_444989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_444989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_444989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_444989 prefixEnd_444989 := by exact prefixLift 444989
  have htrace : WordTrace (prefixWord ++ tailWord_444989) baseStart_444989 baseEnd_444989 := by
    simpa [prefixWord, tailWord_444989, baseEnd_444989] using wordTrace_append hprefix tailTrace_444989
  have hstable : (prefixWord ++ tailWord_444989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444989).length < 2 ^ (prefixWord ++ tailWord_444989).sum := by decide
  have hdescent : baseEnd_444989 < baseStart_444989 := by decide
  rcases family_descends (prefixWord ++ tailWord_444989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445015 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_445015 : Nat := 118140960795 + 445015 * 2 ^ 59
def prefixEnd_445015 : Nat := 4983230072969 + 3 ^ 40 * 445015 * 2
def baseEnd_445015 : Nat := 228506593460681610465919

theorem tailTrace_445015 : CollatzResearch.WordTrace tailWord_445015 prefixEnd_445015 228506593460681610465919 := by
  unfold tailWord_445015
  simp only [CollatzResearch.WordTrace]
  refine ⟨16231030482794132356240499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10820686988529421570826999 16231030482794132356240499)
  ·
    refine ⟨24346545724191198534360749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16231030482794132356240499 24346545724191198534360749)
    ·
      refine ⟨9129954646571699450385281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24346545724191198534360749 9129954646571699450385281)
      ·
        refine ⟨6847465984928774587788961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9129954646571699450385281 6847465984928774587788961)
        ·
          refine ⟨5135599488696580940841721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6847465984928774587788961 5135599488696580940841721)
          ·
            refine ⟨3851699616522435705631291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5135599488696580940841721 3851699616522435705631291)
            ·
              refine ⟨5777549424783653558446937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851699616522435705631291 5777549424783653558446937)
              ·
                refine ⟨4333162068587740168835203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5777549424783653558446937 4333162068587740168835203)
                ·
                  refine ⟨6499743102881610253252805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4333162068587740168835203 6499743102881610253252805)
                  ·
                    refine ⟨1218701831790301922484901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6499743102881610253252805 1218701831790301922484901)
                    ·
                      refine ⟨228506593460681610465919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1218701831790301922484901 228506593460681610465919)
                      ·
                        rfl

theorem cell23_445015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_445015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445015 prefixEnd_445015 := by exact prefixLift 445015
  have htrace : WordTrace (prefixWord ++ tailWord_445015) baseStart_445015 baseEnd_445015 := by
    simpa [prefixWord, tailWord_445015, baseEnd_445015] using wordTrace_append hprefix tailTrace_445015
  have hstable : (prefixWord ++ tailWord_445015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445015).length < 2 ^ (prefixWord ++ tailWord_445015).sum := by decide
  have hdescent : baseEnd_445015 < baseStart_445015 := by decide
  rcases family_descends (prefixWord ++ tailWord_445015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445036 : List Nat := [2, 2, 1, 1, 3, 1, 5, 2, 2, 2, 2]
def baseStart_445036 : Nat := 118140960795 + 445036 * 2 ^ 59
def prefixEnd_445036 : Nat := 4983230072969 + 3 ^ 40 * 445036 * 2
def baseEnd_445036 : Nat := 228517376554426028303323

theorem tailTrace_445036 : CollatzResearch.WordTrace tailWord_445036 prefixEnd_445036 228517376554426028303323 := by
  unfold tailWord_445036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8115898207859026471377481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10821197610478701961836641 8115898207859026471377481)
  ·
    refine ⟨6086923655894269853533111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8115898207859026471377481 6086923655894269853533111)
    ·
      refine ⟨9130385483841404780299667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6086923655894269853533111 9130385483841404780299667)
      ·
        refine ⟨13695578225762107170449501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9130385483841404780299667 13695578225762107170449501)
        ·
          refine ⟨5135841834660790188918563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13695578225762107170449501 5135841834660790188918563)
          ·
            refine ⟨7703762751991185283377845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5135841834660790188918563 7703762751991185283377845)
            ·
              refine ⟨722227757999173620316673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7703762751991185283377845 722227757999173620316673)
              ·
                refine ⟨541670818499380215237505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 722227757999173620316673 541670818499380215237505)
                ·
                  refine ⟨406253113874535161428129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541670818499380215237505 406253113874535161428129)
                  ·
                    refine ⟨304689835405901371071097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 406253113874535161428129 304689835405901371071097)
                    ·
                      refine ⟨228517376554426028303323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 304689835405901371071097 228517376554426028303323)
                      ·
                        rfl

theorem cell23_445036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 2, 2].length) (baseStart_445036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445036 prefixEnd_445036 := by exact prefixLift 445036
  have htrace : WordTrace (prefixWord ++ tailWord_445036) baseStart_445036 baseEnd_445036 := by
    simpa [prefixWord, tailWord_445036, baseEnd_445036] using wordTrace_append hprefix tailTrace_445036
  have hstable : (prefixWord ++ tailWord_445036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445036).length < 2 ^ (prefixWord ++ tailWord_445036).sum := by decide
  have hdescent : baseEnd_445036 < baseStart_445036 := by decide
  rcases family_descends (prefixWord ++ tailWord_445036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445052 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_445052 : Nat := 118140960795 + 445052 * 2 ^ 59
def prefixEnd_445052 : Nat := 4983230072969 + 3 ^ 40 * 445052 * 2
def baseEnd_445052 : Nat := 228525592244897965703249

theorem tailTrace_445052 : CollatzResearch.WordTrace tailWord_445052 prefixEnd_445052 228525592244897965703249 := by
  unfold tailWord_445052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8116189991830043837668705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10821586655773391783558273 8116189991830043837668705)
  ·
    refine ⟨6087142493872532878251529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8116189991830043837668705 6087142493872532878251529)
    ·
      refine ⟨4565356870404399658688647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6087142493872532878251529 4565356870404399658688647)
      ·
        refine ⟨6848035305606599488032971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4565356870404399658688647 6848035305606599488032971)
        ·
          refine ⟨10272052958409899232049457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6848035305606599488032971 10272052958409899232049457)
          ·
            refine ⟨7704039718807424424037093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10272052958409899232049457 7704039718807424424037093)
            ·
              refine ⟨1444507447276392079506955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7704039718807424424037093 1444507447276392079506955)
              ·
                refine ⟨2166761170914588119260433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444507447276392079506955 2166761170914588119260433)
                ·
                  refine ⟨1625070878185941089445325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2166761170914588119260433 1625070878185941089445325)
                  ·
                    refine ⟨609401579319727908541997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1625070878185941089445325 609401579319727908541997)
                    ·
                      refine ⟨228525592244897965703249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 609401579319727908541997 228525592244897965703249)
                      ·
                        rfl

theorem cell23_445052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_445052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445052 prefixEnd_445052 := by exact prefixLift 445052
  have htrace : WordTrace (prefixWord ++ tailWord_445052) baseStart_445052 baseEnd_445052 := by
    simpa [prefixWord, tailWord_445052, baseEnd_445052] using wordTrace_append hprefix tailTrace_445052
  have hstable : (prefixWord ++ tailWord_445052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445052).length < 2 ^ (prefixWord ++ tailWord_445052).sum := by decide
  have hdescent : baseEnd_445052 < baseStart_445052 := by decide
  rcases family_descends (prefixWord ++ tailWord_445052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445053 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 1, 4, 2]
def baseStart_445053 : Nat := 118140960795 + 445053 * 2 ^ 59
def prefixEnd_445053 : Nat := 4983230072969 + 3 ^ 40 * 445053 * 2
def baseEnd_445053 : Nat := 228526105725552461790745

theorem tailTrace_445053 : CollatzResearch.WordTrace tailWord_445053 prefixEnd_445053 228526105725552461790745 := by
  unfold tailWord_445053
  simp only [CollatzResearch.WordTrace]
  refine ⟨16232416456656464846123813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10821610971104309897415875 16232416456656464846123813)
  ·
    refine ⟨3043578085623087158648215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16232416456656464846123813 3043578085623087158648215)
    ·
      refine ⟨4565367128434630737972323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3043578085623087158648215 4565367128434630737972323)
      ·
        refine ⟨6848050692651946106958485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4565367128434630737972323 6848050692651946106958485)
        ·
          refine ⟨321002376218059973763679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6848050692651946106958485 321002376218059973763679)
          ·
            refine ⟨481503564327089960645519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321002376218059973763679 481503564327089960645519)
            ·
              refine ⟨722255346490634940968279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481503564327089960645519 722255346490634940968279)
              ·
                refine ⟨1083383019735952411452419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722255346490634940968279 1083383019735952411452419)
                ·
                  refine ⟨1625074529603928617178629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083383019735952411452419 1625074529603928617178629)
                  ·
                    refine ⟨304701474300736615720993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1625074529603928617178629 304701474300736615720993)
                    ·
                      refine ⟨228526105725552461790745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 304701474300736615720993 228526105725552461790745)
                      ·
                        rfl

theorem cell23_445053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_445053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445053 prefixEnd_445053 := by exact prefixLift 445053
  have htrace : WordTrace (prefixWord ++ tailWord_445053) baseStart_445053 baseEnd_445053 := by
    simpa [prefixWord, tailWord_445053, baseEnd_445053] using wordTrace_append hprefix tailTrace_445053
  have hstable : (prefixWord ++ tailWord_445053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445053).length < 2 ^ (prefixWord ++ tailWord_445053).sum := by decide
  have hdescent : baseEnd_445053 < baseStart_445053 := by decide
  rcases family_descends (prefixWord ++ tailWord_445053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445055 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 6, 5]
def baseStart_445055 : Nat := 118140960795 + 445055 * 2 ^ 59
def prefixEnd_445055 : Nat := 4983230072969 + 3 ^ 40 * 445055 * 2
def baseEnd_445055 : Nat := 76175710895620484655245

theorem tailTrace_445055 : CollatzResearch.WordTrace tailWord_445055 prefixEnd_445055 76175710895620484655245 := by
  unfold tailWord_445055
  simp only [CollatzResearch.WordTrace]
  refine ⟨16232489402649219187696619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10821659601766146125131079 16232489402649219187696619)
  ·
    refine ⟨24348734103973828781544929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16232489402649219187696619 24348734103973828781544929)
    ·
      refine ⟨18261550577980371586158697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24348734103973828781544929 18261550577980371586158697)
      ·
        refine ⟨13696162933485278689619023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18261550577980371586158697 13696162933485278689619023)
        ·
          refine ⟨20544244400227918034428535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13696162933485278689619023 20544244400227918034428535)
          ·
            refine ⟨30816366600341877051642803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20544244400227918034428535 30816366600341877051642803)
            ·
              refine ⟨46224549900512815577464205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30816366600341877051642803 46224549900512815577464205)
              ·
                refine ⟨17334206212692305841549077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46224549900512815577464205 17334206212692305841549077)
                ·
                  refine ⟨812540916219951836322613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17334206212692305841549077 812540916219951836322613)
                  ·
                    refine ⟨76175710895620484655245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 812540916219951836322613 76175710895620484655245)
                    ·
                      rfl

theorem cell23_445055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 5].length) (baseStart_445055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445055 prefixEnd_445055 := by exact prefixLift 445055
  have htrace : WordTrace (prefixWord ++ tailWord_445055) baseStart_445055 baseEnd_445055 := by
    simpa [prefixWord, tailWord_445055, baseEnd_445055] using wordTrace_append hprefix tailTrace_445055
  have hstable : (prefixWord ++ tailWord_445055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445055).length < 2 ^ (prefixWord ++ tailWord_445055).sum := by decide
  have hdescent : baseEnd_445055 < baseStart_445055 := by decide
  rcases family_descends (prefixWord ++ tailWord_445055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445065 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 3, 2, 5]
def baseStart_445065 : Nat := 118140960795 + 445065 * 2 ^ 59
def prefixEnd_445065 : Nat := 4983230072969 + 3 ^ 40 * 445065 * 2
def baseEnd_445065 : Nat := 228532267493406414840689

theorem tailTrace_445065 : CollatzResearch.WordTrace tailWord_445065 prefixEnd_445065 228532267493406414840689 := by
  unfold tailWord_445065
  simp only [CollatzResearch.WordTrace]
  refine ⟨16232854132612990895560649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10821902755075327263707099 16232854132612990895560649)
  ·
    refine ⟨12174640599459743171670487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16232854132612990895560649 12174640599459743171670487)
    ·
      refine ⟨18261960899189614757505731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12174640599459743171670487 18261960899189614757505731)
      ·
        refine ⟨27392941348784422136258597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18261960899189614757505731 27392941348784422136258597)
        ·
          refine ⟨5136176502897079150548487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27392941348784422136258597 5136176502897079150548487)
          ·
            refine ⟨7704264754345618725822731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5136176502897079150548487 7704264754345618725822731)
            ·
              refine ⟨11556397131518428088734097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7704264754345618725822731 11556397131518428088734097)
              ·
                refine ⟨8667297848638821066550573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11556397131518428088734097 8667297848638821066550573)
                ·
                  refine ⟨3250236693239557899956465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8667297848638821066550573 3250236693239557899956465)
                  ·
                    refine ⟨2437677519929668424967349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3250236693239557899956465 2437677519929668424967349)
                    ·
                      refine ⟨228532267493406414840689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2437677519929668424967349 228532267493406414840689)
                      ·
                        rfl

theorem cell23_445065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_445065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445065 prefixEnd_445065 := by exact prefixLift 445065
  have htrace : WordTrace (prefixWord ++ tailWord_445065) baseStart_445065 baseEnd_445065 := by
    simpa [prefixWord, tailWord_445065, baseEnd_445065] using wordTrace_append hprefix tailTrace_445065
  have hstable : (prefixWord ++ tailWord_445065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445065).length < 2 ^ (prefixWord ++ tailWord_445065).sum := by decide
  have hdescent : baseEnd_445065 < baseStart_445065 := by decide
  rcases family_descends (prefixWord ++ tailWord_445065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445076 : List Nat := [2, 4, 2, 2, 1, 1, 3, 3, 5]
def baseStart_445076 : Nat := 118140960795 + 445076 * 2 ^ 59
def prefixEnd_445076 : Nat := 4983230072969 + 3 ^ 40 * 445076 * 2
def baseEnd_445076 : Nat := 25393101753400652422571

theorem tailTrace_445076 : CollatzResearch.WordTrace tailWord_445076 prefixEnd_445076 25393101753400652422571 := by
  unfold tailWord_445076
  simp only [CollatzResearch.WordTrace]
  refine ⟨8116627667786569887105541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10822170223715426516140721 8116627667786569887105541)
  ·
    refine ⟨1521867687709981853832289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8116627667786569887105541 1521867687709981853832289)
    ·
      refine ⟨1141400765782486390374217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1521867687709981853832289 1141400765782486390374217)
      ·
        refine ⟨856050574336864792780663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1141400765782486390374217 856050574336864792780663)
        ·
          refine ⟨1284075861505297189170995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856050574336864792780663 1284075861505297189170995)
          ·
            refine ⟨1926113792257945783756493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284075861505297189170995 1926113792257945783756493)
            ·
              refine ⟨722292672096729668908685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1926113792257945783756493 722292672096729668908685)
              ·
                refine ⟨270859752036273625840757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 722292672096729668908685 270859752036273625840757)
                ·
                  refine ⟨25393101753400652422571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270859752036273625840757 25393101753400652422571)
                  ·
                    rfl

theorem cell23_445076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_445076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445076 prefixEnd_445076 := by exact prefixLift 445076
  have htrace : WordTrace (prefixWord ++ tailWord_445076) baseStart_445076 baseEnd_445076 := by
    simpa [prefixWord, tailWord_445076, baseEnd_445076] using wordTrace_append hprefix tailTrace_445076
  have hstable : (prefixWord ++ tailWord_445076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445076).length < 2 ^ (prefixWord ++ tailWord_445076).sum := by decide
  have hdescent : baseEnd_445076 < baseStart_445076 := by decide
  rcases family_descends (prefixWord ++ tailWord_445076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445089 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 2, 5]
def baseStart_445089 : Nat := 118140960795 + 445089 * 2 ^ 59
def prefixEnd_445089 : Nat := 4983230072969 + 3 ^ 40 * 445089 * 2
def baseEnd_445089 : Nat := 76181530343038106980193

theorem tailTrace_445089 : CollatzResearch.WordTrace tailWord_445089 prefixEnd_445089 76181530343038106980193 := by
  unfold tailWord_445089
  simp only [CollatzResearch.WordTrace]
  refine ⟨16233729484526042994434321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10822486323017361996289547 16233729484526042994434321)
  ·
    refine ⟨12175297113394532245825741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16233729484526042994434321 12175297113394532245825741)
    ·
      refine ⟨4565736417522949592184653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12175297113394532245825741 4565736417522949592184653)
      ·
        refine ⟨1712151156571106097069245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4565736417522949592184653 1712151156571106097069245)
        ·
          refine ⟨642056683714164786400967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1712151156571106097069245 642056683714164786400967)
          ·
            refine ⟨963085025571247179601451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642056683714164786400967 963085025571247179601451)
            ·
              refine ⟨1444627538356870769402177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963085025571247179601451 1444627538356870769402177)
              ·
                refine ⟨1083470653767653077051633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1444627538356870769402177 1083470653767653077051633)
                ·
                  refine ⟨812602990325739807788725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1083470653767653077051633 812602990325739807788725)
                  ·
                    refine ⟨76181530343038106980193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 812602990325739807788725 76181530343038106980193)
                    ·
                      rfl

theorem cell23_445089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_445089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445089 prefixEnd_445089 := by exact prefixLift 445089
  have htrace : WordTrace (prefixWord ++ tailWord_445089) baseStart_445089 baseEnd_445089 := by
    simpa [prefixWord, tailWord_445089, baseEnd_445089] using wordTrace_append hprefix tailTrace_445089
  have hstable : (prefixWord ++ tailWord_445089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445089).length < 2 ^ (prefixWord ++ tailWord_445089).sum := by decide
  have hdescent : baseEnd_445089 < baseStart_445089 := by decide
  rcases family_descends (prefixWord ++ tailWord_445089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445125 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_445125 : Nat := 118140960795 + 445125 * 2 ^ 59
def prefixEnd_445125 : Nat := 4983230072969 + 3 ^ 40 * 445125 * 2
def baseEnd_445125 : Nat := 228563076332676180090413

theorem tailTrace_445125 : CollatzResearch.WordTrace tailWord_445125 prefixEnd_445125 228563076332676180090413 := by
  unfold tailWord_445125
  simp only [CollatzResearch.WordTrace]
  refine ⟨16235042512395621142744829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10823361674930414095163219 16235042512395621142744829)
  ·
    refine ⟨6088140942148357928529311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16235042512395621142744829 6088140942148357928529311)
    ·
      refine ⟨9132211413222536892793967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6088140942148357928529311 9132211413222536892793967)
      ·
        refine ⟨13698317119833805339190951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9132211413222536892793967 13698317119833805339190951)
        ·
          refine ⟨20547475679750708008786427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13698317119833805339190951 20547475679750708008786427)
          ·
            refine ⟨30821213519626062013179641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20547475679750708008786427 30821213519626062013179641)
            ·
              refine ⟨23115910139719546509884731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30821213519626062013179641 23115910139719546509884731)
              ·
                refine ⟨34673865209579319764827097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23115910139719546509884731 34673865209579319764827097)
                ·
                  refine ⟨26005398907184489823620323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34673865209579319764827097 26005398907184489823620323)
                  ·
                    refine ⟨39008098360776734735430485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26005398907184489823620323 39008098360776734735430485)
                    ·
                      refine ⟨228563076332676180090413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 39008098360776734735430485 228563076332676180090413)
                      ·
                        rfl

theorem cell23_445125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_445125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445125 prefixEnd_445125 := by exact prefixLift 445125
  have htrace : WordTrace (prefixWord ++ tailWord_445125) baseStart_445125 baseEnd_445125 := by
    simpa [prefixWord, tailWord_445125, baseEnd_445125] using wordTrace_append hprefix tailTrace_445125
  have hstable : (prefixWord ++ tailWord_445125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445125).length < 2 ^ (prefixWord ++ tailWord_445125).sum := by decide
  have hdescent : baseEnd_445125 < baseStart_445125 := by decide
  rcases family_descends (prefixWord ++ tailWord_445125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445135 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 8]
def baseStart_445135 : Nat := 118140960795 + 445135 * 2 ^ 59
def prefixEnd_445135 : Nat := 4983230072969 + 3 ^ 40 * 445135 * 2
def baseEnd_445135 : Nat := 228568211139221140965367

theorem tailTrace_445135 : CollatzResearch.WordTrace tailWord_445135 prefixEnd_445135 228568211139221140965367 := by
  unfold tailWord_445135
  simp only [CollatzResearch.WordTrace]
  refine ⟨16235407242359392850608859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10823604828239595233739239 16235407242359392850608859)
  ·
    refine ⟨24353110863539089275913289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16235407242359392850608859 24353110863539089275913289)
    ·
      refine ⟨18264833147654316956934967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24353110863539089275913289 18264833147654316956934967)
      ·
        refine ⟨27397249721481475435402451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18264833147654316956934967 27397249721481475435402451)
        ·
          refine ⟨41095874582222213153103677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27397249721481475435402451 41095874582222213153103677)
          ·
            refine ⟨15410952968333329932413879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41095874582222213153103677 15410952968333329932413879)
            ·
              refine ⟨23116429452499994898620819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15410952968333329932413879 23116429452499994898620819)
              ·
                refine ⟨34674644178749992347931229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23116429452499994898620819 34674644178749992347931229)
                ·
                  refine ⟨13002991567031247130474211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34674644178749992347931229 13002991567031247130474211)
                  ·
                    refine ⟨19504487350546870695711317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13002991567031247130474211 19504487350546870695711317)
                    ·
                      refine ⟨228568211139221140965367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 19504487350546870695711317 228568211139221140965367)
                      ·
                        rfl

theorem cell23_445135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_445135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445135 prefixEnd_445135 := by exact prefixLift 445135
  have htrace : WordTrace (prefixWord ++ tailWord_445135) baseStart_445135 baseEnd_445135 := by
    simpa [prefixWord, tailWord_445135, baseEnd_445135] using wordTrace_append hprefix tailTrace_445135
  have hstable : (prefixWord ++ tailWord_445135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445135).length < 2 ^ (prefixWord ++ tailWord_445135).sum := by decide
  have hdescent : baseEnd_445135 < baseStart_445135 := by decide
  rcases family_descends (prefixWord ++ tailWord_445135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
